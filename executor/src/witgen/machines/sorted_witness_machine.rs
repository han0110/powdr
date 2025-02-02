use std::collections::{BTreeMap, HashMap, HashSet};

use itertools::{Either, Itertools};

use super::super::affine_expression::AffineExpression;
use super::fixed_lookup_machine::FixedLookup;
use super::Machine;
use super::{EvalResult, FixedData};
use crate::witgen::affine_expression::AffineResult;
use crate::witgen::EvalValue;
use crate::witgen::{
    expression_evaluator::ExpressionEvaluator, fixed_evaluator::FixedEvaluator,
    symbolic_evaluator::SymbolicEvaluator,
};
use number::FieldElement;
use pil_analyzer::{
    self, Expression, Identity, IdentityKind, PolynomialReference, SelectedExpressions,
};

/// A machine that can support a lookup in a set of columns that are sorted
/// by one specific column and values in that column have to be unique.
/// This means there is a column A and a constraint of the form
/// NOTLAST { A' - A } in { POSITIVE }
/// Where
///  - NOTLAST is zero only on the last row
///  - POSITIVE has all values from 1 to half of the field size.
pub struct SortedWitnesses<T> {
    key_col: PolynomialReference,
    /// Position of the witness columns in the data.
    /// The key column has a position of usize::max
    witness_positions: HashMap<PolynomialReference, usize>,
    data: BTreeMap<T, Vec<Option<T>>>,
}

impl<T: FieldElement> SortedWitnesses<T> {
    pub fn try_new(
        fixed_data: &FixedData<T>,
        identities: &[&Identity<T>],
        witness_names: &HashSet<&PolynomialReference>,
    ) -> Option<Box<Self>> {
        if identities.len() != 1 {
            return None;
        }
        check_identity(fixed_data, identities.first().unwrap()).map(|key_col| {
            let witness_positions = witness_names
                .iter()
                .filter(|&w| *w != key_col)
                .sorted()
                .enumerate()
                .map(|(i, &x)| (x.clone(), i))
                .collect();

            Box::new(SortedWitnesses {
                key_col: key_col.clone(),
                witness_positions,
                data: Default::default(),
            })
        })
    }
}

fn check_identity<'a, T: FieldElement>(
    fixed_data: &FixedData<T>,
    id: &'a Identity<T>,
) -> Option<&'a PolynomialReference> {
    // Looking for NOTLAST { A' - A } in { POSITIVE }
    if id.kind != IdentityKind::Plookup
        || id.right.selector.is_some()
        || id.left.expressions.len() != 1
    {
        return None;
    }

    // Check for A' - A in the LHS
    let key_column = check_constraint(id.left.expressions.first().unwrap())?;

    let notlast = id.left.selector.as_ref()?;
    let positive = id.right.expressions.first().unwrap();

    // TODO this could be rather slow. We should check the code for identity instead
    // of evaluating it.
    let degree = fixed_data.degree as usize;
    for row in 0..(degree) {
        let ev = ExpressionEvaluator::new(FixedEvaluator::new(fixed_data, row));
        let nl = ev.evaluate(notlast).ok()?.constant_value()?;
        if (row == degree - 1 && nl != 0.into()) || (row < degree - 1 && nl != 1.into()) {
            return None;
        }
        let pos = ev.evaluate(positive).ok()?.constant_value()?;
        if pos != (row as u64 + 1).into() {
            return None;
        }
    }
    Some(key_column)
}

/// Checks that the identity has a constraint of the form `a' - a` as the first expression
/// on the left hand side and returns the name of the witness column.
fn check_constraint<T: FieldElement>(constraint: &Expression<T>) -> Option<&PolynomialReference> {
    let symbolic_ev = SymbolicEvaluator;
    let sort_constraint = match ExpressionEvaluator::new(symbolic_ev).evaluate(constraint) {
        Ok(c) => c,
        Err(_) => return None,
    };
    let key_column_id = match sort_constraint.nonzero_variables().as_slice() {
        [key, _] => *key,
        _ => return None,
    };
    if key_column_id.next || key_column_id.is_fixed() {
        return None;
    }
    let poly_next = PolynomialReference {
        next: true,
        ..key_column_id.clone()
    };
    let pattern = AffineExpression::from_variable_id(&poly_next)
        - AffineExpression::from_variable_id(key_column_id);
    if sort_constraint != pattern {
        return None;
    }

    Some(key_column_id)
}

impl<T: FieldElement> Machine<T> for SortedWitnesses<T> {
    fn process_plookup<'a>(
        &mut self,
        _fixed_data: &FixedData<T>,
        _fixed_lookup: &mut FixedLookup<T>,
        kind: IdentityKind,
        left: &[AffineResult<&'a PolynomialReference, T>],
        right: &SelectedExpressions<T>,
    ) -> Option<EvalResult<'a, T>> {
        if kind != IdentityKind::Plookup || right.selector.is_some() {
            return None;
        }
        let rhs = right
            .expressions
            .iter()
            .map(|e| match e {
                pil_analyzer::Expression::PolynomialReference(p) => {
                    assert!(!p.next);
                    if *p == self.key_col || self.witness_positions.contains_key(p) {
                        Some(p)
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;

        Some(self.process_plookup_internal(left, right, rhs))
    }
    fn witness_col_values(&mut self, fixed_data: &FixedData<T>) -> HashMap<String, Vec<T>> {
        let mut result = HashMap::new();

        let (mut keys, mut values): (Vec<_>, Vec<_>) =
            std::mem::take(&mut self.data).into_iter().unzip();

        let mut last_key = keys.last().cloned().unwrap_or_default();
        while keys.len() < fixed_data.degree as usize {
            last_key += 1u64.into();
            keys.push(last_key);
        }
        result.insert(self.key_col.name.clone(), keys);

        for (col, &i) in &self.witness_positions {
            let mut col_values = values
                .iter_mut()
                .map(|row| std::mem::take(&mut row[i]).unwrap_or_default())
                .collect::<Vec<_>>();
            col_values.resize(fixed_data.degree as usize, 0.into());
            result.insert(col.name.clone(), col_values);
        }

        result
    }
}

impl<T: FieldElement> SortedWitnesses<T> {
    fn process_plookup_internal<'a>(
        &mut self,
        left: &[AffineResult<&'a PolynomialReference, T>],
        right: &SelectedExpressions<T>,
        rhs: Vec<&PolynomialReference>,
    ) -> EvalResult<'a, T> {
        // Fail if the LHS has an error.
        let (left, errors): (Vec<_>, Vec<_>) = left.iter().partition_map(|x| match x {
            Ok(x) => Either::Left(x),
            Err(x) => Either::Right(x),
        });
        if !errors.is_empty() {
            return Ok(EvalValue::incomplete(
                errors
                    .into_iter()
                    .cloned()
                    .reduce(|x, y| x.combine(y))
                    .unwrap(),
            ));
        }

        let key_index = rhs.iter().position(|&x| x == &self.key_col).unwrap();

        let key_value = left[key_index].constant_value().ok_or_else(|| {
            format!(
                "Value of unique key must be known: {} = {}",
                left[key_index], right.expressions[key_index]
            )
        })?;

        let mut assignments = EvalValue::complete(vec![]);
        let stored_values = self
            .data
            .entry(key_value)
            .or_insert_with(|| vec![None; self.witness_positions.len()]);
        for (&l, &r) in left.iter().zip(rhs.iter()).skip(1) {
            let stored_value = &mut stored_values[self.witness_positions[r]];
            match stored_value {
                // There is a stored value
                Some(v) => {
                    match (l.clone() - (*v).into()).solve() {
                        Err(()) => {
                            // The LHS value is known and it is differetn from the stored one.
                            return Err(format!(
                                "Lookup mismatch: There is already a unique row with {} = \
                            {key_value} and {r} = {v}, but wanted to store {r} = {l}",
                                self.key_col,
                            )
                            .into());
                        }
                        Ok(ass) => {
                            if !ass.is_empty() {
                                log::trace!("Read {} = {key_value} -> {r} = {v}", self.key_col);
                            }
                            assignments.combine(ass);
                        }
                    }
                }
                // There is no value stored yet.
                None => match l.constant_value() {
                    Some(v) => {
                        log::trace!("Stored {} = {key_value} -> {r} = {v}", self.key_col);
                        *stored_value = Some(v);
                    }
                    None => {
                        return Err(format!(
                            "Value {r} for key {} = {key_value} not known",
                            self.key_col,
                        )
                        .into())
                    }
                },
            }
        }
        Ok(assignments)
    }
}
