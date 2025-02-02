use std::collections::HashMap;

use pil_analyzer::util::previsit_expressions_in_identity_mut;
use pil_analyzer::{Expression, Identity, PolyID, PolynomialReference};

/// Checks if an expression is
/// - a polynomial
/// - not part of a polynomial array
/// - not shifted with `'`
/// and return the polynomial if so
pub fn try_to_simple_poly<T>(expr: &Expression<T>) -> Option<&PolynomialReference> {
    if let Expression::PolynomialReference(
        p @ PolynomialReference {
            index: None,
            next: false,
            ..
        },
    ) = expr
    {
        Some(p)
    } else {
        None
    }
}

pub fn try_to_simple_poly_ref<T>(expr: &Expression<T>) -> Option<PolyID> {
    if let Expression::PolynomialReference(PolynomialReference {
        poly_id,
        index: None,
        next: false,
        ..
    }) = expr
    {
        Some(poly_id.unwrap())
    } else {
        None
    }
}

pub fn is_simple_poly_of_name<T>(expr: &Expression<T>, poly_name: &str) -> bool {
    if let Expression::PolynomialReference(PolynomialReference {
        name,
        index: None,
        next: false,
        ..
    }) = expr
    {
        name == poly_name
    } else {
        false
    }
}

pub fn substitute_constants<T: Copy>(
    identities: &[Identity<T>],
    constants: &HashMap<String, T>,
) -> Vec<Identity<T>> {
    identities
        .iter()
        .cloned()
        .map(|mut identity| {
            previsit_expressions_in_identity_mut(&mut identity, &mut |e| {
                if let Expression::Constant(name) = e {
                    *e = Expression::Number(constants[name])
                }
                std::ops::ControlFlow::Continue::<()>(())
            });
            identity
        })
        .collect()
}
