use number::FieldElement;
use pil_analyzer::Analyzed;
use std::io;
use strum::{Display, EnumString, EnumVariantNames};

#[derive(Clone, EnumString, EnumVariantNames, Display)]
pub enum Backend {
    #[strum(serialize = "halo2")]
    Halo2,
    #[strum(serialize = "halo2-mock")]
    Halo2Mock,
}

/// Create a proof for a given PIL, fixed column values and witness column values
/// using the chosen backend.

pub type Proof = Vec<u8>;
pub type Params = Vec<u8>;

pub trait ProverWithParams {
    fn prove<T: FieldElement, R: io::Read>(
        pil: &Analyzed<T>,
        fixed: Vec<(&str, Vec<T>)>,
        witness: Vec<(&str, Vec<T>)>,
        params: R,
    ) -> Option<Proof>;

    fn generate_params<T: FieldElement>(size: usize) -> Params;
}

pub trait ProverWithoutParams {
    fn prove<T: FieldElement>(
        pil: &Analyzed<T>,
        fixed: Vec<(&str, Vec<T>)>,
        witness: Vec<(&str, Vec<T>)>,
    ) -> Option<Proof>;
}

pub struct Halo2Backend;
pub struct Halo2MockBackend;

impl ProverWithParams for Halo2Backend {
    fn prove<T: FieldElement, R: io::Read>(
        pil: &Analyzed<T>,
        fixed: Vec<(&str, Vec<T>)>,
        witness: Vec<(&str, Vec<T>)>,
        params: R,
    ) -> Option<Proof> {
        Some(halo2::prove_ast_read_params(pil, fixed, witness, params))
    }

    fn generate_params<T: FieldElement>(size: usize) -> Params {
        halo2::generate_params::<T>(size)
    }
}

impl ProverWithoutParams for Halo2MockBackend {
    fn prove<T: FieldElement>(
        pil: &Analyzed<T>,
        fixed: Vec<(&str, Vec<T>)>,
        witness: Vec<(&str, Vec<T>)>,
    ) -> Option<Proof> {
        halo2::mock_prove(pil, fixed, witness);
        None
    }
}
