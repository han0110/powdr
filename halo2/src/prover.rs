use halo2_proofs::{
    dev::MockProver,
    halo2curves::bn256::{Bn256, Fq, Fr, G1Affine},
    plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey},
    poly::{
        commitment::{Params, ParamsProver},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::{AccumulatorStrategy, SingleStrategy},
        },
        VerificationStrategy,
    },
    transcript::{
        EncodedChallenge, Keccak256Read, Keccak256Write, TranscriptReadBuffer,
        TranscriptWriterBuffer,
    },
};
use number::{BigInt, FieldElement};
use pil_analyzer::Analyzed;
use polyexen::plaf::PlafDisplayBaseTOML;
use rand::{rngs::StdRng, SeedableRng};
use snark_verifier::{
    loader::{
        evm::{self, deploy_and_call, encode_calldata, EvmLoader},
        native::{NativeLoader, LOADER},
        Loader,
    },
    //loader::evm::{self, encode_calldata, Address, EvmLoader, ExecutorBuilder},
    pcs::kzg::{Gwc19, KzgAs, LimbsEncoding},
    //system::halo2::{compile, transcript::evm::EvmTranscript, Config},
    system::halo2::{compile, transcript::evm::EvmTranscript, Config},
    util::arithmetic::{CurveAffine, PrimeField},
    verifier::{self, plonk::PlonkProtocol, SnarkVerifier},
};

use crate::circuit_builder::analyzed_to_circuit;
use std::io;
use std::time::{Duration, Instant};
use std::{io::Cursor, rc::Rc};
use rand::rngs::OsRng;
use itertools::Itertools;

const LIMBS: usize = 4;
const BITS: usize = 68;

type As = KzgAs<Bn256, Gwc19>;
type PlonkSuccinctVerifier = verifier::plonk::PlonkSuccinctVerifier<As, LimbsEncoding<LIMBS, BITS>>;
type PlonkVerifier = verifier::plonk::PlonkVerifier<As, LimbsEncoding<LIMBS, BITS>>;

/// Create a halo2 proof for a given PIL, fixed column values and witness column values
/// We use KZG ([GWC variant](https://eprint.iacr.org/2019/953)) and Keccak256

pub fn prove_ast_read_params<T: FieldElement, R: io::Read>(
    pil: &Analyzed<T>,
    fixed: Vec<(&str, Vec<T>)>,
    witness: Vec<(&str, Vec<T>)>,
    mut params: R,
) -> Vec<u8> {
    if polyexen::expr::get_field_p::<Fr>() != T::modulus().to_arbitrary_integer() {
        panic!("powdr modulus doesn't match halo2 modulus. Make sure you are using Bn254");
    }

    prove_ast(
        pil,
        fixed,
        witness,
        ParamsKZG::<Bn256>::read(&mut params).unwrap(),
    )
}

pub fn prove_ast<T: FieldElement>(
    pil: &Analyzed<T>,
    fixed: Vec<(&str, Vec<T>)>,
    witness: Vec<(&str, Vec<T>)>,
    params: ParamsKZG<Bn256>,
) -> Vec<u8> {
    if polyexen::expr::get_field_p::<Fr>() != T::modulus().to_arbitrary_integer() {
        panic!("powdr modulus doesn't match halo2 modulus. Make sure you are using Bn254");
    }

    let circuit = analyzed_to_circuit(pil, fixed, witness);

    log::debug!("{}", PlafDisplayBaseTOML(&circuit.plaf));

    let inputs = vec![];

    let vk = keygen_vk(&params, &circuit).unwrap();
    let pk = keygen_pk(&params, vk.clone(), &circuit).unwrap();
    let mut transcript: Keccak256Write<
        Vec<u8>,
        G1Affine,
        halo2_proofs::transcript::Challenge255<G1Affine>,
    > = Keccak256Write::init(vec![]);

    create_proof::<KZGCommitmentScheme<Bn256>, ProverGWC<_>, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        &[&inputs],
        StdRng::from_entropy(),
        &mut transcript,
    )
    .unwrap();

    let proof = transcript.finalize();

    let mut transcript = Keccak256Read::init(&proof[..]);

    assert!(verify_proof::<_, VerifierGWC<_>, _, _, _>(
        &params,
        &vk,
        SingleStrategy::new(&params),
        &[&inputs],
        &mut transcript
    )
    .is_ok());

    proof
}

pub fn prove_aggr_read_proof_params<T: FieldElement, R1: io::Read, R2: io::Read>(
    pil: &Analyzed<T>,
    fixed: Vec<(&str, Vec<T>)>,
    witness: Vec<(&str, Vec<T>)>,
    mut proof: R1,
    mut params: R2,
) -> Vec<u8> {
    let mut proof_vec = vec![];
    proof.read_to_end(&mut proof_vec).unwrap();
    prove_aggr(
        pil,
        fixed,
        witness,
        proof_vec,
        ParamsKZG::<Bn256>::read(&mut params).unwrap(),
    )
}

pub fn prove_aggr<T: FieldElement>(
    pil: &Analyzed<T>,
    fixed: Vec<(&str, Vec<T>)>,
    witness: Vec<(&str, Vec<T>)>,
    proof: Vec<u8>,
    params: ParamsKZG<Bn256>,
) -> Vec<u8> {
    if polyexen::expr::get_field_p::<Fr>() != T::modulus().to_arbitrary_integer() {
        panic!("powdr modulus doesn't match halo2 modulus. Make sure you are using Bn254");
    }

    // TODO this is hacky
    let degree = usize::BITS - fixed[0].1.len().leading_zeros() + 1;
    let params_app = {
        let mut params = params.clone();
        params.downsize(degree);
        params
    };

    println!("Generating app circuit...");
    let start = Instant::now();
    let circuit = analyzed_to_circuit(pil, fixed, witness);
    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);

    println!("Generating app circuit verification key...");
    let start = Instant::now();
    let vk_app = keygen_vk(&params_app, &circuit).unwrap();
    //let pk_app = keygen_pk(&params, vk_app.clone(), &circuit).unwrap();
    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);

    println!("Generating circuit for compression snark...");
    let start = Instant::now();
    let protocol_app = compile(
        &params_app,
        &vk_app,
        Config::kzg().with_num_instance(vec![]),
    );
    let empty_snark = aggregation::Snark::new_without_witness(protocol_app.clone());
    let agg_circuit = aggregation::AggregationCircuit::new_without_witness(&params, [empty_snark]);
    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);

    println!("Generating pk for compression snark...");
    let start = Instant::now();
    let pk = gen_pk(&params, &agg_circuit);
    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);

    println!("Generating compressed snark verifier...");
    let start = Instant::now();
    let deployment_code = gen_aggregation_evm_verifier(
        &params,
        pk.get_vk(),
        aggregation::AggregationCircuit::num_instance(),
        aggregation::AggregationCircuit::accumulator_indices(),
    );
    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);

    /*
    println!("Generating app snark with witness proof...");
    let start = Instant::now();
    let snark = aggregation::Snark::new(protocol_app, vec![], proof.clone());
    let agg_circuit = aggregation::AggregationCircuit::new(&params, [snark]);
    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);

    println!("Generating app snark with witness proof...");
    let start = Instant::now();
    let proof = gen_proof::<_, _, EvmTranscript<G1Affine, _, _, _>, EvmTranscript<G1Affine, _, _, _>>(
        &params,
        &pk,
        agg_circuit.clone(),
        agg_circuit.instances(),
    );
    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);
    */

    vec![]
}

pub fn kzg_params(size: usize) -> ParamsKZG<Bn256> {
    ParamsKZG::<Bn256>::new(size as u32)
}

pub fn generate_params<T: FieldElement>(size: usize) -> Vec<u8> {
    if polyexen::expr::get_field_p::<Fr>() != T::modulus().to_arbitrary_integer() {
        panic!("powdr modulus doesn't match halo2 modulus. Make sure you are using Bn254");
    }

    let params = kzg_params(size);
    let mut data = vec![];
    ParamsKZG::<Bn256>::write(&params, &mut data).unwrap();

    data
}

mod aggregation {
    use super::{As, PlonkSuccinctVerifier, BITS, LIMBS};
    use halo2_curves::bn256::{Bn256, Fq, Fr, G1Affine};
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{self, Circuit, ConstraintSystem, Error},
        poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
    };
    use halo2_wrong_ecc::{
        integer::rns::Rns,
        maingate::{
            MainGate, MainGateConfig, MainGateInstructions, RangeChip, RangeConfig,
            RangeInstructions, RegionCtx,
        },
        EccConfig,
    };
    use itertools::Itertools;
    use rand::rngs::OsRng;
    use snark_verifier::{
        loader::{self, halo2::halo2_wrong_ecc, native::NativeLoader},
        pcs::{
            kzg::{KzgAccumulator, KzgSuccinctVerifyingKey, LimbsEncodingInstructions},
            AccumulationScheme, AccumulationSchemeProver,
        },
        system,
        util::arithmetic::{fe_to_limbs, PrimeField},
        verifier::{plonk::PlonkProtocol, SnarkVerifier},
    };
    use std::rc::Rc;

    const T: usize = 5;
    const RATE: usize = 4;
    const R_F: usize = 8;
    const R_P: usize = 60;

    type Svk = KzgSuccinctVerifyingKey<G1Affine>;
    type BaseFieldEccChip = halo2_wrong_ecc::BaseFieldEccChip<G1Affine, LIMBS, BITS>;
    type Halo2Loader<'a> = loader::halo2::Halo2Loader<'a, G1Affine, BaseFieldEccChip>;
    pub type PoseidonTranscript<L, S> =
        system::halo2::transcript::halo2::PoseidonTranscript<G1Affine, L, S, T, RATE, R_F, R_P>;

    pub struct Snark {
        protocol: PlonkProtocol<G1Affine>,
        instances: Vec<Vec<Fr>>,
        proof: Vec<u8>,
    }

    impl Snark {
        pub fn new(
            protocol: PlonkProtocol<G1Affine>,
            instances: Vec<Vec<Fr>>,
            proof: Vec<u8>,
        ) -> Self {
            Self {
                protocol,
                instances,
                proof,
            }
        }

        pub fn new_without_witness(
            protocol: PlonkProtocol<G1Affine>,
        ) -> Self {
            Self {
                protocol,
                instances: vec![],
                proof: Default::default(),
            }
        }

    }

    impl From<Snark> for SnarkWitness {
        fn from(snark: Snark) -> Self {
            Self {
                protocol: snark.protocol,
                instances: snark
                    .instances
                    .into_iter()
                    .map(|instances| instances.into_iter().map(Value::known).collect_vec())
                    .collect(),
                proof: Value::known(snark.proof),
            }
        }
    }

    #[derive(Clone)]
    pub struct SnarkWitness {
        protocol: PlonkProtocol<G1Affine>,
        instances: Vec<Vec<Value<Fr>>>,
        proof: Value<Vec<u8>>,
    }

    impl SnarkWitness {
        fn without_witnesses(&self) -> Self {
            SnarkWitness {
                protocol: self.protocol.clone(),
                instances: self
                    .instances
                    .iter()
                    .map(|instances| vec![Value::unknown(); instances.len()])
                    .collect(),
                proof: Value::unknown(),
            }
        }

        fn proof(&self) -> Value<&[u8]> {
            self.proof.as_ref().map(Vec::as_slice)
        }
    }

    pub fn aggregate<'a>(
        svk: &Svk,
        loader: &Rc<Halo2Loader<'a>>,
        snarks: &[SnarkWitness],
        as_proof: Value<&'_ [u8]>,
    ) -> KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>> {
        let assign_instances = |instances: &[Vec<Value<Fr>>]| {
            instances
                .iter()
                .map(|instances| {
                    instances
                        .iter()
                        .map(|instance| loader.assign_scalar(*instance))
                        .collect_vec()
                })
                .collect_vec()
        };

        let accumulators = snarks
            .iter()
            .flat_map(|snark| {
                let protocol = snark.protocol.loaded(loader);
                let instances = assign_instances(&snark.instances);
                let mut transcript =
                    PoseidonTranscript::<Rc<Halo2Loader>, _>::new(loader, snark.proof());
                let proof =
                    PlonkSuccinctVerifier::read_proof(svk, &protocol, &instances, &mut transcript)
                        .unwrap();
                PlonkSuccinctVerifier::verify(svk, &protocol, &instances, &proof).unwrap()
            })
            .collect_vec();

        let acccumulator = {
            let mut transcript = PoseidonTranscript::<Rc<Halo2Loader>, _>::new(loader, as_proof);
            let proof =
                As::read_proof(&Default::default(), &accumulators, &mut transcript).unwrap();
            As::verify(&Default::default(), &accumulators, &proof).unwrap()
        };

        acccumulator
    }

    #[derive(Clone)]
    pub struct AggregationConfig {
        main_gate_config: MainGateConfig,
        range_config: RangeConfig,
    }

    impl AggregationConfig {
        pub fn configure<F: PrimeField>(
            meta: &mut ConstraintSystem<F>,
            composition_bits: Vec<usize>,
            overflow_bits: Vec<usize>,
        ) -> Self {
            let main_gate_config = MainGate::<F>::configure(meta);
            let range_config =
                RangeChip::<F>::configure(meta, &main_gate_config, composition_bits, overflow_bits);
            AggregationConfig {
                main_gate_config,
                range_config,
            }
        }

        pub fn main_gate(&self) -> MainGate<Fr> {
            MainGate::new(self.main_gate_config.clone())
        }

        pub fn range_chip(&self) -> RangeChip<Fr> {
            RangeChip::new(self.range_config.clone())
        }

        pub fn ecc_chip(&self) -> BaseFieldEccChip {
            BaseFieldEccChip::new(EccConfig::new(
                self.range_config.clone(),
                self.main_gate_config.clone(),
            ))
        }
    }

    #[derive(Clone)]
    pub struct AggregationCircuit {
        svk: Svk,
        snarks: Vec<SnarkWitness>,
        instances: Vec<Fr>,
        as_proof: Value<Vec<u8>>,
    }

    impl AggregationCircuit {
        pub fn new(params: &ParamsKZG<Bn256>, snarks: impl IntoIterator<Item = Snark>) -> Self {
            let svk = params.get_g()[0].into();
            let snarks = snarks.into_iter().collect_vec();

            let accumulators = snarks
                .iter()
                .flat_map(|snark| {
                    let mut transcript =
                        PoseidonTranscript::<NativeLoader, _>::new(snark.proof.as_slice());
                    let proof = PlonkSuccinctVerifier::read_proof(
                        &svk,
                        &snark.protocol,
                        &snark.instances,
                        &mut transcript,
                    )
                    .unwrap();
                    PlonkSuccinctVerifier::verify(&svk, &snark.protocol, &snark.instances, &proof)
                        .unwrap()
                })
                .collect_vec();

            let (accumulator, as_proof) = {
                let mut transcript = PoseidonTranscript::<NativeLoader, _>::new(Vec::new());
                let accumulator =
                    As::create_proof(&Default::default(), &accumulators, &mut transcript, OsRng)
                        .unwrap();
                (accumulator, transcript.finalize())
            };

            let KzgAccumulator { lhs, rhs } = accumulator;
            let instances = [lhs.x, lhs.y, rhs.x, rhs.y]
                .map(fe_to_limbs::<_, _, LIMBS, BITS>)
                .concat();

            Self {
                svk,
                snarks: snarks.into_iter().map_into().collect(),
                instances,
                as_proof: Value::known(as_proof),
            }
        }

        pub fn new_without_witness(params: &ParamsKZG<Bn256>, snarks: impl IntoIterator<Item = Snark>) -> Self {
            let svk = params.get_g()[0].into();
            let snarks = snarks.into_iter().collect_vec();

            Self {
                svk,
                snarks: snarks.into_iter().map_into().collect(),
                instances: vec![],
                as_proof: Value::unknown(),
            }
        }

        pub fn accumulator_indices() -> Vec<(usize, usize)> {
            (0..4 * LIMBS).map(|idx| (0, idx)).collect()
        }

        pub fn num_instance() -> Vec<usize> {
            vec![4 * LIMBS]
        }

        pub fn instances(&self) -> Vec<Vec<Fr>> {
            vec![self.instances.clone()]
        }

        pub fn as_proof(&self) -> Value<&[u8]> {
            self.as_proof.as_ref().map(Vec::as_slice)
        }
    }

    impl Circuit<Fr> for AggregationCircuit {
        type Config = AggregationConfig;
        type FloorPlanner = SimpleFloorPlanner;
        //#[cfg(feature = "halo2_circuit_params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self {
                svk: self.svk,
                snarks: self
                    .snarks
                    .iter()
                    .map(SnarkWitness::without_witnesses)
                    .collect(),
                instances: Vec::new(),
                as_proof: Value::unknown(),
            }
        }

        fn configure(meta: &mut plonk::ConstraintSystem<Fr>) -> Self::Config {
            AggregationConfig::configure(
                meta,
                vec![BITS / LIMBS],
                Rns::<Fq, Fr, LIMBS, BITS>::construct().overflow_lengths(),
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), plonk::Error> {
            let main_gate = config.main_gate();
            let range_chip = config.range_chip();

            range_chip.load_table(&mut layouter)?;

            let accumulator_limbs = layouter.assign_region(
                || "",
                |region| {
                    let ctx = RegionCtx::new(region, 0);

                    let ecc_chip = config.ecc_chip();
                    let loader = Halo2Loader::new(ecc_chip, ctx);
                    let accumulator = aggregate(&self.svk, &loader, &self.snarks, self.as_proof());

                    let accumulator_limbs = [accumulator.lhs, accumulator.rhs]
                        .iter()
                        .map(|ec_point| {
                            loader.ecc_chip().assign_ec_point_to_limbs(
                                &mut loader.ctx_mut(),
                                ec_point.assigned(),
                            )
                        })
                        .collect::<Result<Vec<_>, Error>>()?
                        .into_iter()
                        .flatten();

                    Ok(accumulator_limbs)
                },
            )?;

            for (row, limb) in accumulator_limbs.enumerate() {
                main_gate.expose_public(layouter.namespace(|| ""), limb, row)?;
            }

            Ok(())
        }
    }
}

fn gen_pk<C: Circuit<Fr>>(params: &ParamsKZG<Bn256>, circuit: &C) -> ProvingKey<G1Affine> {
    let vk = keygen_vk(params, circuit).unwrap();
    keygen_pk(params, vk, circuit).unwrap()
}

fn gen_proof<
    C: Circuit<Fr>,
    E: EncodedChallenge<G1Affine>,
    TR: TranscriptReadBuffer<Cursor<Vec<u8>>, G1Affine, E>,
    TW: TranscriptWriterBuffer<Vec<u8>, G1Affine, E>,
>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
) -> Vec<u8> {
    MockProver::run(params.k(), &circuit, instances.clone())
        .unwrap()
        .assert_satisfied();

    let instances = instances
        .iter()
        .map(|instances| instances.as_slice())
        .collect_vec();
    let proof = {
        let mut transcript = TW::init(Vec::new());
        create_proof::<KZGCommitmentScheme<Bn256>, ProverGWC<_>, _, _, TW, _>(
            params,
            pk,
            &[circuit],
            &[instances.as_slice()],
            OsRng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };

    let accept = {
        let mut transcript = TR::init(Cursor::new(proof.clone()));
        VerificationStrategy::<_, VerifierGWC<_>>::finalize(
            verify_proof::<_, VerifierGWC<_>, _, TR, _>(
                params.verifier_params(),
                pk.get_vk(),
                AccumulatorStrategy::new(params.verifier_params()),
                &[instances.as_slice()],
                &mut transcript,
            )
            .unwrap(),
        )
    };
    assert!(accept);

    proof
}

fn gen_aggregation_evm_verifier(
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    num_instance: Vec<usize>,
    accumulator_indices: Vec<(usize, usize)>,
) -> Vec<u8> {
    let protocol = compile(
        params,
        vk,
        Config::kzg()
            .with_num_instance(num_instance.clone())
            .with_accumulator_indices(Some(accumulator_indices)),
    );
    let vk = (params.get_g()[0], params.g2(), params.s_g2()).into();

    let loader = EvmLoader::new::<Fq, Fr>();
    let protocol = protocol.loaded(&loader);
    let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(&loader);

    let instances = transcript.load_instances(num_instance);
    let proof = PlonkVerifier::read_proof(&vk, &protocol, &instances, &mut transcript).unwrap();
    PlonkVerifier::verify(&vk, &protocol, &instances, &proof).unwrap();

    evm::compile_yul(&loader.yul_code())
}
