//! A real WHIR proof over `BinaryField128` on the additive domain, with Blake3
//! commitments, run through a byte-logging challenger.
//!
//! This is the proof the garbled verifier will check, produced by Plonky3's
//! prover exactly as `examples/prove_hash_binary` configures WHIR, minus the
//! boolean-trace front end: the committed object is a plain multilinear over
//! `GF(2^128)`. The logger records every byte Plonky3's verifier observes and
//! samples, which is the executed transcript a circuit must reproduce.

use p3_binary_field::{BinaryChallenger, BinaryField128};
use p3_binary_pcs::whir::{BinaryWhirProfile, BooleanWhirDomain, recommended_cap_height};
use p3_blake3::Blake3;
use p3_challenger::{CanObserve, CanSample, HashChallenger};
use p3_commit::MultilinearPcs;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_sumcheck::layout::{Layout, SuffixProver, Table};
use p3_sumcheck::{OpeningProtocol, OpeningRequest, TableShape, TableSpec};
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher};
use p3_whir::WhirProver;
use rand010::SeedableRng;
use rand010::rngs::SmallRng;
use std::sync::{Arc, Mutex};

type F = BinaryField128;
type Hash = SerializingHasher<Blake3>;
type Compress = CompressionFunctionFromHasher<Blake3, 2, 32>;
type Mmcs = MerkleTreeMmcs<F, u8, Hash, Compress, 2, 32>;
type Inner = HashChallenger<u8, Blake3, 32>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Observe(u8),
    Sample(u8),
}

/// `HashChallenger` with every observed and sampled byte logged. Sampling into
/// a slice is forwarded whole, since `HashChallenger` overrides it, and the
/// bytes it produced are logged in order. The log is shared out, as
/// `BinaryChallenger` keeps its inner challenger private.
#[derive(Clone)]
struct ByteLogger {
    inner: Inner,
    log: Arc<Mutex<Vec<Op>>>,
}

impl CanObserve<u8> for ByteLogger {
    fn observe(&mut self, value: u8) {
        self.log.lock().unwrap().push(Op::Observe(value));
        self.inner.observe(value);
    }
}

impl CanSample<u8> for ByteLogger {
    fn sample(&mut self) -> u8 {
        let v = self.inner.sample();
        self.log.lock().unwrap().push(Op::Sample(v));
        v
    }

    fn sample_into_slice(&mut self, values: &mut [u8]) {
        self.inner.sample_into_slice(values);
        self.log.lock().unwrap().extend(values.iter().map(|&v| Op::Sample(v)));
    }
}

type Challenger = BinaryChallenger<F, ByteLogger>;
type Pcs = WhirProver<F, F, BooleanWhirDomain, Mmcs, Challenger, SuffixProver<F, F>>;

fn challenger() -> (Challenger, Arc<Mutex<Vec<Op>>>) {
    let log = Arc::new(Mutex::new(Vec::new()));
    let inner = ByteLogger { inner: HashChallenger::new(vec![], Blake3), log: log.clone() };
    (BinaryChallenger::new(inner), log)
}

fn runs(log: &[Op]) -> String {
    let mut out = Vec::new();
    let mut i = 0;
    while i < log.len() {
        let observing = matches!(log[i], Op::Observe(_));
        let start = i;
        while i < log.len() && matches!(log[i], Op::Observe(_)) == observing {
            i += 1;
        }
        out.push(format!("{}{}", if observing { 'O' } else { 'S' }, i - start));
    }
    out.join(" ")
}

/// Prove a random `GF(2^128)` multilinear and verify it through the logger.
fn prove_and_log(num_vars: usize, log_inv_rate: usize, folding: usize) -> Vec<Op> {
    let width = 1usize;
    let specs = vec![TableSpec::new(
        TableShape::new(num_vars, width),
        vec![OpeningRequest::new(vec![0], vec![])],
    )];
    let mut rng = SmallRng::seed_from_u64(11);
    let tables: Vec<Table<F>> = vec![Table::rand(&mut rng, width, num_vars)];
    let witness = <SuffixProver<F, F> as Layout<F, F>>::new_witness(tables, folding);
    let protocol = OpeningProtocol::new(specs).pad_to_min_num_variables(folding);
    let num_variables = witness.num_variables();

    let domain = BooleanWhirDomain::default();
    let config = BinaryWhirProfile::proven_list_decoding(110, log_inv_rate, folding)
        .config::<F, F, Challenger, _>(num_variables, &domain)
        .expect("profile config");
    let cap_height = recommended_cap_height(&config);
    let mmcs = Mmcs::new(Hash::new(Blake3), Compress::new(Blake3), cap_height);
    let pcs = Pcs::new(config, domain, mmcs);

    let (mut ch, _) = challenger();
    let (commitment, prover_data) =
        <Pcs as MultilinearPcs<F, Challenger>>::commit(&pcs, witness, &mut ch).expect("commit");
    let proof = <Pcs as MultilinearPcs<F, Challenger>>::open(&pcs, prover_data, protocol.clone(), &mut ch)
        .expect("open");

    let (mut ch, log) = challenger();
    <Pcs as MultilinearPcs<F, Challenger>>::verify(&pcs, &commitment, &proof, &mut ch, protocol)
        .expect("Plonky3's own verifier must accept the proof");
    let out = log.lock().unwrap().clone();
    out
}

#[test]
fn plonky3_binary_whir_proof_verifies_and_its_byte_transcript_is_logged() {
    for (num_vars, rate, folding) in [(8usize, 3usize, 4usize), (12, 3, 4)] {
        let log = prove_and_log(num_vars, rate, folding);
        let observed = log.iter().filter(|o| matches!(o, Op::Observe(_))).count();
        let sampled = log.len() - observed;
        eprintln!(
            "{num_vars} vars, rate 1/{}, folding {folding}: {observed} bytes observed, {sampled} sampled\nschedule: {}",
            1 << rate,
            runs(&log)
        );
        assert!(sampled > 0);
    }
}
