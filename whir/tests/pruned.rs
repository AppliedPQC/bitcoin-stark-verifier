//! Expanding a real Plonky3 pruned multi-opening into per-query paths.
//!
//! The proof authenticates every queried row with one compact multiproof, which
//! a script cannot walk: `open_query` checks one leaf against one complete
//! sibling path. `whir::pruned::expand` recovers those paths. Nothing here is
//! hand-built -- the tree, the opening and the pruned digests all come from
//! Plonky3's own `MerkleTreeMmcs`, with the compression WHIR uses.

use bitcoin_script::{define_pushable, script};
use p3_commit::Mmcs;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::{default_koalabear_poseidon2_16, KoalaBear, Poseidon2KoalaBear};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use poseidon2::merkle::{self, DIGEST};
use whir::pruned;

define_pushable!();

type F = KoalaBear;
type Perm = Poseidon2KoalaBear<16>;
type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type PackedF = <F as Field>::Packing;
type MyMmcs = MerkleTreeMmcs<PackedF, PackedF, MyHash, MyCompress, 2, 8>;

fn u32s(d: &[F; DIGEST]) -> [u32; DIGEST] {
    core::array::from_fn(|i| d[i].as_canonical_u32())
}

/// A tree, an opening at several indices, and the pruned proof over them.
fn open(depth: usize, width: usize, indices: &[usize]) -> ([u32; DIGEST], Vec<[u32; DIGEST]>, Vec<[u32; DIGEST]>) {
    let perm = default_koalabear_poseidon2_16();
    let mmcs = MyMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 0);

    let height = 1usize << depth;
    let values: Vec<F> = (0..height * width).map(|i| F::from_u32(1000 + i as u32)).collect();
    let (root, data) = mmcs.commit_matrix(RowMajorMatrix::new(values, width));

    let (opened, pruned_proof) = mmcs.open_multi_batch(indices, &data);

    // The leaf is the hash of the opened row, which is what the tree stores.
    let leaves: Vec<[u32; DIGEST]> = opened
        .iter()
        .map(|per_query| {
            let row: Vec<u32> = per_query[0].iter().map(|x| x.as_canonical_u32()).collect();
            poseidon2::reference::hash_row(&row)
        })
        .collect();

    let boundaries: Vec<[u32; DIGEST]> = pruned_proof.sibling_hashes.iter().map(u32s).collect();
    let root_c: [u32; DIGEST] = u32s(&root.roots()[0]);
    (root_c, leaves, boundaries)
}

/// Every expanded path reaches the committed root, for a range of query sets.
///
/// The interesting cases are the ones pruning actually compresses: adjacent
/// leaves share a parent, so the proof omits their mutual siblings and `expand`
/// has to recompute them rather than read them off the wire.
#[test]
fn expanded_paths_reach_the_committed_root() {
    let depth = 4;
    for indices in [
        vec![11usize],              // a lone leaf: the path is fully supplied
        vec![2, 3],                 // siblings: neither sibling is on the wire
        vec![0, 1, 2, 3],           // a whole subtree: most of it recomputed
        vec![0, 5, 9, 14],          // scattered
        vec![1, 1, 7],              // a duplicate query
        (0..16).collect::<Vec<_>>(), // every leaf: nothing left to supply
    ] {
        let (root, leaves, boundaries) = open(depth, 1, &indices);
        let paths = pruned::expand(&boundaries, &indices, &leaves, depth)
            .unwrap_or_else(|e| panic!("expand failed on {indices:?}: {e:?}"));
        assert_eq!(paths.len(), indices.len(), "one path per query, duplicates included");

        for p in &paths {
            assert_eq!(p.siblings.len(), depth, "a full path has one sibling per level");
            let bits: Vec<bool> = (0..depth).map(|i| (p.index >> i) & 1 == 1).collect();
            assert_eq!(
                poseidon2::reference::merkle_root(p.leaf, &p.siblings, &bits),
                root,
                "expanded path for leaf {} of {indices:?} missed the root",
                p.index
            );
        }
    }
}

/// The expanded path is what the script's own walk consumes.
#[test]
fn an_expanded_path_verifies_in_bitcoin_script() {
    let depth = 4;
    let indices = vec![2usize, 3, 9];
    let (root, leaves, boundaries) = open(depth, 1, &indices);
    let paths = pruned::expand(&boundaries, &indices, &leaves, depth).expect("expand");

    for p in &paths {
        let bits: Vec<bool> = (0..depth).map(|i| (p.index >> i) & 1 == 1).collect();
        let info = bitcoin_scriptexec::execute_script(script! {
            for x in root.iter() { {*x} }
            for i in (0..depth).rev() { for x in p.siblings[i].iter() { {*x} } }
            for x in p.leaf.iter() { {*x} }
            for &b in bits.iter().rev() { { if b { 1u32 } else { 0u32 } } OP_TOALTSTACK }
            { merkle::merkle_verify_from_altstack(depth) }
        });
        assert!(
            info.error.is_none(),
            "script rejected the expanded path for leaf {}: {:?} at {:?}",
            p.index,
            info.error,
            info.last_opcode
        );
    }
}

/// A proof carrying the wrong number of boundary digests is refused.
#[test]
fn a_miscounted_proof_is_rejected() {
    let depth = 4;
    let indices = vec![2usize, 9];
    let (_root, leaves, boundaries) = open(depth, 1, &indices);

    let mut short = boundaries.clone();
    short.pop();
    assert!(matches!(
        pruned::expand(&short, &indices, &leaves, depth),
        Err(pruned::Error::SiblingCount { .. })
    ));

    let mut long = boundaries.clone();
    long.push([0; DIGEST]);
    assert!(matches!(
        pruned::expand(&long, &indices, &leaves, depth),
        Err(pruned::Error::SiblingCount { .. })
    ));
}
