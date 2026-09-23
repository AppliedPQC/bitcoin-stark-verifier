//! Expanding Plonky3's pruned multi-opening into one full path per query.
//!
//! A WHIR proof authenticates every queried row with a single
//! [`PrunedMerklePaths`]: the minimal set of *boundary* sibling digests. Any
//! sibling that another queried leaf can reconstruct is simply left out, and an
//! amortized verifier walks all the leaves together, recomputing those as it
//! climbs.
//!
//! The Bitcoin Script verifier cannot walk leaves together. `open_query` checks
//! one leaf against one complete sibling path, because a script has no place to
//! keep a frontier between queries. So a real proof has to be expanded first:
//! every omitted sibling recomputed, and each query given the full path it would
//! have carried had it been opened alone.
//!
//! That expansion is what this module does. It costs the amortization back --
//! the point of pruning -- which is the right trade here: the script's own cost
//! model already prices one independent path per query.
//!
//! # Provenance
//!
//! `walk_frontier`, `sibling_offset` and `restore_boundaries` are ports of
//! `prune_paths`/`restore_paths` in Plonky3's `p3-merkle-tree`
//! (`merkle-tree/src/pruning.rs`), which are `pub(crate)` there and so cannot be
//! called from outside. Plonky3 is MIT/Apache-2.0, Copyright (c) 2022 The
//! Plonky3 Authors. The wire order they define is normative: level 0 first,
//! within a level groups by ascending parent index, within a group missing child
//! positions ascending. `expand` below is new -- Plonky3 never needs per-leaf
//! paths, so it has no equivalent.
//!
//! Only the binary case is implemented, which is what WHIR's trees use: the
//! compression is `TruncatedPermutation<Perm, 2, 8, 16>`.


/// Digest type of the trees this expands: a 32-byte hash.
pub type Digest = [u8; 32];

/// Plonky3's `CompressionFunctionFromHasher<Blake3, 2, 32>`: Blake3 of the two
/// children concatenated.
pub fn compress(left: &Digest, right: &Digest) -> Digest {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(left);
    buf[32..].copy_from_slice(right);
    *blake3::hash(&buf).as_bytes()
}

/// What went wrong expanding a pruned proof.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// The proof carried a different number of boundary digests than the
    /// frontier over these indices requires.
    SiblingCount { expected: usize, got: usize },
    /// A queried index does not name a leaf of a tree of this depth.
    IndexOutOfRange { index: usize, depth: usize },
    /// A query has no opened row, or a row has no leaf digest.
    MissingLeaf { index: usize },
}

/// Runs `visit` once per boundary child of the frontier, in wire order.
///
/// The frontier starts at the sorted-unique queried leaves and folds up one
/// level per step, grouping nodes that share a parent. A child that a frontier
/// node already covers is recomputable and skipped; every other child is a
/// boundary and fires one callback.
///
/// `visit` receives the level, the slot whose buffer leads the group, the lead's
/// position in the group, and the boundary child's position.
///
/// Ported from Plonky3's `walk_frontier`; pruning and restoration share it so
/// that both agree on wire order.
fn walk_frontier(sorted_unique: &[usize], depth: usize, mut visit: impl FnMut(usize, usize, usize, usize)) {
    if sorted_unique.is_empty() {
        return;
    }
    // (node index at this level, slot of the smallest queried leaf beneath it)
    let mut nodes: Vec<(usize, usize)> = sorted_unique.iter().enumerate().map(|(slot, &i)| (i, slot)).collect();
    let mut parents: Vec<(usize, usize)> = Vec::with_capacity(nodes.len());

    for level in 0..depth {
        parents.clear();
        let mut i = 0;
        while i < nodes.len() {
            let group_start = (nodes[i].0 / 2) * 2;
            let lead = nodes[i].1;
            let lead_pos = nodes[i].0 - group_start;
            let mut member = i;
            for k in 0..2 {
                if member < nodes.len() && nodes[member].0 == group_start + k {
                    member += 1;
                } else {
                    visit(level, lead, lead_pos, k);
                }
            }
            parents.push((group_start / 2, lead));
            i = member;
        }
        core::mem::swap(&mut nodes, &mut parents);
    }
}

/// Offset of child `k` inside a lead path's one-per-level sibling slot.
///
/// Binary, so a level holds exactly one sibling and the offset is the level
/// itself; the function is kept to mirror Plonky3's arity-general form.
const fn sibling_offset(_k: usize, _lead_pos: usize) -> usize {
    0
}

/// Scatters the proof's boundary digests into per-leaf buffers.
///
/// Positions the frontier does not touch are left `None`: they are the ones an
/// amortized verifier recomputes, and [`expand`] fills them in.
///
/// Ported from Plonky3's `restore_paths`. The indices come from the caller --
/// the verifier's own transcript -- never from the proof.
fn restore_boundaries(
    boundaries: &[Digest],
    sorted_unique: &[usize],
    depth: usize,
) -> Result<Vec<Vec<Option<Digest>>>, Error> {
    if sorted_unique.is_empty() {
        return if boundaries.is_empty() {
            Ok(vec![])
        } else {
            Err(Error::SiblingCount { expected: 0, got: boundaries.len() })
        };
    }
    let mut restored = vec![vec![None; depth]; sorted_unique.len()];
    let mut cursor = 0;
    let mut overrun = false;
    walk_frontier(sorted_unique, depth, |level, lead, lead_pos, k| {
        match boundaries.get(cursor) {
            Some(d) => restored[lead][level + sibling_offset(k, lead_pos)] = Some(*d),
            None => overrun = true,
        }
        cursor += 1;
    });
    if overrun || cursor != boundaries.len() {
        return Err(Error::SiblingCount { expected: cursor, got: boundaries.len() });
    }
    Ok(restored)
}

/// One query's complete authentication path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path {
    /// The leaf's index, which also gives the direction bits.
    pub index: usize,
    /// The leaf digest: the hash of the opened row.
    pub leaf: Digest,
    /// One sibling per level, level 0 first -- what `merkle_verify_from_altstack`
    /// consumes.
    pub siblings: Vec<Digest>,
}

/// Expands a pruned multi-opening into one complete path per query.
///
/// `indices` and `leaves` are in query order, as the transcript produced them;
/// duplicates are allowed and share a path. `boundaries` is the proof's
/// `sibling_hashes`, `log_leaves` is `log2` of the domain and `cap_height`
/// that of the Merkle cap the tree is committed as (`0` for a single root).
///
/// The walk climbs all queried leaves together, exactly as an amortized verifier
/// would: at each level a group's sibling is either a boundary digest, which the
/// proof supplied, or a node this walk has already computed from other opened
/// leaves. Recording whichever it was, per leaf, is what turns one amortized
/// proof into `n` independent paths.
pub fn expand(
    boundaries: &[Digest],
    indices: &[usize],
    leaves: &[Digest],
    log_leaves: usize,
    cap_height: usize,
) -> Result<Vec<Path>, Error> {
    if indices.len() != leaves.len() {
        return Err(Error::MissingLeaf { index: indices.len().min(leaves.len()) });
    }
    for &i in indices {
        if log_leaves < usize::BITS as usize && i >= 1usize << log_leaves {
            return Err(Error::IndexOutOfRange { index: i, depth: log_leaves });
        }
    }
    // A Merkle cap of height `h` ends every path `h` levels early: the walk
    // stops at the cap's roots, and `Path::index >> depth` names the root.
    assert!(cap_height <= log_leaves, "the cap is not taller than the tree");
    let depth = log_leaves - cap_height;

    // Sorted-unique order is the order the frontier -- and so the wire -- uses.
    let mut sorted_unique: Vec<usize> = indices.to_vec();
    sorted_unique.sort_unstable();
    sorted_unique.dedup();

    let restored = restore_boundaries(boundaries, &sorted_unique, depth)?;

    // Leaf digest per unique index, taken from the caller's query-order rows.
    let leaf_of = |idx: usize| -> Result<Digest, Error> {
        indices
            .iter()
            .position(|&i| i == idx)
            .map(|p| leaves[p])
            .ok_or(Error::MissingLeaf { index: idx })
    };

    let mut siblings: Vec<Vec<Digest>> = vec![Vec::with_capacity(depth); sorted_unique.len()];
    // The running frontier: (node index, digest, slots of every queried leaf beneath).
    let mut nodes: Vec<(usize, Digest, Vec<usize>)> = sorted_unique
        .iter()
        .enumerate()
        .map(|(slot, &idx)| leaf_of(idx).map(|d| (idx, d, vec![slot])))
        .collect::<Result<_, _>>()?;

    for level in 0..depth {
        let mut parents: Vec<(usize, Digest, Vec<usize>)> = Vec::with_capacity(nodes.len());
        let mut i = 0;
        while i < nodes.len() {
            let group_start = (nodes[i].0 / 2) * 2;
            let paired = i + 1 < nodes.len() && nodes[i + 1].0 == group_start + 1 && nodes[i].0 == group_start;

            let (left, right, members): (Digest, Digest, Vec<usize>) = if paired {
                // Both children were opened: each is the other's sibling, and the
                // proof rightly carried neither.
                let mut m = nodes[i].2.clone();
                m.extend_from_slice(&nodes[i + 1].2);
                for &s in &nodes[i].2 {
                    siblings[s].push(nodes[i + 1].1);
                }
                for &s in &nodes[i + 1].2 {
                    siblings[s].push(nodes[i].1);
                }
                (nodes[i].1, nodes[i + 1].1, m)
            } else {
                // One child opened: the other is a boundary the proof supplied,
                // recorded against this group's lead.
                let lead = nodes[i].2[0];
                let sib = restored[lead][level].ok_or(Error::SiblingCount { expected: level, got: 0 })?;
                for &s in &nodes[i].2 {
                    siblings[s].push(sib);
                }
                if nodes[i].0 == group_start {
                    (nodes[i].1, sib, nodes[i].2.clone())
                } else {
                    (sib, nodes[i].1, nodes[i].2.clone())
                }
            };

            parents.push((group_start / 2, compress(&left, &right), members));
            i += if paired { 2 } else { 1 };
        }
        nodes = parents;
    }

    // Back to query order, duplicates included.
    indices
        .iter()
        .map(|&idx| {
            let slot = sorted_unique.binary_search(&idx).map_err(|_| Error::MissingLeaf { index: idx })?;
            Ok(Path { index: idx, leaf: leaf_of(idx)?, siblings: siblings[slot].clone() })
        })
        .collect()
}
