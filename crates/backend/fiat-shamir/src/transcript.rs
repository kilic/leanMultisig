use field::Field;
use serde::{Deserialize, Serialize};
use symetric::merkle::Sha256Digest;

use crate::PrunedMerklePaths;

pub const DIGEST_LEN_FE: usize = 8;

#[derive(Debug, Clone)]
pub struct MerkleOpening<F, Digest = [F; DIGEST_LEN_FE]> {
    pub leaf_data: Vec<F>,
    pub path: Vec<Digest>,
}

/// "RawProof": the format which is used in the zkVM recursion program (no Merkle pruning, no sumcheck optimization to send less data, etc)
#[derive(Clone)]
pub struct RawProof<F> {
    pub transcript: Vec<F>,
    pub merkle_openings: Vec<MerkleOpening<F>>,
}

#[derive(Debug, Clone)]
pub struct MerklePath<Data, Digest> {
    pub leaf_data: Vec<Data>,
    pub sibling_hashes: Vec<Digest>,
    // does not appear in the proof itself, but useful for Merkle pruning
    pub leaf_index: usize,
}

#[derive(Debug, Clone)]
pub struct MerklePaths<Data, Digest>(pub(crate) Vec<MerklePath<Data, Digest>>);

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Proof<F, Digest = [F; DIGEST_LEN_FE]> {
    pub(crate) transcript: Vec<F>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) commitments: Vec<Digest>,
    pub(crate) merkle_paths: Vec<PrunedMerklePaths<F, Digest>>,
}

pub trait ProofDigestSize<F: Field> {
    fn digest_size_bytes() -> usize;
}

impl<F: Field> ProofDigestSize<F> for [F; DIGEST_LEN_FE] {
    fn digest_size_bytes() -> usize {
        DIGEST_LEN_FE * F::bits().div_ceil(8)
    }
}

impl<F: Field> ProofDigestSize<F> for Sha256Digest {
    fn digest_size_bytes() -> usize {
        size_of::<Sha256Digest>()
    }
}

impl<F: Field, Digest: ProofDigestSize<F>> Proof<F, Digest> {
    pub fn proof_size_bytes(&self) -> usize {
        let field_bytes = F::bits().div_ceil(8);
        let merkle_size: usize = self
            .merkle_paths
            .iter()
            .map(|paths| {
                paths.leaf_data.iter().map(|d| d.len() * field_bytes).sum::<usize>()
                    + paths
                        .paths
                        .iter()
                        .map(|(_, sh): &(_, Vec<_>)| sh.len() * Digest::digest_size_bytes())
                        .sum::<usize>()
            })
            .sum();
        self.transcript.len() * field_bytes + self.commitments.len() * Digest::digest_size_bytes() + merkle_size
    }
}

impl<F: Field> Proof<F> {
    pub fn proof_size_fe(&self) -> usize {
        let merkle_size: usize = self
            .merkle_paths
            .iter()
            .map(|paths| {
                paths.leaf_data.iter().map(|d| d.len()).sum::<usize>()
                    + paths
                        .paths
                        .iter()
                        .map(|(_, sh): &(_, Vec<_>)| sh.len() * DIGEST_LEN_FE)
                        .sum::<usize>()
            })
            .sum();
        self.transcript.len() + merkle_size
    }
}
