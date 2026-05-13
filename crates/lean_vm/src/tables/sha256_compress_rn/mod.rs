//! Incomplete rookie-numbers-style SHA-256 compression experiment.
//!
//! This table preserves the rookie-numbers scheduling/compression witness layout but deliberately
//! omits all lookup/preprocessed relation checks. It is only intended for cost comparison against
//! the complete `sha256_compress` table.

use crate::{F, PrecompileCompTimeArgs, RunnerError, Table};
use backend::{PrimeCharacteristicRing, PrimeField32};
use utils::ToUsize;

mod air;

mod columns;
pub use columns::*;

mod trace_gen;
pub use trace_gen::*;

pub const SHA256_RN_WORDS: usize = 8;
pub const SHA256_RN_BLOCK_WORDS: usize = 16;
pub const SHA256_RN_U32_LIMBS: usize = 2;
pub const SHA256_RN_COMPRESS_ROUNDS: usize = 64;
pub const SHA256_RN_SCHEDULE_EXTENSIONS: usize = SHA256_RN_COMPRESS_ROUNDS - SHA256_RN_BLOCK_WORDS;

pub const SHA256_RN_STATE_LIMBS: usize = SHA256_RN_WORDS * SHA256_RN_U32_LIMBS;
pub const SHA256_RN_BLOCK_LIMBS: usize = SHA256_RN_BLOCK_WORDS * SHA256_RN_U32_LIMBS;

pub const SHA256_RN_PRECOMPILE_DATA: usize = 6;
pub const SHA256_COMPRESS_RN_NAME: &str = "sha256_compress_rn";

pub const BITS_PER_LIMB: usize = 16;
pub const LIMB_MASK: u32 = 0xffff;

pub const SHA256_RN_VIRTUAL_BIG_SIGMA1_I0_ARITY: usize = 5;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA1_I1_ARITY: usize = 5;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA1_O2_ARITY: usize = 4;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA0_I0_ARITY: usize = 6;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA0_I1_ARITY: usize = 6;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA0_O2_ARITY: usize = 4;
pub const SHA256_RN_VIRTUAL_MAJ_I0_LOW_ARITY: usize = 4;
pub const SHA256_RN_VIRTUAL_MAJ_I0_HIGH_0_ARITY: usize = 4;
pub const SHA256_RN_VIRTUAL_MAJ_I0_HIGH_1_ARITY: usize = 4;
pub const SHA256_RN_VIRTUAL_MAJ_I1_LOW_0_ARITY: usize = 4;
pub const SHA256_RN_VIRTUAL_MAJ_I1_LOW_1_ARITY: usize = 4;
pub const SHA256_RN_VIRTUAL_MAJ_I1_HIGH_ARITY: usize = 4;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA1_I0_START: usize = 0;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA1_I1_START: usize =
    SHA256_RN_VIRTUAL_BIG_SIGMA1_I0_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_BIG_SIGMA1_I0_ARITY;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA1_O2_START: usize =
    SHA256_RN_VIRTUAL_BIG_SIGMA1_I1_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_BIG_SIGMA1_I1_ARITY;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA0_I0_START: usize =
    SHA256_RN_VIRTUAL_BIG_SIGMA1_O2_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_BIG_SIGMA1_O2_ARITY;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA0_I1_START: usize =
    SHA256_RN_VIRTUAL_BIG_SIGMA0_I0_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_BIG_SIGMA0_I0_ARITY;
pub const SHA256_RN_VIRTUAL_BIG_SIGMA0_O2_START: usize =
    SHA256_RN_VIRTUAL_BIG_SIGMA0_I1_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_BIG_SIGMA0_I1_ARITY;
pub const SHA256_RN_VIRTUAL_MAJ_I0_LOW_START: usize =
    SHA256_RN_VIRTUAL_BIG_SIGMA0_O2_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_BIG_SIGMA0_O2_ARITY;
pub const SHA256_RN_VIRTUAL_MAJ_I0_HIGH_0_START: usize =
    SHA256_RN_VIRTUAL_MAJ_I0_LOW_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_MAJ_I0_LOW_ARITY;
pub const SHA256_RN_VIRTUAL_MAJ_I0_HIGH_1_START: usize =
    SHA256_RN_VIRTUAL_MAJ_I0_HIGH_0_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_MAJ_I0_HIGH_0_ARITY;
pub const SHA256_RN_VIRTUAL_MAJ_I1_LOW_0_START: usize =
    SHA256_RN_VIRTUAL_MAJ_I0_HIGH_1_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_MAJ_I0_HIGH_1_ARITY;
pub const SHA256_RN_VIRTUAL_MAJ_I1_LOW_1_START: usize =
    SHA256_RN_VIRTUAL_MAJ_I1_LOW_0_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_MAJ_I1_LOW_0_ARITY;
pub const SHA256_RN_VIRTUAL_MAJ_I1_HIGH_START: usize =
    SHA256_RN_VIRTUAL_MAJ_I1_LOW_1_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_MAJ_I1_LOW_1_ARITY;
pub const NUM_SHA256_COMPRESS_RN_VIRTUAL_COLS: usize =
    SHA256_RN_VIRTUAL_MAJ_I1_HIGH_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_VIRTUAL_MAJ_I1_HIGH_ARITY;

pub const SHA256_RN_K: [u32; SHA256_RN_COMPRESS_ROUNDS] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
    0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8,
    0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
    0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
    0xc67178f2,
];

#[allow(non_snake_case)]
pub(super) mod Sigma0 {
    pub const I0_L: u32 = 0b1011010101010101;
    pub const I1_L: u32 = 0b0100101010101010;
    pub const I0_H: u32 = 0b0100101010101010;
    pub const I1_H: u32 = 0b1011010101010101;
    pub const O0_L: u32 = 0b0101000000101010;
    pub const O1_L: u32 = 0b1010100000010101;
    pub const O2: u32 = 0b00000111110000000000011111000000;
    pub const O0_H: u32 = 0b1010100000010101;
    pub const O1_H: u32 = 0b0101000000101010;
}

#[allow(non_snake_case)]
pub(super) mod Sigma1 {
    pub const I0_L: u32 = 0b1010100001010101;
    pub const I1_L: u32 = 0b0101011110101010;
    pub const I0_H: u32 = 0b1010101101010110;
    pub const I1_H: u32 = 0b0101010010101001;
    pub const O0_L: u32 = 0b1001010100101010;
    pub const O1_L: u32 = 0b0000101000010100;
    pub const O2: u32 = 0b10000001001000000110000011000001;
    pub const O0_H: u32 = 0b0101010000001010;
    pub const O1_H: u32 = 0b0010101011010101;
}

#[allow(non_snake_case)]
pub mod BigSigma0 {
    pub const I0_L: u32 = 0b0000111110000011;
    pub const I0_H0: u32 = 0b01111100;
    pub const I0_H1: u32 = 0b11110000;
    pub const I1_L0: u32 = 0b01111100;
    pub const I1_L1: u32 = 0b11110000;
    pub const I1_H: u32 = 0b0000111110000011;
    pub const O0_L: u32 = 0b0000001111000000;
    pub const O1_L: u32 = 0b0111000000011110;
    pub const O2: u32 = 0b10001100001000011000110000100001;
    pub const O0_H: u32 = 0b0111000000011110;
    pub const O1_H: u32 = 0b0000001111000000;
}

#[allow(non_snake_case)]
pub mod BigSigma1 {
    pub const I0: u32 = 0b10011000110001100110011000110001;
    pub const I1: u32 = 0b01100111001110011001100111001110;
    pub const I0_L: u32 = 0b0110011000110001;
    pub const I0_H: u32 = 0b1001100011000110;
    pub const I1_L: u32 = 0b1001100111001110;
    pub const I1_H: u32 = 0b0110011100111001;
    pub const O0_L: u32 = 0b0001100010001000;
    pub const O1_L: u32 = 0b1110011000100011;
    pub const O2: u32 = 0b10100101010100000000000101010100;
    pub const O0_H: u32 = 0b0100001000100011;
    pub const O1_H: u32 = 0b0001100010001100;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sha256RnSchedulingRoundWitness {
    pub w_15_i0_low: u32,
    pub w_15_i0_high: u32,
    pub sigma_0_o0_low: u32,
    pub sigma_0_o0_high: u32,
    pub sigma_0_o20_pext: u32,
    pub sigma_0_o1_low: u32,
    pub sigma_0_o1_high: u32,
    pub sigma_0_o21_pext: u32,
    pub sigma_0_o2_low: u32,
    pub sigma_0_o2_high: u32,
    pub w_2_i0_low: u32,
    pub w_2_i0_high: u32,
    pub sigma_1_o0_low: u32,
    pub sigma_1_o0_high: u32,
    pub sigma_1_o20_pext: u32,
    pub sigma_1_o1_low: u32,
    pub sigma_1_o1_high: u32,
    pub sigma_1_o21_pext: u32,
    pub sigma_1_o2_low: u32,
    pub sigma_1_o2_high: u32,
    pub carry_low: u32,
    pub carry_high: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sha256RnCompressionRoundWitness {
    pub e_i0_low: u32,
    pub e_i0_high: u32,
    pub sigma_1_o0_low: u32,
    pub sigma_1_o0_high: u32,
    pub sigma_1_o20_pext: u32,
    pub sigma_1_o1_low: u32,
    pub sigma_1_o1_high: u32,
    pub sigma_1_o21_pext: u32,
    pub sigma_1_o2_low: u32,
    pub sigma_1_o2_high: u32,
    pub f_i0_low: u32,
    pub f_i0_high: u32,
    pub ch_left_i0_low: u32,
    pub ch_left_i0_high: u32,
    pub ch_left_i1_low: u32,
    pub ch_left_i1_high: u32,
    pub g_i0_low: u32,
    pub g_i0_high: u32,
    pub ch_right_i0_low: u32,
    pub ch_right_i0_high: u32,
    pub ch_right_i1_low: u32,
    pub ch_right_i1_high: u32,
    pub a_i0_high_0: u32,
    pub a_i0_high_1: u32,
    pub a_i1_low_0: u32,
    pub a_i1_low_1: u32,
    pub sigma_0_o0_low: u32,
    pub sigma_0_o0_high: u32,
    pub sigma_0_o20_pext: u32,
    pub sigma_0_o1_low: u32,
    pub sigma_0_o1_high: u32,
    pub sigma_0_o21_pext: u32,
    pub sigma_0_o2_low: u32,
    pub sigma_0_o2_high: u32,
    pub b_i0_high_0: u32,
    pub b_i0_high_1: u32,
    pub b_i1_low_0: u32,
    pub b_i1_low_1: u32,
    pub c_i0_high_0: u32,
    pub c_i0_high_1: u32,
    pub c_i1_low_0: u32,
    pub c_i1_low_1: u32,
    pub maj_i0_low: u32,
    pub maj_i0_high_0: u32,
    pub maj_i0_high_1: u32,
    pub maj_i1_low_0: u32,
    pub maj_i1_low_1: u32,
    pub maj_i1_high: u32,
    pub e_carry_low: u32,
    pub e_carry_high: u32,
    pub a_carry_low: u32,
    pub a_carry_high: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sha256CompressRnWitness {
    pub h_in: [u32; SHA256_RN_WORDS],
    pub block: [u32; SHA256_RN_BLOCK_WORDS],
    pub w: [u32; SHA256_RN_COMPRESS_ROUNDS],
    pub scheduling: [Sha256RnSchedulingRoundWitness; SHA256_RN_SCHEDULE_EXTENSIONS],
    pub compression: [Sha256RnCompressionRoundWitness; SHA256_RN_COMPRESS_ROUNDS],
    pub h_out: [u32; SHA256_RN_WORDS],
    pub virtual_lookup_values: Vec<F>,
}

pub fn generate_sha256_compress_rn_witness(
    h_in: [u32; SHA256_RN_WORDS],
    block: [u32; SHA256_RN_BLOCK_WORDS],
) -> Sha256CompressRnWitness {
    const EMPTY_SCHED: Sha256RnSchedulingRoundWitness = Sha256RnSchedulingRoundWitness {
        w_15_i0_low: 0,
        w_15_i0_high: 0,
        sigma_0_o0_low: 0,
        sigma_0_o0_high: 0,
        sigma_0_o20_pext: 0,
        sigma_0_o1_low: 0,
        sigma_0_o1_high: 0,
        sigma_0_o21_pext: 0,
        sigma_0_o2_low: 0,
        sigma_0_o2_high: 0,
        w_2_i0_low: 0,
        w_2_i0_high: 0,
        sigma_1_o0_low: 0,
        sigma_1_o0_high: 0,
        sigma_1_o20_pext: 0,
        sigma_1_o1_low: 0,
        sigma_1_o1_high: 0,
        sigma_1_o21_pext: 0,
        sigma_1_o2_low: 0,
        sigma_1_o2_high: 0,
        carry_low: 0,
        carry_high: 0,
    };
    const EMPTY_COMP: Sha256RnCompressionRoundWitness = Sha256RnCompressionRoundWitness {
        e_i0_low: 0,
        e_i0_high: 0,
        sigma_1_o0_low: 0,
        sigma_1_o0_high: 0,
        sigma_1_o20_pext: 0,
        sigma_1_o1_low: 0,
        sigma_1_o1_high: 0,
        sigma_1_o21_pext: 0,
        sigma_1_o2_low: 0,
        sigma_1_o2_high: 0,
        f_i0_low: 0,
        f_i0_high: 0,
        ch_left_i0_low: 0,
        ch_left_i0_high: 0,
        ch_left_i1_low: 0,
        ch_left_i1_high: 0,
        g_i0_low: 0,
        g_i0_high: 0,
        ch_right_i0_low: 0,
        ch_right_i0_high: 0,
        ch_right_i1_low: 0,
        ch_right_i1_high: 0,
        a_i0_high_0: 0,
        a_i0_high_1: 0,
        a_i1_low_0: 0,
        a_i1_low_1: 0,
        sigma_0_o0_low: 0,
        sigma_0_o0_high: 0,
        sigma_0_o20_pext: 0,
        sigma_0_o1_low: 0,
        sigma_0_o1_high: 0,
        sigma_0_o21_pext: 0,
        sigma_0_o2_low: 0,
        sigma_0_o2_high: 0,
        b_i0_high_0: 0,
        b_i0_high_1: 0,
        b_i1_low_0: 0,
        b_i1_low_1: 0,
        c_i0_high_0: 0,
        c_i0_high_1: 0,
        c_i1_low_0: 0,
        c_i1_low_1: 0,
        maj_i0_low: 0,
        maj_i0_high_0: 0,
        maj_i0_high_1: 0,
        maj_i1_low_0: 0,
        maj_i1_low_1: 0,
        maj_i1_high: 0,
        e_carry_low: 0,
        e_carry_high: 0,
        a_carry_low: 0,
        a_carry_high: 0,
    };

    let mut w = [0u32; SHA256_RN_COMPRESS_ROUNDS];
    w[..SHA256_RN_BLOCK_WORDS].copy_from_slice(&block);
    let mut scheduling = [EMPTY_SCHED; SHA256_RN_SCHEDULE_EXTENSIONS];

    for t in SHA256_RN_BLOCK_WORDS..SHA256_RN_COMPRESS_ROUNDS {
        let [w_16_low, w_16_high] = u32_to_u16_limbs_u32(w[t - 16]);
        let [w_15_low, w_15_high] = u32_to_u16_limbs_u32(w[t - 15]);
        let [w_7_low, w_7_high] = u32_to_u16_limbs_u32(w[t - 7]);
        let [w_2_low, w_2_high] = u32_to_u16_limbs_u32(w[t - 2]);

        let w_15_i0_low = w_15_low & Sigma0::I0_L;
        let w_15_i0_high = w_15_high & Sigma0::I0_H;
        let sigma_0_i0 = small_sigma0(w_15_i0_low + (w_15_i0_high << BITS_PER_LIMB));
        let sigma_0_o0_low = sigma_0_i0 & Sigma0::O0_L;
        let sigma_0_o0_high = (sigma_0_i0 >> BITS_PER_LIMB) & Sigma0::O0_H;
        let sigma_0_o20 = sigma_0_i0 & Sigma0::O2;
        let sigma_0_o20_pext = pext_u32(sigma_0_o20, Sigma0::O2);

        let w_15_i1_low = w_15_low & Sigma0::I1_L;
        let w_15_i1_high = w_15_high & Sigma0::I1_H;
        let sigma_0_i1 = small_sigma0(w_15_i1_low + (w_15_i1_high << BITS_PER_LIMB));
        let sigma_0_o1_low = sigma_0_i1 & Sigma0::O1_L;
        let sigma_0_o1_high = (sigma_0_i1 >> BITS_PER_LIMB) & Sigma0::O1_H;
        let sigma_0_o21 = sigma_0_i1 & Sigma0::O2;
        let sigma_0_o21_pext = pext_u32(sigma_0_o21, Sigma0::O2);

        let sigma_0_o2 = sigma_0_o20 ^ sigma_0_o21;
        let sigma_0_o2_low = sigma_0_o2 & LIMB_MASK;
        let sigma_0_o2_high = sigma_0_o2 >> BITS_PER_LIMB;

        let w_2_i0_low = w_2_low & Sigma1::I0_L;
        let w_2_i0_high = w_2_high & Sigma1::I0_H;
        let sigma_1_i0 = small_sigma1(w_2_i0_low + (w_2_i0_high << BITS_PER_LIMB));
        let sigma_1_o0_low = sigma_1_i0 & Sigma1::O0_L;
        let sigma_1_o0_high = (sigma_1_i0 >> BITS_PER_LIMB) & Sigma1::O0_H;
        let sigma_1_o20 = sigma_1_i0 & Sigma1::O2;
        let sigma_1_o20_pext = pext_u32(sigma_1_o20, Sigma1::O2);

        let w_2_i1_low = w_2_low & Sigma1::I1_L;
        let w_2_i1_high = w_2_high & Sigma1::I1_H;
        let sigma_1_i1 = small_sigma1(w_2_i1_low + (w_2_i1_high << BITS_PER_LIMB));
        let sigma_1_o1_low = sigma_1_i1 & Sigma1::O1_L;
        let sigma_1_o1_high = (sigma_1_i1 >> BITS_PER_LIMB) & Sigma1::O1_H;
        let sigma_1_o21 = sigma_1_i1 & Sigma1::O2;
        let sigma_1_o21_pext = pext_u32(sigma_1_o21, Sigma1::O2);

        let sigma_1_o2 = sigma_1_o20 ^ sigma_1_o21;
        let sigma_1_o2_low = sigma_1_o2 & LIMB_MASK;
        let sigma_1_o2_high = sigma_1_o2 >> BITS_PER_LIMB;

        let sigma_0_low = sigma_0_o0_low + sigma_0_o1_low + sigma_0_o2_low;
        let sigma_0_high = sigma_0_o0_high + sigma_0_o1_high + sigma_0_o2_high;
        let sigma_1_low = sigma_1_o0_low + sigma_1_o1_low + sigma_1_o2_low;
        let sigma_1_high = sigma_1_o0_high + sigma_1_o1_high + sigma_1_o2_high;

        let round_low = w_16_low + sigma_0_low + w_7_low + sigma_1_low;
        let round_high = w_16_high + sigma_0_high + w_7_high + sigma_1_high;
        let carry_low = round_low >> BITS_PER_LIMB;
        let carry_high = (round_high + carry_low) >> BITS_PER_LIMB;
        let new_w_low = round_low - (carry_low << BITS_PER_LIMB);
        let new_w_high = round_high + carry_low - (carry_high << BITS_PER_LIMB);
        w[t] = u16_limb_u32s_to_u32([new_w_low, new_w_high]);

        scheduling[t - SHA256_RN_BLOCK_WORDS] = Sha256RnSchedulingRoundWitness {
            w_15_i0_low,
            w_15_i0_high,
            sigma_0_o0_low,
            sigma_0_o0_high,
            sigma_0_o20_pext,
            sigma_0_o1_low,
            sigma_0_o1_high,
            sigma_0_o21_pext,
            sigma_0_o2_low,
            sigma_0_o2_high,
            w_2_i0_low,
            w_2_i0_high,
            sigma_1_o0_low,
            sigma_1_o0_high,
            sigma_1_o20_pext,
            sigma_1_o1_low,
            sigma_1_o1_high,
            sigma_1_o21_pext,
            sigma_1_o2_low,
            sigma_1_o2_high,
            carry_low,
            carry_high,
        };
    }

    let mut compression = [EMPTY_COMP; SHA256_RN_COMPRESS_ROUNDS];
    let mut hash_buffer = words_to_limbs(h_in);
    let mut big_sigma0_i0 = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut big_sigma0_i1 = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut big_sigma0_o2 = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut big_sigma1_i0 = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut big_sigma1_i1 = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut big_sigma1_o2 = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut maj_i0_low_tuples = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut maj_i0_high_0_tuples = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut maj_i0_high_1_tuples = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut maj_i1_low_0_tuples = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut maj_i1_low_1_tuples = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);
    let mut maj_i1_high_tuples = Vec::with_capacity(SHA256_RN_COMPRESS_ROUNDS);

    for round in 0..SHA256_RN_COMPRESS_ROUNDS {
        let a_low = hash_buffer[0];
        let a_high = hash_buffer[1];
        let b_low = hash_buffer[2];
        let b_high = hash_buffer[3];
        let c_low = hash_buffer[4];
        let c_high = hash_buffer[5];
        let d_low = hash_buffer[6];
        let d_high = hash_buffer[7];
        let e_low = hash_buffer[8];
        let e_high = hash_buffer[9];
        let f_low = hash_buffer[10];
        let f_high = hash_buffer[11];
        let g_low = hash_buffer[12];
        let g_high = hash_buffer[13];
        let h_low = hash_buffer[14];
        let h_high = hash_buffer[15];

        let e_i0_low = e_low & BigSigma1::I0_L;
        let e_i0_high = e_high & BigSigma1::I0_H;
        let sigma_1_i0 = big_sigma1(e_i0_low + (e_i0_high << BITS_PER_LIMB));
        let sigma_1_o0_low = sigma_1_i0 & BigSigma1::O0_L;
        let sigma_1_o0_high = (sigma_1_i0 >> BITS_PER_LIMB) & BigSigma1::O0_H;
        let sigma_1_o20 = sigma_1_i0 & BigSigma1::O2;
        let sigma_1_o20_pext = pext_u32(sigma_1_o20, BigSigma1::O2);

        let e_i1_low = e_low & BigSigma1::I1_L;
        let e_i1_high = e_high & BigSigma1::I1_H;
        let sigma_1_i1 = big_sigma1(e_i1_low + (e_i1_high << BITS_PER_LIMB));
        let sigma_1_o1_low = sigma_1_i1 & BigSigma1::O1_L;
        let sigma_1_o1_high = (sigma_1_i1 >> BITS_PER_LIMB) & BigSigma1::O1_H;
        let sigma_1_o21 = sigma_1_i1 & BigSigma1::O2;
        let sigma_1_o21_pext = pext_u32(sigma_1_o21, BigSigma1::O2);

        let sigma_1_o2 = sigma_1_o20 ^ sigma_1_o21;
        let sigma_1_o2_low = sigma_1_o2 & LIMB_MASK;
        let sigma_1_o2_high = sigma_1_o2 >> BITS_PER_LIMB;
        let sigma_1_low = sigma_1_o0_low + sigma_1_o1_low + sigma_1_o2_low;
        let sigma_1_high = sigma_1_o0_high + sigma_1_o1_high + sigma_1_o2_high;

        big_sigma1_i0.push([
            F::from_u32(e_i0_low),
            F::from_u32(e_i0_high),
            F::from_u32(sigma_1_o0_low),
            F::from_u32(sigma_1_o0_high),
            F::from_u32(sigma_1_o20_pext),
        ]);
        big_sigma1_i1.push([
            F::from_u32(e_i1_low),
            F::from_u32(e_i1_high),
            F::from_u32(sigma_1_o1_low),
            F::from_u32(sigma_1_o1_high),
            F::from_u32(sigma_1_o21_pext),
        ]);
        big_sigma1_o2.push([
            F::from_u32(sigma_1_o20_pext),
            F::from_u32(sigma_1_o21_pext),
            F::from_u32(sigma_1_o2_low),
            F::from_u32(sigma_1_o2_high),
        ]);

        let f_i0_low = f_low & BigSigma1::I0_L;
        let f_i0_high = f_high & BigSigma1::I0_H;
        let f_i1_low = f_low & BigSigma1::I1_L;
        let f_i1_high = f_high & BigSigma1::I1_H;
        let ch_left_i0_low = e_i0_low & f_i0_low;
        let ch_left_i0_high = e_i0_high & f_i0_high;
        let ch_left_i1_low = e_i1_low & f_i1_low;
        let ch_left_i1_high = e_i1_high & f_i1_high;

        let g_i0_low = g_low & BigSigma1::I0_L;
        let g_i0_high = g_high & BigSigma1::I0_H;
        let g_i1_low = g_low & BigSigma1::I1_L;
        let g_i1_high = g_high & BigSigma1::I1_H;
        let ch_right_i0_low = (!e_i0_low) & g_i0_low;
        let ch_right_i0_high = (!e_i0_high) & g_i0_high;
        let ch_right_i1_low = (!e_i1_low) & g_i1_low;
        let ch_right_i1_high = (!e_i1_high) & g_i1_high;
        let ch_low = ch_left_i0_low + ch_left_i1_low + ch_right_i0_low + ch_right_i1_low;
        let ch_high = ch_left_i0_high + ch_left_i1_high + ch_right_i0_high + ch_right_i1_high;

        let a_i0_low = a_low & BigSigma0::I0_L;
        let a_i0_high_0 = a_high & BigSigma0::I0_H0;
        let a_i0_high_1 = (a_high >> 8) & BigSigma0::I0_H1;
        let sigma_0_i0 = big_sigma0(a_i0_low + (a_i0_high_0 << BITS_PER_LIMB) + (a_i0_high_1 << 24));
        let sigma_0_o0_low = sigma_0_i0 & BigSigma0::O0_L;
        let sigma_0_o0_high = (sigma_0_i0 >> BITS_PER_LIMB) & BigSigma0::O0_H;
        let sigma_0_o20 = sigma_0_i0 & BigSigma0::O2;
        let sigma_0_o20_pext = pext_u32(sigma_0_o20, BigSigma0::O2);

        let a_i1_low_0 = a_low & BigSigma0::I1_L0;
        let a_i1_low_1 = (a_low >> 8) & BigSigma0::I1_L1;
        let a_i1_high = a_high & BigSigma0::I1_H;
        let sigma_0_i1 = big_sigma0(a_i1_low_0 + (a_i1_low_1 << 8) + (a_i1_high << BITS_PER_LIMB));
        let sigma_0_o1_low = sigma_0_i1 & BigSigma0::O1_L;
        let sigma_0_o1_high = (sigma_0_i1 >> BITS_PER_LIMB) & BigSigma0::O1_H;
        let sigma_0_o21 = sigma_0_i1 & BigSigma0::O2;
        let sigma_0_o21_pext = pext_u32(sigma_0_o21, BigSigma0::O2);

        let sigma_0_o2 = sigma_0_o20 ^ sigma_0_o21;
        let sigma_0_o2_low = sigma_0_o2 & LIMB_MASK;
        let sigma_0_o2_high = sigma_0_o2 >> BITS_PER_LIMB;
        let sigma_0_low = sigma_0_o0_low + sigma_0_o1_low + sigma_0_o2_low;
        let sigma_0_high = sigma_0_o0_high + sigma_0_o1_high + sigma_0_o2_high;

        big_sigma0_i0.push([
            F::from_u32(a_i0_low),
            F::from_u32(a_i0_high_0),
            F::from_u32(a_i0_high_1),
            F::from_u32(sigma_0_o0_low),
            F::from_u32(sigma_0_o0_high),
            F::from_u32(sigma_0_o20_pext),
        ]);
        big_sigma0_i1.push([
            F::from_u32(a_i1_low_0),
            F::from_u32(a_i1_low_1),
            F::from_u32(a_i1_high),
            F::from_u32(sigma_0_o1_low),
            F::from_u32(sigma_0_o1_high),
            F::from_u32(sigma_0_o21_pext),
        ]);
        big_sigma0_o2.push([
            F::from_u32(sigma_0_o20_pext),
            F::from_u32(sigma_0_o21_pext),
            F::from_u32(sigma_0_o2_low),
            F::from_u32(sigma_0_o2_high),
        ]);

        let b_i0_low = b_low & BigSigma0::I0_L;
        let b_i0_high_0 = b_high & BigSigma0::I0_H0;
        let b_i0_high_1 = (b_high >> 8) & BigSigma0::I0_H1;
        let b_i1_low_0 = b_low & BigSigma0::I1_L0;
        let b_i1_low_1 = (b_low >> 8) & BigSigma0::I1_L1;
        let b_i1_high = b_high & BigSigma0::I1_H;
        let c_i0_low = c_low & BigSigma0::I0_L;
        let c_i0_high_0 = c_high & BigSigma0::I0_H0;
        let c_i0_high_1 = (c_high >> 8) & BigSigma0::I0_H1;
        let c_i1_low_0 = c_low & BigSigma0::I1_L0;
        let c_i1_low_1 = (c_low >> 8) & BigSigma0::I1_L1;
        let c_i1_high = c_high & BigSigma0::I1_H;
        let maj_i0_low = maj(a_i0_low, b_i0_low, c_i0_low);
        let maj_i0_high_0 = maj(a_i0_high_0, b_i0_high_0, c_i0_high_0);
        let maj_i0_high_1 = maj(a_i0_high_1, b_i0_high_1, c_i0_high_1);
        let maj_i1_low_0 = maj(a_i1_low_0, b_i1_low_0, c_i1_low_0);
        let maj_i1_low_1 = maj(a_i1_low_1, b_i1_low_1, c_i1_low_1);
        let maj_i1_high = maj(a_i1_high, b_i1_high, c_i1_high);
        maj_i0_low_tuples.push([
            F::from_u32(a_i0_low),
            F::from_u32(b_i0_low),
            F::from_u32(c_i0_low),
            F::from_u32(maj_i0_low),
        ]);
        maj_i0_high_0_tuples.push([
            F::from_u32(a_i0_high_0),
            F::from_u32(b_i0_high_0),
            F::from_u32(c_i0_high_0),
            F::from_u32(maj_i0_high_0),
        ]);
        maj_i0_high_1_tuples.push([
            F::from_u32(a_i0_high_1),
            F::from_u32(b_i0_high_1),
            F::from_u32(c_i0_high_1),
            F::from_u32(maj_i0_high_1),
        ]);
        maj_i1_low_0_tuples.push([
            F::from_u32(a_i1_low_0),
            F::from_u32(b_i1_low_0),
            F::from_u32(c_i1_low_0),
            F::from_u32(maj_i1_low_0),
        ]);
        maj_i1_low_1_tuples.push([
            F::from_u32(a_i1_low_1),
            F::from_u32(b_i1_low_1),
            F::from_u32(c_i1_low_1),
            F::from_u32(maj_i1_low_1),
        ]);
        maj_i1_high_tuples.push([
            F::from_u32(a_i1_high),
            F::from_u32(b_i1_high),
            F::from_u32(c_i1_high),
            F::from_u32(maj_i1_high),
        ]);
        let maj_low = maj_i0_low + maj_i1_low_0 + (maj_i1_low_1 << 8);
        let maj_high = maj_i0_high_0 + (maj_i0_high_1 << 8) + maj_i1_high;

        let [w_low, w_high] = u32_to_u16_limbs_u32(w[round]);
        let k_low = SHA256_RN_K[round] & LIMB_MASK;
        let k_high = SHA256_RN_K[round] >> BITS_PER_LIMB;
        let temp1_low = h_low + sigma_1_low + ch_low + k_low + w_low;
        let temp1_high = h_high + sigma_1_high + ch_high + k_high + w_high;
        let temp2_low = sigma_0_low + maj_low;
        let temp2_high = sigma_0_high + maj_high;

        let e_carry_low = (temp1_low + d_low) >> BITS_PER_LIMB;
        let e_carry_high = (temp1_high + d_high + e_carry_low) >> BITS_PER_LIMB;
        let new_e_low = temp1_low + d_low - (e_carry_low << BITS_PER_LIMB);
        let new_e_high = temp1_high + d_high + e_carry_low - (e_carry_high << BITS_PER_LIMB);
        let a_carry_low = (temp1_low + temp2_low) >> BITS_PER_LIMB;
        let a_carry_high = (temp1_high + temp2_high + a_carry_low) >> BITS_PER_LIMB;
        let new_a_low = temp1_low + temp2_low - (a_carry_low << BITS_PER_LIMB);
        let new_a_high = temp1_high + temp2_high + a_carry_low - (a_carry_high << BITS_PER_LIMB);

        compression[round] = Sha256RnCompressionRoundWitness {
            e_i0_low,
            e_i0_high,
            sigma_1_o0_low,
            sigma_1_o0_high,
            sigma_1_o20_pext,
            sigma_1_o1_low,
            sigma_1_o1_high,
            sigma_1_o21_pext,
            sigma_1_o2_low,
            sigma_1_o2_high,
            f_i0_low,
            f_i0_high,
            ch_left_i0_low,
            ch_left_i0_high,
            ch_left_i1_low,
            ch_left_i1_high,
            g_i0_low,
            g_i0_high,
            ch_right_i0_low,
            ch_right_i0_high,
            ch_right_i1_low,
            ch_right_i1_high,
            a_i0_high_0,
            a_i0_high_1,
            a_i1_low_0,
            a_i1_low_1,
            sigma_0_o0_low,
            sigma_0_o0_high,
            sigma_0_o20_pext,
            sigma_0_o1_low,
            sigma_0_o1_high,
            sigma_0_o21_pext,
            sigma_0_o2_low,
            sigma_0_o2_high,
            b_i0_high_0,
            b_i0_high_1,
            b_i1_low_0,
            b_i1_low_1,
            c_i0_high_0,
            c_i0_high_1,
            c_i1_low_0,
            c_i1_low_1,
            maj_i0_low,
            maj_i0_high_0,
            maj_i0_high_1,
            maj_i1_low_0,
            maj_i1_low_1,
            maj_i1_high,
            e_carry_low,
            e_carry_high,
            a_carry_low,
            a_carry_high,
        };

        hash_buffer = [
            new_a_low, new_a_high, a_low, a_high, b_low, b_high, c_low, c_high, new_e_low, new_e_high, e_low, e_high,
            f_low, f_high, g_low, g_high,
        ];
    }

    let final_state = limbs_to_words(hash_buffer);
    let h_out = core::array::from_fn(|i| h_in[i].wrapping_add(final_state[i]));
    let mut virtual_lookup_values = Vec::with_capacity(NUM_SHA256_COMPRESS_RN_VIRTUAL_COLS);
    for tuple in &big_sigma1_i0 {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &big_sigma1_i1 {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &big_sigma1_o2 {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &big_sigma0_i0 {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &big_sigma0_i1 {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &big_sigma0_o2 {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &maj_i0_low_tuples {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &maj_i0_high_0_tuples {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &maj_i0_high_1_tuples {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &maj_i1_low_0_tuples {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &maj_i1_low_1_tuples {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    for tuple in &maj_i1_high_tuples {
        virtual_lookup_values.extend_from_slice(tuple);
    }
    debug_assert_eq!(virtual_lookup_values.len(), NUM_SHA256_COMPRESS_RN_VIRTUAL_COLS);

    Sha256CompressRnWitness {
        h_in,
        block,
        w,
        scheduling,
        compression,
        h_out,
        virtual_lookup_values,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sha256CompressRnPrecompile<const BUS: bool>;

impl<const BUS: bool> crate::TableT for Sha256CompressRnPrecompile<BUS> {
    fn name(&self) -> &'static str {
        SHA256_COMPRESS_RN_NAME
    }

    fn table(&self) -> Table {
        Table::sha256_compress_rn()
    }

    fn lookups(&self) -> Vec<crate::LookupIntoMemory> {
        vec![
            crate::LookupIntoMemory {
                index: SHA256_RN_COL_STATE_PTR,
                values: (SHA256_RN_COL_STATE_LIMBS_START..SHA256_RN_COL_STATE_LIMBS_START + SHA256_RN_STATE_LIMBS)
                    .collect(),
            },
            crate::LookupIntoMemory {
                index: SHA256_RN_COL_BLOCK_PTR,
                values: (SHA256_RN_COL_W_START..SHA256_RN_COL_W_START + SHA256_RN_BLOCK_LIMBS).collect(),
            },
            crate::LookupIntoMemory {
                index: SHA256_RN_COL_OUT_PTR,
                values: (SHA256_RN_COL_OUT_LIMBS_START..SHA256_RN_COL_OUT_LIMBS_START + SHA256_RN_STATE_LIMBS)
                    .collect(),
            },
        ]
    }

    fn bus(&self) -> crate::Bus {
        crate::Bus {
            direction: crate::BusDirection::Pull,
            selector: SHA256_RN_COL_FLAG,
            data: vec![
                crate::BusData::Constant(SHA256_RN_PRECOMPILE_DATA),
                crate::BusData::Column(SHA256_RN_COL_STATE_PTR),
                crate::BusData::Column(SHA256_RN_COL_BLOCK_PTR),
                crate::BusData::Column(SHA256_RN_COL_OUT_PTR),
            ],
        }
    }

    fn padding_row(&self, padding: &crate::PaddingMemory) -> Vec<F> {
        sha256_compress_rn_trace_row(
            F::ZERO,
            F::from_usize(padding.sha256_state_ptr),
            F::from_usize(padding.sha256_block_ptr),
            F::from_usize(padding.sha256_out_ptr),
            crate::SHA256_IV,
            crate::SHA256_ZERO_BLOCK,
        )
    }

    fn virtual_padding_row(&self, _padding: &crate::PaddingMemory) -> Vec<F> {
        generate_sha256_compress_rn_witness(crate::SHA256_IV, crate::SHA256_ZERO_BLOCK).virtual_lookup_values
    }

    fn n_virtual_columns(&self) -> usize {
        NUM_SHA256_COMPRESS_RN_VIRTUAL_COLS
    }

    fn execute<M: crate::MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut crate::InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let PrecompileCompTimeArgs::Sha256CompressRn = args else {
            unreachable!("Sha256CompressRn table called with non-Sha256CompressRn args");
        };

        let state_ptr = arg_a.to_usize();
        let block_ptr = arg_b.to_usize();
        let out_ptr = arg_c.to_usize();

        let h_in = field_limbs_to_words::<SHA256_RN_WORDS>(&ctx.memory.get_slice(state_ptr, SHA256_RN_STATE_LIMBS)?)?;
        let block =
            field_limbs_to_words::<SHA256_RN_BLOCK_WORDS>(&ctx.memory.get_slice(block_ptr, SHA256_RN_BLOCK_LIMBS)?)?;
        let witness = generate_sha256_compress_rn_witness(h_in, block);
        ctx.memory.set_slice(out_ptr, &words_to_field_limbs_le(witness.h_out))?;

        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        push_sha256_compress_rn_trace_row_from_witness(trace, F::ONE, arg_a, arg_b, arg_c, &witness);
        debug_assert_eq!(trace.virtual_columns.len(), NUM_SHA256_COMPRESS_RN_VIRTUAL_COLS);
        for (column, value) in trace.virtual_columns.iter_mut().zip(witness.virtual_lookup_values) {
            column.push(value);
        }

        Ok(())
    }
}

fn field_limbs_to_words<const N: usize>(limbs: &[F]) -> Result<[u32; N], RunnerError> {
    assert_eq!(limbs.len(), N * SHA256_RN_U32_LIMBS);
    let mut words = [0u32; N];
    for (word, limb_pair) in words.iter_mut().zip(limbs.chunks_exact(SHA256_RN_U32_LIMBS)) {
        let lo = limb_to_u16(limb_pair[0])?;
        let hi = limb_to_u16(limb_pair[1])?;
        *word = u16_limb_u32s_to_u32([u32::from(lo), u32::from(hi)]);
    }
    Ok(words)
}

fn limb_to_u16(limb: F) -> Result<u16, RunnerError> {
    let value = limb.as_canonical_u32();
    u16::try_from(value).map_err(|_| RunnerError::InvalidSha256Input)
}

fn words_to_field_limbs_le<const N: usize>(words: [u32; N]) -> Vec<F> {
    words
        .into_iter()
        .flat_map(u32_to_u16_limbs_u32)
        .map(|limb| F::from_usize(limb as usize))
        .collect()
}

#[inline]
pub(super) const fn u32_to_u16_limbs_u32(word: u32) -> [u32; SHA256_RN_U32_LIMBS] {
    [word & LIMB_MASK, word >> BITS_PER_LIMB]
}

#[inline]
const fn u16_limb_u32s_to_u32(limbs: [u32; SHA256_RN_U32_LIMBS]) -> u32 {
    limbs[0] | (limbs[1] << BITS_PER_LIMB)
}

#[inline]
fn words_to_limbs(words: [u32; SHA256_RN_WORDS]) -> [u32; SHA256_RN_STATE_LIMBS] {
    let mut limbs = [0u32; SHA256_RN_STATE_LIMBS];
    for (i, word) in words.into_iter().enumerate() {
        let [low, high] = u32_to_u16_limbs_u32(word);
        limbs[2 * i] = low;
        limbs[2 * i + 1] = high;
    }
    limbs
}

#[inline]
fn limbs_to_words(limbs: [u32; SHA256_RN_STATE_LIMBS]) -> [u32; SHA256_RN_WORDS] {
    core::array::from_fn(|i| u16_limb_u32s_to_u32([limbs[2 * i], limbs[2 * i + 1]]))
}

#[inline]
const fn small_sigma0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}

#[inline]
const fn small_sigma1(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}

#[inline]
pub const fn big_sigma0(x: u32) -> u32 {
    x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
}

#[inline]
pub const fn big_sigma1(x: u32) -> u32 {
    x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
}

#[inline]
const fn maj(a: u32, b: u32, c: u32) -> u32 {
    (a & b) ^ (a & c) ^ (b & c)
}

#[inline]
pub const fn pext_u32(x: u32, mut mask: u32) -> u32 {
    let mut out = 0u32;
    let mut bit = 1u32;
    while mask != 0 {
        let lowest = mask & mask.wrapping_neg();
        if x & lowest != 0 {
            out |= bit;
        }
        mask ^= lowest;
        bit <<= 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::{
        Air, PrimeCharacteristicRing, PrimeField32, SumcheckComputation, get_symbolic_constraints_and_bus_data_values,
    };
    use core::borrow::Borrow;
    use std::collections::BTreeMap;

    use crate::{
        EF, ExtraDataForBuses, InstructionContext, InstructionCounts, Memory, MemoryAccess, SHA256_ABC_BLOCK,
        SHA256_BLOCK_WORDS, SHA256_IV, SHA256_STATE_WORDS, SHA256_ZERO_BLOCK, TableT, TableTrace,
        sha256_compress_words, words_to_field_limbs_le as baseline_words_to_field_limbs_le,
    };

    fn words_to_hex(words: [u32; SHA256_RN_WORDS]) -> String {
        words.iter().map(|word| format!("{word:08x}")).collect()
    }

    fn extract_packed_words(limbs: &[[F; SHA256_RN_U32_LIMBS]; SHA256_RN_WORDS]) -> [u32; SHA256_RN_WORDS] {
        core::array::from_fn(|i| {
            let lo = limbs[i][0].as_canonical_u32();
            let hi = limbs[i][1].as_canonical_u32();
            lo | (hi << BITS_PER_LIMB)
        })
    }

    fn extract_trace_output(row: &[F]) -> [u32; SHA256_RN_WORDS] {
        let cols: &Sha256CompressRnCols<F> = row.borrow();
        extract_packed_words(&cols.sha.h_out)
    }

    fn air_extra_data(n_constraints: usize) -> ExtraDataForBuses<EF> {
        let mut powers = Vec::with_capacity(n_constraints + 1);
        let alpha = EF::from(F::from_usize(7));
        let mut current = EF::ONE;
        for _ in 0..=n_constraints {
            powers.push(current);
            current *= alpha;
        }
        ExtraDataForBuses::new(Vec::new(), EF::ZERO, powers)
    }

    #[test]
    fn sha256_compress_rn_column_and_constraint_counts_match_plan() {
        assert_eq!(NUM_SHA256_RN_AIR_COLS, 4544);
        assert_eq!(NUM_SHA256_COMPRESS_RN_COLS, 4548);
        assert_eq!(SHA256_RN_COL_AIR_START, 4);
        assert_eq!(SHA256_RN_COL_STATE_LIMBS_START, 4);
        assert_eq!(SHA256_RN_COL_W_START, 20);
        assert_eq!(SHA256_RN_COL_OUT_LIMBS_START, 4532);

        let table = Sha256CompressRnPrecompile::<false>;
        let (constraints, bus_flag, bus_data) = get_symbolic_constraints_and_bus_data_values::<F, _>(&table);
        assert_eq!(constraints.len(), table.n_constraints());
        assert_eq!(table.n_constraints(), 113);
        assert_eq!(
            bus_flag,
            backend::SymbolicExpression::Variable(backend::SymbolicVariable::new(SHA256_RN_COL_FLAG))
        );
        assert_eq!(bus_data.len(), 4);
    }

    #[test]
    fn sha256_compress_rn_matches_existing_compress_outputs() {
        let cases: [([u32; SHA256_STATE_WORDS], [u32; SHA256_BLOCK_WORDS]); 3] = [
            (SHA256_IV, SHA256_ABC_BLOCK),
            (SHA256_IV, SHA256_ZERO_BLOCK),
            (
                [
                    0x0123_4567,
                    0x89ab_cdef,
                    0xfedc_ba98,
                    0x7654_3210,
                    0x0f1e_2d3c,
                    0x4b5a_6978,
                    0x8877_6655,
                    0x4433_2211,
                ],
                [
                    0xffff_ffff,
                    0,
                    0x1357_9bdf,
                    0x2468_ace0,
                    0xdead_beef,
                    0xcafe_babe,
                    0x0001_0002,
                    0x0003_0004,
                    0x0102_0304,
                    0x1111_2222,
                    0x3333_4444,
                    0x5555_6666,
                    0x7777_8888,
                    0x9999_aaaa,
                    0xbbbb_cccc,
                    0xdddd_eeee,
                ],
            ),
        ];

        for (h_in, block) in cases {
            let row = sha256_compress_rn_trace_row(F::ONE, F::ZERO, F::ZERO, F::ZERO, h_in, block);
            assert_eq!(extract_trace_output(&row), sha256_compress_words(h_in, block));
        }
    }

    #[test]
    fn sha256_compress_rn_generated_trace_satisfies_residual_air() {
        let table = Sha256CompressRnPrecompile::<false>;
        let extra_data = air_extra_data(table.n_constraints());
        let row = sha256_compress_rn_trace_row(
            F::ONE,
            F::from_usize(10),
            F::from_usize(20),
            F::from_usize(30),
            SHA256_IV,
            SHA256_ABC_BLOCK,
        );

        assert_eq!(
            <Sha256CompressRnPrecompile<false> as SumcheckComputation<EF>>::eval_base(&table, &row, &extra_data),
            EF::ZERO
        );

        let mut tampered_output = row.clone();
        tampered_output[SHA256_RN_COL_OUT_LIMBS_START] += F::ONE;
        assert_ne!(
            <Sha256CompressRnPrecompile<false> as SumcheckComputation<EF>>::eval_base(
                &table,
                &tampered_output,
                &extra_data
            ),
            EF::ZERO
        );

        let mut tampered_lookup_only = row;
        let first_scheduling_lookup_only = SHA256_RN_COL_W_START + SHA256_RN_COMPRESS_ROUNDS * SHA256_RN_U32_LIMBS;
        tampered_lookup_only[first_scheduling_lookup_only] += F::ONE;
        assert_eq!(
            <Sha256CompressRnPrecompile<false> as SumcheckComputation<EF>>::eval_base(
                &table,
                &tampered_lookup_only,
                &extra_data
            ),
            EF::ZERO,
            "lookup-backed witness columns are intentionally unchecked in this experiment"
        );
    }

    #[test]
    fn sha256_compress_rn_execute_writes_output_and_trace_row() {
        let state_ptr = 0;
        let block_ptr = SHA256_RN_STATE_LIMBS;
        let out_ptr = SHA256_RN_STATE_LIMBS + SHA256_RN_BLOCK_LIMBS;

        let mut memory = Memory::new(vec![]);
        memory
            .set_slice(state_ptr, &baseline_words_to_field_limbs_le(SHA256_IV))
            .unwrap();
        memory
            .set_slice(block_ptr, &baseline_words_to_field_limbs_le(SHA256_ABC_BLOCK))
            .unwrap();

        let table = Table::sha256_compress_rn();
        let mut traces = BTreeMap::new();
        traces.insert(table, TableTrace::new(&Sha256CompressRnPrecompile::<true>));
        let mut fp = 0;
        let mut pc = 0;
        let pcs = vec![0];
        let mut counts = InstructionCounts::default();
        let mut ctx = InstructionContext {
            memory: &mut memory,
            fp: &mut fp,
            pc: &mut pc,
            pcs: &pcs,
            traces: &mut traces,
            counts: &mut counts,
        };

        table
            .execute(
                F::from_usize(state_ptr),
                F::from_usize(block_ptr),
                F::from_usize(out_ptr),
                PrecompileCompTimeArgs::Sha256CompressRn,
                &mut ctx,
            )
            .unwrap();

        let out = ctx.memory.get_slice(out_ptr, SHA256_RN_STATE_LIMBS).unwrap();
        let out_words = field_limbs_to_words::<SHA256_RN_WORDS>(&out).unwrap();
        assert_eq!(
            words_to_hex(out_words),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );

        let trace = ctx.traces.get(&table).unwrap();
        assert_eq!(trace.columns.len(), NUM_SHA256_COMPRESS_RN_COLS);
        assert_eq!(trace.columns[SHA256_RN_COL_FLAG], [F::ONE]);
        assert_eq!(trace.columns[SHA256_RN_COL_STATE_PTR], [F::from_usize(state_ptr)]);
        assert_eq!(trace.columns[SHA256_RN_COL_BLOCK_PTR], [F::from_usize(block_ptr)]);
        assert_eq!(trace.columns[SHA256_RN_COL_OUT_PTR], [F::from_usize(out_ptr)]);
        assert_eq!(trace.virtual_columns.len(), NUM_SHA256_COMPRESS_RN_VIRTUAL_COLS);
        assert!(trace.virtual_columns.iter().all(|column| column.len() == 1));
    }
}
