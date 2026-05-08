use core::borrow::BorrowMut;

use backend::PrimeCharacteristicRing;

use crate::{F, TableTrace};

use super::{
    NUM_SHA256_COMPRESS_RN_COLS, SHA256_RN_COMPRESS_ROUNDS, SHA256_RN_SCHEDULE_EXTENSIONS, SHA256_RN_U32_LIMBS,
    SHA256_RN_WORDS, Sha256CompressRnCols, Sha256CompressRnWitness, Sha256RnCols, Sha256RnCompressionRoundCols,
    Sha256RnSchedulingRoundCols, generate_sha256_compress_rn_witness, u32_to_u16_limbs_u32,
};

pub fn sha256_compress_rn_trace_row(
    flag: F,
    state_ptr: F,
    block_ptr: F,
    out_ptr: F,
    h_in: [u32; SHA256_RN_WORDS],
    block: [u32; super::SHA256_RN_BLOCK_WORDS],
) -> Vec<F> {
    let witness = generate_sha256_compress_rn_witness(h_in, block);
    sha256_compress_rn_trace_row_from_witness(flag, state_ptr, block_ptr, out_ptr, &witness)
}

pub fn sha256_compress_rn_trace_row_from_witness(
    flag: F,
    state_ptr: F,
    block_ptr: F,
    out_ptr: F,
    witness: &Sha256CompressRnWitness,
) -> Vec<F> {
    let mut row = F::zero_vec(NUM_SHA256_COMPRESS_RN_COLS);
    let cols: &mut Sha256CompressRnCols<F> = row.as_mut_slice().borrow_mut();
    fill_sha256_compress_rn_cols(cols, flag, state_ptr, block_ptr, out_ptr, witness);
    row
}

pub fn push_sha256_compress_rn_trace_row_from_witness(
    trace: &mut TableTrace,
    flag: F,
    state_ptr: F,
    block_ptr: F,
    out_ptr: F,
    witness: &Sha256CompressRnWitness,
) {
    let row = sha256_compress_rn_trace_row_from_witness(flag, state_ptr, block_ptr, out_ptr, witness);
    debug_assert_eq!(trace.columns.len(), row.len());
    for (column, value) in trace.columns.iter_mut().zip(row) {
        column.push(value);
    }
}

pub fn fill_sha256_compress_rn_cols(
    cols: &mut Sha256CompressRnCols<F>,
    flag: F,
    state_ptr: F,
    block_ptr: F,
    out_ptr: F,
    witness: &Sha256CompressRnWitness,
) {
    cols.flag = flag;
    cols.state_ptr = state_ptr;
    cols.block_ptr = block_ptr;
    cols.out_ptr = out_ptr;
    fill_sha256_rn_cols(&mut cols.sha, witness);
}

pub fn fill_sha256_rn_cols(cols: &mut Sha256RnCols<F>, witness: &Sha256CompressRnWitness) {
    for i in 0..SHA256_RN_WORDS {
        cols.h_in[i] = word_limbs(witness.h_in[i]);
        cols.h_out[i] = word_limbs(witness.h_out[i]);
    }

    for i in 0..SHA256_RN_COMPRESS_ROUNDS {
        cols.w[i] = word_limbs(witness.w[i]);
        cols.compression[i] = Sha256RnCompressionRoundCols {
            e_i0_low: F::from_u32(witness.compression[i].e_i0_low),
            e_i0_high: F::from_u32(witness.compression[i].e_i0_high),
            sigma_1_o0_low: F::from_u32(witness.compression[i].sigma_1_o0_low),
            sigma_1_o0_high: F::from_u32(witness.compression[i].sigma_1_o0_high),
            sigma_1_o20_pext: F::from_u32(witness.compression[i].sigma_1_o20_pext),
            sigma_1_o1_low: F::from_u32(witness.compression[i].sigma_1_o1_low),
            sigma_1_o1_high: F::from_u32(witness.compression[i].sigma_1_o1_high),
            sigma_1_o21_pext: F::from_u32(witness.compression[i].sigma_1_o21_pext),
            sigma_1_o2_low: F::from_u32(witness.compression[i].sigma_1_o2_low),
            sigma_1_o2_high: F::from_u32(witness.compression[i].sigma_1_o2_high),
            f_i0_low: F::from_u32(witness.compression[i].f_i0_low),
            f_i0_high: F::from_u32(witness.compression[i].f_i0_high),
            ch_left_i0_low: F::from_u32(witness.compression[i].ch_left_i0_low),
            ch_left_i0_high: F::from_u32(witness.compression[i].ch_left_i0_high),
            ch_left_i1_low: F::from_u32(witness.compression[i].ch_left_i1_low),
            ch_left_i1_high: F::from_u32(witness.compression[i].ch_left_i1_high),
            g_i0_low: F::from_u32(witness.compression[i].g_i0_low),
            g_i0_high: F::from_u32(witness.compression[i].g_i0_high),
            ch_right_i0_low: F::from_u32(witness.compression[i].ch_right_i0_low),
            ch_right_i0_high: F::from_u32(witness.compression[i].ch_right_i0_high),
            ch_right_i1_low: F::from_u32(witness.compression[i].ch_right_i1_low),
            ch_right_i1_high: F::from_u32(witness.compression[i].ch_right_i1_high),
            a_i0_high_0: F::from_u32(witness.compression[i].a_i0_high_0),
            a_i0_high_1: F::from_u32(witness.compression[i].a_i0_high_1),
            a_i1_low_0: F::from_u32(witness.compression[i].a_i1_low_0),
            a_i1_low_1: F::from_u32(witness.compression[i].a_i1_low_1),
            sigma_0_o0_low: F::from_u32(witness.compression[i].sigma_0_o0_low),
            sigma_0_o0_high: F::from_u32(witness.compression[i].sigma_0_o0_high),
            sigma_0_o20_pext: F::from_u32(witness.compression[i].sigma_0_o20_pext),
            sigma_0_o1_low: F::from_u32(witness.compression[i].sigma_0_o1_low),
            sigma_0_o1_high: F::from_u32(witness.compression[i].sigma_0_o1_high),
            sigma_0_o21_pext: F::from_u32(witness.compression[i].sigma_0_o21_pext),
            sigma_0_o2_low: F::from_u32(witness.compression[i].sigma_0_o2_low),
            sigma_0_o2_high: F::from_u32(witness.compression[i].sigma_0_o2_high),
            b_i0_high_0: F::from_u32(witness.compression[i].b_i0_high_0),
            b_i0_high_1: F::from_u32(witness.compression[i].b_i0_high_1),
            b_i1_low_0: F::from_u32(witness.compression[i].b_i1_low_0),
            b_i1_low_1: F::from_u32(witness.compression[i].b_i1_low_1),
            c_i0_high_0: F::from_u32(witness.compression[i].c_i0_high_0),
            c_i0_high_1: F::from_u32(witness.compression[i].c_i0_high_1),
            c_i1_low_0: F::from_u32(witness.compression[i].c_i1_low_0),
            c_i1_low_1: F::from_u32(witness.compression[i].c_i1_low_1),
            maj_i0_low: F::from_u32(witness.compression[i].maj_i0_low),
            maj_i0_high_0: F::from_u32(witness.compression[i].maj_i0_high_0),
            maj_i0_high_1: F::from_u32(witness.compression[i].maj_i0_high_1),
            maj_i1_low_0: F::from_u32(witness.compression[i].maj_i1_low_0),
            maj_i1_low_1: F::from_u32(witness.compression[i].maj_i1_low_1),
            maj_i1_high: F::from_u32(witness.compression[i].maj_i1_high),
            e_carry_low: F::from_u32(witness.compression[i].e_carry_low),
            e_carry_high: F::from_u32(witness.compression[i].e_carry_high),
            a_carry_low: F::from_u32(witness.compression[i].a_carry_low),
            a_carry_high: F::from_u32(witness.compression[i].a_carry_high),
        };
    }

    for i in 0..SHA256_RN_SCHEDULE_EXTENSIONS {
        cols.scheduling[i] = Sha256RnSchedulingRoundCols {
            w_15_i0_low: F::from_u32(witness.scheduling[i].w_15_i0_low),
            w_15_i0_high: F::from_u32(witness.scheduling[i].w_15_i0_high),
            sigma_0_o0_low: F::from_u32(witness.scheduling[i].sigma_0_o0_low),
            sigma_0_o0_high: F::from_u32(witness.scheduling[i].sigma_0_o0_high),
            sigma_0_o20_pext: F::from_u32(witness.scheduling[i].sigma_0_o20_pext),
            sigma_0_o1_low: F::from_u32(witness.scheduling[i].sigma_0_o1_low),
            sigma_0_o1_high: F::from_u32(witness.scheduling[i].sigma_0_o1_high),
            sigma_0_o21_pext: F::from_u32(witness.scheduling[i].sigma_0_o21_pext),
            sigma_0_o2_low: F::from_u32(witness.scheduling[i].sigma_0_o2_low),
            sigma_0_o2_high: F::from_u32(witness.scheduling[i].sigma_0_o2_high),
            w_2_i0_low: F::from_u32(witness.scheduling[i].w_2_i0_low),
            w_2_i0_high: F::from_u32(witness.scheduling[i].w_2_i0_high),
            sigma_1_o0_low: F::from_u32(witness.scheduling[i].sigma_1_o0_low),
            sigma_1_o0_high: F::from_u32(witness.scheduling[i].sigma_1_o0_high),
            sigma_1_o20_pext: F::from_u32(witness.scheduling[i].sigma_1_o20_pext),
            sigma_1_o1_low: F::from_u32(witness.scheduling[i].sigma_1_o1_low),
            sigma_1_o1_high: F::from_u32(witness.scheduling[i].sigma_1_o1_high),
            sigma_1_o21_pext: F::from_u32(witness.scheduling[i].sigma_1_o21_pext),
            sigma_1_o2_low: F::from_u32(witness.scheduling[i].sigma_1_o2_low),
            sigma_1_o2_high: F::from_u32(witness.scheduling[i].sigma_1_o2_high),
            carry_low: F::from_u32(witness.scheduling[i].carry_low),
            carry_high: F::from_u32(witness.scheduling[i].carry_high),
        };
    }
}

fn word_limbs(word: u32) -> [F; SHA256_RN_U32_LIMBS] {
    u32_to_u16_limbs_u32(word).map(F::from_u32)
}
