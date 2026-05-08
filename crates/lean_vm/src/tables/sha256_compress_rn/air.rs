use backend::*;

use super::{
    BITS_PER_LIMB, NUM_SHA256_COMPRESS_RN_COLS, SHA256_RN_BLOCK_WORDS, SHA256_RN_COMPRESS_ROUNDS, SHA256_RN_K,
    SHA256_RN_PRECOMPILE_DATA, SHA256_RN_SCHEDULE_EXTENSIONS, SHA256_RN_U32_LIMBS, SHA256_RN_WORDS,
    Sha256CompressRnCols, Sha256CompressRnPrecompile, Sha256RnCols,
};
use crate::{EF, ExtraDataForBuses, eval_virtual_bus_column};

impl<const BUS: bool> Air for Sha256CompressRnPrecompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        NUM_SHA256_COMPRESS_RN_COLS
    }

    fn degree_air(&self) -> usize {
        2
    }

    fn n_constraints(&self) -> usize {
        1 + SHA256_RN_SCHEDULE_EXTENSIONS * SHA256_RN_U32_LIMBS + SHA256_RN_WORDS * SHA256_RN_U32_LIMBS + BUS as usize
    }

    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let cols: &Sha256CompressRnCols<AB::IF> = {
            let up = builder.up();
            let (prefix, shorts, suffix) = unsafe { up.align_to::<Sha256CompressRnCols<AB::IF>>() };
            debug_assert!(prefix.is_empty(), "Alignment should match");
            debug_assert!(suffix.is_empty(), "Alignment should match");
            debug_assert_eq!(shorts.len(), 1);
            unsafe { &*shorts.as_ptr() }
        };

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                cols.flag,
                &[
                    AB::IF::from_usize(SHA256_RN_PRECOMPILE_DATA),
                    cols.state_ptr,
                    cols.block_ptr,
                    cols.out_ptr,
                ],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&cols.flag));
            builder.declare_values(&[
                AB::IF::from_usize(SHA256_RN_PRECOMPILE_DATA),
                cols.state_ptr,
                cols.block_ptr,
                cols.out_ptr,
            ]);
        }

        builder.assert_bool(cols.flag);
        eval_scheduling(builder, &cols.sha);
        let final_state = eval_compression::<AB>(&cols.sha);
        eval_output_bridge(builder, &cols.sha, &final_state);
    }
}

fn eval_scheduling<AB: AirBuilder>(builder: &mut AB, local: &Sha256RnCols<AB::IF>) {
    let two_16 = AB::IF::from_usize(1 << BITS_PER_LIMB);
    for t in SHA256_RN_BLOCK_WORDS..SHA256_RN_COMPRESS_ROUNDS {
        let cols = &local.scheduling[t - SHA256_RN_BLOCK_WORDS];
        let w_16 = &local.w[t - 16];
        let w_7 = &local.w[t - 7];
        let new_w = &local.w[t];

        let sigma_0_low = cols.sigma_0_o0_low + cols.sigma_0_o1_low + cols.sigma_0_o2_low;
        let sigma_0_high = cols.sigma_0_o0_high + cols.sigma_0_o1_high + cols.sigma_0_o2_high;
        let sigma_1_low = cols.sigma_1_o0_low + cols.sigma_1_o1_low + cols.sigma_1_o2_low;
        let sigma_1_high = cols.sigma_1_o0_high + cols.sigma_1_o1_high + cols.sigma_1_o2_high;

        builder.assert_zero(new_w[0] + cols.carry_low * two_16 - w_16[0] - sigma_0_low - w_7[0] - sigma_1_low);
        builder.assert_zero(
            new_w[1] + cols.carry_high * two_16 - w_16[1] - sigma_0_high - w_7[1] - sigma_1_high - cols.carry_low,
        );
    }
}

fn eval_compression<AB: AirBuilder>(local: &Sha256RnCols<AB::IF>) -> [[AB::IF; SHA256_RN_U32_LIMBS]; SHA256_RN_WORDS] {
    let two_8 = AB::IF::from_usize(1 << 8);
    let two_16 = AB::IF::from_usize(1 << BITS_PER_LIMB);

    let mut hash_buffer: [AB::IF; SHA256_RN_WORDS * SHA256_RN_U32_LIMBS] = core::array::from_fn(|i| {
        let word = i / SHA256_RN_U32_LIMBS;
        let limb = i % SHA256_RN_U32_LIMBS;
        local.h_in[word][limb]
    });

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

        let cols = &local.compression[round];
        let e_i1_low = e_low - cols.e_i0_low;
        let e_i1_high = e_high - cols.e_i0_high;
        let f_i1_low = f_low - cols.f_i0_low;
        let f_i1_high = f_high - cols.f_i0_high;
        let g_i1_low = g_low - cols.g_i0_low;
        let g_i1_high = g_high - cols.g_i0_high;

        let sigma_1_low = cols.sigma_1_o0_low + cols.sigma_1_o1_low + cols.sigma_1_o2_low;
        let sigma_1_high = cols.sigma_1_o0_high + cols.sigma_1_o1_high + cols.sigma_1_o2_high;
        let ch_left_low = cols.ch_left_i0_low + cols.ch_left_i1_low;
        let ch_left_high = cols.ch_left_i0_high + cols.ch_left_i1_high;
        let ch_right_low = cols.ch_right_i0_low + cols.ch_right_i1_low;
        let ch_right_high = cols.ch_right_i0_high + cols.ch_right_i1_high;

        let a_i0_low = a_low - cols.a_i1_low_0 - cols.a_i1_low_1 * two_8;
        let a_i1_high = a_high - cols.a_i0_high_0 - cols.a_i0_high_1 * two_8;
        let b_i0_low = b_low - cols.b_i1_low_0 - cols.b_i1_low_1 * two_8;
        let b_i1_high = b_high - cols.b_i0_high_0 - cols.b_i0_high_1 * two_8;
        let c_i0_low = c_low - cols.c_i1_low_0 - cols.c_i1_low_1 * two_8;
        let c_i1_high = c_high - cols.c_i0_high_0 - cols.c_i0_high_1 * two_8;

        let sigma_0_low = cols.sigma_0_o0_low + cols.sigma_0_o1_low + cols.sigma_0_o2_low;
        let sigma_0_high = cols.sigma_0_o0_high + cols.sigma_0_o1_high + cols.sigma_0_o2_high;
        let maj_low = cols.maj_i0_low + cols.maj_i1_low_0 + cols.maj_i1_low_1 * two_8;
        let maj_high = cols.maj_i0_high_0 + cols.maj_i0_high_1 * two_8 + cols.maj_i1_high;

        // These values are normally checked by rookie-numbers lookup relations. They are kept
        // live here so the no-lookup experiment preserves the same residual expression shape.
        let _pretend_lookup_inputs = [
            e_i1_low, e_i1_high, f_i1_low, f_i1_high, g_i1_low, g_i1_high, a_i0_low, a_i1_high, b_i0_low, b_i1_high,
            c_i0_low, c_i1_high,
        ];

        let k_low = AB::IF::from_u32(SHA256_RN_K[round] & super::LIMB_MASK);
        let k_high = AB::IF::from_u32(SHA256_RN_K[round] >> BITS_PER_LIMB);
        let w_low = local.w[round][0];
        let w_high = local.w[round][1];

        let temp1_low = h_low + sigma_1_low + ch_left_low + ch_right_low + k_low + w_low;
        let temp1_high = h_high + sigma_1_high + ch_left_high + ch_right_high + k_high + w_high;
        let temp2_low = sigma_0_low + maj_low;
        let temp2_high = sigma_0_high + maj_high;

        let new_e_low = d_low + temp1_low - cols.e_carry_low * two_16;
        let new_e_high = d_high + temp1_high + cols.e_carry_low - cols.e_carry_high * two_16;
        let new_a_low = temp1_low + temp2_low - cols.a_carry_low * two_16;
        let new_a_high = temp1_high + temp2_high + cols.a_carry_low - cols.a_carry_high * two_16;

        hash_buffer = [
            new_a_low, new_a_high, a_low, a_high, b_low, b_high, c_low, c_high, new_e_low, new_e_high, e_low, e_high,
            f_low, f_high, g_low, g_high,
        ];
    }

    core::array::from_fn(|i| [hash_buffer[2 * i], hash_buffer[2 * i + 1]])
}

fn eval_output_bridge<AB: AirBuilder>(
    builder: &mut AB,
    local: &Sha256RnCols<AB::IF>,
    final_state: &[[AB::IF; SHA256_RN_U32_LIMBS]; SHA256_RN_WORDS],
) {
    for (i, final_word) in final_state.iter().enumerate() {
        add2_expr_out(builder, &local.h_out[i], &local.h_in[i], final_word);
    }
}

#[inline]
fn add2_expr_out<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::IF; SHA256_RN_U32_LIMBS],
    b: &[AB::IF; SHA256_RN_U32_LIMBS],
    c: &[AB::IF; SHA256_RN_U32_LIMBS],
) {
    let two_16 = AB::IF::from_usize(1 << BITS_PER_LIMB);
    let two_32 = two_16.square();

    let acc_16 = a[0] - b[0] - c[0];
    let acc_32 = a[1] - b[1] - c[1];
    let acc = acc_16 + acc_32 * two_16;

    builder.assert_zero(acc * (acc + two_32));
    builder.assert_zero(acc_16 * (acc_16 + two_16));
}
