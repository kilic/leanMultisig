use core::{
    borrow::{Borrow, BorrowMut},
    mem::size_of,
};

use super::{SHA256_RN_COMPRESS_ROUNDS, SHA256_RN_SCHEDULE_EXTENSIONS, SHA256_RN_U32_LIMBS, SHA256_RN_WORDS};

pub const SHA256_RN_COL_FLAG: usize = 0;
pub const SHA256_RN_COL_STATE_PTR: usize = 1;
pub const SHA256_RN_COL_BLOCK_PTR: usize = 2;
pub const SHA256_RN_COL_OUT_PTR: usize = 3;
pub const SHA256_RN_COL_AIR_START: usize = 4;
pub const SHA256_RN_COL_STATE_LIMBS_START: usize = SHA256_RN_COL_AIR_START;
pub const SHA256_RN_COL_W_START: usize = SHA256_RN_COL_STATE_LIMBS_START + SHA256_RN_WORDS * SHA256_RN_U32_LIMBS;
pub const SHA256_RN_COL_OUT_LIMBS_START: usize = NUM_SHA256_COMPRESS_RN_COLS - SHA256_RN_WORDS * SHA256_RN_U32_LIMBS;

#[repr(C)]
#[derive(Debug)]
pub struct Sha256RnSchedulingRoundCols<T> {
    pub w_15_i0_low: T,
    pub w_15_i0_high: T,
    pub sigma_0_o0_low: T,
    pub sigma_0_o0_high: T,
    pub sigma_0_o20_pext: T,
    pub sigma_0_o1_low: T,
    pub sigma_0_o1_high: T,
    pub sigma_0_o21_pext: T,
    pub sigma_0_o2_low: T,
    pub sigma_0_o2_high: T,
    pub w_2_i0_low: T,
    pub w_2_i0_high: T,
    pub sigma_1_o0_low: T,
    pub sigma_1_o0_high: T,
    pub sigma_1_o20_pext: T,
    pub sigma_1_o1_low: T,
    pub sigma_1_o1_high: T,
    pub sigma_1_o21_pext: T,
    pub sigma_1_o2_low: T,
    pub sigma_1_o2_high: T,
    pub carry_low: T,
    pub carry_high: T,
}

#[repr(C)]
#[derive(Debug)]
pub struct Sha256RnCompressionRoundCols<T> {
    pub e_i0_low: T,
    pub e_i0_high: T,
    pub sigma_1_o0_low: T,
    pub sigma_1_o0_high: T,
    pub sigma_1_o20_pext: T,
    pub sigma_1_o1_low: T,
    pub sigma_1_o1_high: T,
    pub sigma_1_o21_pext: T,
    pub sigma_1_o2_low: T,
    pub sigma_1_o2_high: T,
    pub f_i0_low: T,
    pub f_i0_high: T,
    pub ch_left_i0_low: T,
    pub ch_left_i0_high: T,
    pub ch_left_i1_low: T,
    pub ch_left_i1_high: T,
    pub g_i0_low: T,
    pub g_i0_high: T,
    pub ch_right_i0_low: T,
    pub ch_right_i0_high: T,
    pub ch_right_i1_low: T,
    pub ch_right_i1_high: T,
    pub a_i0_high_0: T,
    pub a_i0_high_1: T,
    pub a_i1_low_0: T,
    pub a_i1_low_1: T,
    pub sigma_0_o0_low: T,
    pub sigma_0_o0_high: T,
    pub sigma_0_o20_pext: T,
    pub sigma_0_o1_low: T,
    pub sigma_0_o1_high: T,
    pub sigma_0_o21_pext: T,
    pub sigma_0_o2_low: T,
    pub sigma_0_o2_high: T,
    pub b_i0_high_0: T,
    pub b_i0_high_1: T,
    pub b_i1_low_0: T,
    pub b_i1_low_1: T,
    pub c_i0_high_0: T,
    pub c_i0_high_1: T,
    pub c_i1_low_0: T,
    pub c_i1_low_1: T,
    pub maj_i0_low: T,
    pub maj_i0_high_0: T,
    pub maj_i0_high_1: T,
    pub maj_i1_low_0: T,
    pub maj_i1_low_1: T,
    pub maj_i1_high: T,
    pub e_carry_low: T,
    pub e_carry_high: T,
    pub a_carry_low: T,
    pub a_carry_high: T,
}

#[repr(C)]
#[derive(Debug)]
pub struct Sha256RnCols<T> {
    pub h_in: [[T; SHA256_RN_U32_LIMBS]; SHA256_RN_WORDS],
    pub w: [[T; SHA256_RN_U32_LIMBS]; SHA256_RN_COMPRESS_ROUNDS],
    pub scheduling: [Sha256RnSchedulingRoundCols<T>; SHA256_RN_SCHEDULE_EXTENSIONS],
    pub compression: [Sha256RnCompressionRoundCols<T>; SHA256_RN_COMPRESS_ROUNDS],
    pub h_out: [[T; SHA256_RN_U32_LIMBS]; SHA256_RN_WORDS],
}

#[repr(C)]
#[derive(Debug)]
pub struct Sha256CompressRnCols<T> {
    pub flag: T,
    pub state_ptr: T,
    pub block_ptr: T,
    pub out_ptr: T,
    pub sha: Sha256RnCols<T>,
}

pub const NUM_SHA256_RN_AIR_COLS: usize = size_of::<Sha256RnCols<u8>>();
pub const NUM_SHA256_COMPRESS_RN_COLS: usize = size_of::<Sha256CompressRnCols<u8>>();

impl<T> Borrow<Sha256RnCols<T>> for [T] {
    fn borrow(&self) -> &Sha256RnCols<T> {
        debug_assert_eq!(self.len(), NUM_SHA256_RN_AIR_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to::<Sha256RnCols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}

impl<T> BorrowMut<Sha256RnCols<T>> for [T] {
    fn borrow_mut(&mut self) -> &mut Sha256RnCols<T> {
        debug_assert_eq!(self.len(), NUM_SHA256_RN_AIR_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to_mut::<Sha256RnCols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &mut shorts[0]
    }
}

impl<T> Borrow<Sha256CompressRnCols<T>> for [T] {
    fn borrow(&self) -> &Sha256CompressRnCols<T> {
        debug_assert_eq!(self.len(), NUM_SHA256_COMPRESS_RN_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to::<Sha256CompressRnCols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}

impl<T> BorrowMut<Sha256CompressRnCols<T>> for [T] {
    fn borrow_mut(&mut self) -> &mut Sha256CompressRnCols<T> {
        debug_assert_eq!(self.len(), NUM_SHA256_COMPRESS_RN_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to_mut::<Sha256CompressRnCols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &mut shorts[0]
    }
}
