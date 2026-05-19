/-
  Layer C: Round Step (E-State Update)
  Field-level low/high-limb equations for the `e` update.
  Depends on: Semantics
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.RoundStep.Semantics

set_option autoImplicit false

set_option maxHeartbeats 10000000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

private theorem round_step_e_lo_eq_source (air : C FBB ExtF) (row slot : ℕ)
    (hslot : slot < 4)
    (hrs : round_step_constraints air row)
    (hrawE_bits : isBitsWord (rawConcatEBitsWord air row (slot + 3))) :
    lo16Expr (rawConcatABitsWord air row slot) +
      lo16Expr (rawConcatEBitsWord air row slot) +
      round_step_a_lo_sigma1_rhs air row slot +
      round_step_a_lo_ch_rhs air row slot hrawE_bits +
      lo16Expr (nextScheduleBitsWord air row slot) * next_is_round_row air row +
      roundConstantPolyAtNext air row slot 0 -
        (lo16Expr (nextEBitsWord air row slot) +
          next_carry_e air slot 0 row * 65536) = 0 := by
  have hslot' : roundStepELoConstraint air row slot := round_step_e_lo air row slot hslot hrs
  interval_cases slot
  · simpa only [roundStepELoConstraint, constraint_723, roundConstantPolyAtNext,
      lo16Expr, round_step_a_lo_sigma1_rhs, round_step_a_lo_sigma1_bit,
      round_step_a_lo_ch_rhs, round_step_a_lo_ch_bit,
      nextScheduleBitsWord, nextEBitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord, roundConstantLookupPoly, encoder_choose2] using hslot'
  · simpa only [roundStepELoConstraint, constraint_727, roundConstantPolyAtNext,
      lo16Expr, round_step_a_lo_sigma1_rhs, round_step_a_lo_sigma1_bit,
      round_step_a_lo_ch_rhs, round_step_a_lo_ch_bit,
      nextScheduleBitsWord, nextEBitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord, roundConstantLookupPoly, encoder_choose2] using hslot'
  · simpa only [roundStepELoConstraint, constraint_731, roundConstantPolyAtNext,
      lo16Expr, round_step_a_lo_sigma1_rhs, round_step_a_lo_sigma1_bit,
      round_step_a_lo_ch_rhs, round_step_a_lo_ch_bit,
      nextScheduleBitsWord, nextEBitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord, roundConstantLookupPoly, encoder_choose2] using hslot'
  · simpa only [roundStepELoConstraint, constraint_735, roundConstantPolyAtNext,
      lo16Expr, round_step_a_lo_sigma1_rhs, round_step_a_lo_sigma1_bit,
      round_step_a_lo_ch_rhs, round_step_a_lo_ch_bit,
      nextScheduleBitsWord, nextEBitsWord, rawConcatABitsWord, rawConcatEBitsWord,
      eBitsWord, aBitsWord, roundConstantLookupPoly, encoder_choose2] using hslot'

theorem round_step_e_lo_eq_param (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16) :
    composeLo16 (concatABitsWord air row slot) +
      composeLo16 (concatEBitsWord air row slot) +
      composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) +
      composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
          (concatEBitsWord air row (slot + 2))
          (concatEBitsWord air row (slot + 1))) +
      k_limb_at row_idx slot 0 +
      composeLo16 (scheduleBitsWord air (nextRow air row) slot) =
    composeLo16 (eBitsWord air (nextRow air row) slot) +
      next_carry_e air slot 0 row * (2 ^ 16 : ℕ) := by
  have hrawE_bits : isBitsWord (rawConcatEBitsWord air row (slot + 3)) := by
    simpa [rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 3) hrot hrow] using
      concatEBits_boolean air row (slot + 3) (by omega) hbb hbb_next
  have hsrc := round_step_e_lo_eq_source air row slot hslot hrs hrawE_bits
  have hk :
      roundConstantPolyAtNext air row slot 0 = k_limb_at row_idx slot 0 :=
    roundConstantPolyAtNext_eq_k_limb_at air row slot 0 row_idx
      hslot (by omega) hrot hrow hflags_next hidx hidx_bound
  have hpow : (((2 ^ 16 : ℕ) : FBB) = 65536) := by
    norm_num
  rw [hround_next, hk, ← hpow] at hsrc
  simp only [mul_one] at hsrc
  have hperm :
      lo16Expr (rawConcatABitsWord air row slot) +
          lo16Expr (rawConcatEBitsWord air row slot) +
          round_step_a_lo_sigma1_rhs air row slot +
          round_step_a_lo_ch_rhs air row slot hrawE_bits +
          lo16Expr (nextScheduleBitsWord air row slot) +
          k_limb_at row_idx slot 0 =
        lo16Expr (rawConcatABitsWord air row slot) +
          lo16Expr (rawConcatEBitsWord air row slot) +
          round_step_a_lo_sigma1_rhs air row slot +
          round_step_a_lo_ch_rhs air row slot hrawE_bits +
          k_limb_at row_idx slot 0 +
          lo16Expr (nextScheduleBitsWord air row slot) := by
    ac_rfl
  rw [hperm] at hsrc
  rw [← composeLo16_eq_lo16Expr (rawConcatABitsWord air row slot),
    ← composeLo16_eq_lo16Expr (rawConcatEBitsWord air row slot),
    ← round_step_a_lo_sigma1_eq air row slot,
    ← round_step_a_lo_ch_eq air row slot hrawE_bits,
    ← composeLo16_eq_lo16Expr (nextScheduleBitsWord air row slot),
    ← composeLo16_eq_lo16Expr (nextEBitsWord air row slot)] at hsrc
  have hraw := sub_eq_zero.mp hsrc
  simpa only [nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row slot hrot hrow,
    nextEBitsWord_eq_eBitsWord_nextRow air row slot hrot hrow,
    rawConcatABitsWord_eq_concatABitsWord air row slot hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row slot hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 1) hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 2) hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 3) hrot hrow,
    add_assoc, add_left_comm, add_comm] using hraw

/-- Field-level low-limb equation for the `e` update of one round slot. -/
theorem round_step_e_lo_eq (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16) :
    composeLo16 (concatABitsWord air row slot) +
      composeLo16 (concatEBitsWord air row slot) +
      composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) +
    composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
          (concatEBitsWord air row (slot + 2))
          (concatEBitsWord air row (slot + 1))) +
      k_limb_at row_idx slot 0 +
      composeLo16 (scheduleBitsWord air (nextRow air row) slot) =
    composeLo16 (eBitsWord air (nextRow air row) slot) +
      next_carry_e air slot 0 row * (2 ^ 16 : ℕ) := by
  simpa using round_step_e_lo_eq_param air row slot row_idx hslot hrow hrot hrs hbb hbb_next
    hround_next hflags_next hidx hidx_bound

/-- Field-level high-limb equation for the `e` update of one round slot. -/
theorem round_step_e_hi_eq (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16) :
    composeHi16 (concatABitsWord air row slot) +
      composeHi16 (concatEBitsWord air row slot) +
      composeHi16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) +
      composeHi16 (fieldCh (concatEBitsWord air row (slot + 3))
          (concatEBitsWord air row (slot + 2))
          (concatEBitsWord air row (slot + 1))) +
      k_limb_at row_idx slot 1 +
      composeHi16 (scheduleBitsWord air (nextRow air row) slot) +
      next_carry_e air slot 0 row =
    composeHi16 (eBitsWord air (nextRow air row) slot) +
      next_carry_e air slot 1 row * (2 ^ 16 : ℕ) := by
  interval_cases slot
  · have hrawE3_bits : isBitsWord (rawConcatEBitsWord air row 3) := by
      simpa [rawConcatEBitsWord_eq_concatEBitsWord air row 3 hrot hrow] using
        concatEBits_boolean air row 3 (by omega) hbb hbb_next
    have hsrc :
        next_carry_e air 0 0 row +
          hi16Expr (rawConcatABitsWord air row 0) +
          hi16Expr (rawConcatEBitsWord air row 0) +
          round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 3) +
          round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 3)
            (rawConcatEBitsWord air row 2) (rawConcatEBitsWord air row 1) +
          hi16Expr (nextScheduleBitsWord air row 0) * next_is_round_row air row +
          roundConstantPolyAtNext air row 0 1 -
            (hi16Expr (nextEBitsWord air row 0) +
              next_carry_e air 0 1 row * 65536) = 0 := by
      have hslot0 : roundStepEHiConstraint air row 0 := round_step_e_hi air row 0 (by omega) hrs
      simpa only [roundStepEHiConstraint, constraint_724, roundConstantPolyAtNext,
        hi16Expr, round_step_a_hi_sigma1_rhs, round_step_a_hi_sigma1_bit,
        round_step_a_hi_ch_rhs, round_step_a_hi_ch_bit,
        nextScheduleBitsWord, nextEBitsWord, rawConcatABitsWord, rawConcatEBitsWord,
        eBitsWord, aBitsWord, roundConstantLookupPoly, encoder_choose2] using hslot0
    have hk :
        roundConstantPolyAtNext air row 0 1 = k_limb_at row_idx 0 1 :=
      roundConstantPolyAtNext_eq_k_limb_at air row 0 1 row_idx
        (by omega) (by omega) hrot hrow hflags_next hidx hidx_bound
    have hpow : (((2 ^ 16 : ℕ) : FBB) = 65536) := by norm_num
    rw [hround_next, hk, ← hpow] at hsrc
    simp only [mul_one] at hsrc
    have hperm :
        next_carry_e air 0 0 row +
            hi16Expr (rawConcatABitsWord air row 0) +
            hi16Expr (rawConcatEBitsWord air row 0) +
            round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 3) +
            round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 3)
              (rawConcatEBitsWord air row 2) (rawConcatEBitsWord air row 1) +
            hi16Expr (nextScheduleBitsWord air row 0) +
            k_limb_at row_idx 0 1 =
          hi16Expr (rawConcatABitsWord air row 0) +
            hi16Expr (rawConcatEBitsWord air row 0) +
            round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 3) +
            round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 3)
              (rawConcatEBitsWord air row 2) (rawConcatEBitsWord air row 1) +
            k_limb_at row_idx 0 1 +
            hi16Expr (nextScheduleBitsWord air row 0) +
            next_carry_e air 0 0 row := by
      ac_rfl
    rw [hperm] at hsrc
    rw [← composeHi16_eq_hi16Expr (rawConcatABitsWord air row 0),
      ← composeHi16_eq_hi16Expr (rawConcatEBitsWord air row 0),
      ← round_step_a_hi_sigma1_eq (rawConcatEBitsWord air row 3),
      ← round_step_a_hi_ch_eq (rawConcatEBitsWord air row 3)
        (rawConcatEBitsWord air row 2) (rawConcatEBitsWord air row 1) hrawE3_bits,
      ← composeHi16_eq_hi16Expr (nextScheduleBitsWord air row 0),
      ← composeHi16_eq_hi16Expr (nextEBitsWord air row 0)] at hsrc
    have hraw := sub_eq_zero.mp hsrc
    simpa only [nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 0 hrot hrow,
      nextEBitsWord_eq_eBitsWord_nextRow air row 0 hrot hrow,
      rawConcatABitsWord_eq_concatABitsWord air row 0 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 0 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 1 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 2 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 3 hrot hrow,
      add_assoc, add_left_comm, add_comm] using hraw
  · have hrawE4_bits : isBitsWord (rawConcatEBitsWord air row 4) := by
      simpa [rawConcatEBitsWord_eq_concatEBitsWord air row 4 hrot hrow] using
        concatEBits_boolean air row 4 (by omega) hbb hbb_next
    have hsrc :
        next_carry_e air 1 0 row +
          hi16Expr (rawConcatABitsWord air row 1) +
          hi16Expr (rawConcatEBitsWord air row 1) +
          round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 4) +
          round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 4)
            (rawConcatEBitsWord air row 3) (rawConcatEBitsWord air row 2) +
          hi16Expr (nextScheduleBitsWord air row 1) * next_is_round_row air row +
          roundConstantPolyAtNext air row 1 1 -
            (hi16Expr (nextEBitsWord air row 1) +
              next_carry_e air 1 1 row * 65536) = 0 := by
      have hslot1 : roundStepEHiConstraint air row 1 := round_step_e_hi air row 1 (by omega) hrs
      simpa only [roundStepEHiConstraint, constraint_728, roundConstantPolyAtNext,
        hi16Expr, round_step_a_hi_sigma1_rhs, round_step_a_hi_sigma1_bit,
        round_step_a_hi_ch_rhs, round_step_a_hi_ch_bit,
        nextScheduleBitsWord, nextEBitsWord, rawConcatABitsWord, rawConcatEBitsWord,
        eBitsWord, aBitsWord, roundConstantLookupPoly, encoder_choose2] using hslot1
    have hk :
        roundConstantPolyAtNext air row 1 1 = k_limb_at row_idx 1 1 :=
      roundConstantPolyAtNext_eq_k_limb_at air row 1 1 row_idx
        (by omega) (by omega) hrot hrow hflags_next hidx hidx_bound
    have hpow : (((2 ^ 16 : ℕ) : FBB) = 65536) := by norm_num
    rw [hround_next, hk, ← hpow] at hsrc
    simp only [mul_one] at hsrc
    have hperm :
        next_carry_e air 1 0 row +
            hi16Expr (rawConcatABitsWord air row 1) +
            hi16Expr (rawConcatEBitsWord air row 1) +
            round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 4) +
            round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 4)
              (rawConcatEBitsWord air row 3) (rawConcatEBitsWord air row 2) +
            hi16Expr (nextScheduleBitsWord air row 1) +
            k_limb_at row_idx 1 1 =
          hi16Expr (rawConcatABitsWord air row 1) +
            hi16Expr (rawConcatEBitsWord air row 1) +
            round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 4) +
            round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 4)
              (rawConcatEBitsWord air row 3) (rawConcatEBitsWord air row 2) +
            k_limb_at row_idx 1 1 +
            hi16Expr (nextScheduleBitsWord air row 1) +
            next_carry_e air 1 0 row := by
      ac_rfl
    rw [hperm] at hsrc
    rw [← composeHi16_eq_hi16Expr (rawConcatABitsWord air row 1),
      ← composeHi16_eq_hi16Expr (rawConcatEBitsWord air row 1),
      ← round_step_a_hi_sigma1_eq (rawConcatEBitsWord air row 4),
      ← round_step_a_hi_ch_eq (rawConcatEBitsWord air row 4)
        (rawConcatEBitsWord air row 3) (rawConcatEBitsWord air row 2) hrawE4_bits,
      ← composeHi16_eq_hi16Expr (nextScheduleBitsWord air row 1),
      ← composeHi16_eq_hi16Expr (nextEBitsWord air row 1)] at hsrc
    have hraw := sub_eq_zero.mp hsrc
    simpa only [nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 1 hrot hrow,
      nextEBitsWord_eq_eBitsWord_nextRow air row 1 hrot hrow,
      rawConcatABitsWord_eq_concatABitsWord air row 1 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 1 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 2 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 3 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 4 hrot hrow,
      add_assoc, add_left_comm, add_comm] using hraw
  · have hrawE5_bits : isBitsWord (rawConcatEBitsWord air row 5) := by
      simpa [rawConcatEBitsWord_eq_concatEBitsWord air row 5 hrot hrow] using
        concatEBits_boolean air row 5 (by omega) hbb hbb_next
    have hsrc :
        next_carry_e air 2 0 row +
          hi16Expr (rawConcatABitsWord air row 2) +
          hi16Expr (rawConcatEBitsWord air row 2) +
          round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 5) +
          round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 5)
            (rawConcatEBitsWord air row 4) (rawConcatEBitsWord air row 3) +
          hi16Expr (nextScheduleBitsWord air row 2) * next_is_round_row air row +
          roundConstantPolyAtNext air row 2 1 -
            (hi16Expr (nextEBitsWord air row 2) +
              next_carry_e air 2 1 row * 65536) = 0 := by
      have hslot2 : roundStepEHiConstraint air row 2 := round_step_e_hi air row 2 (by omega) hrs
      simpa only [roundStepEHiConstraint, constraint_732, roundConstantPolyAtNext,
        hi16Expr, round_step_a_hi_sigma1_rhs, round_step_a_hi_sigma1_bit,
        round_step_a_hi_ch_rhs, round_step_a_hi_ch_bit,
        nextScheduleBitsWord, nextEBitsWord, rawConcatABitsWord, rawConcatEBitsWord,
        eBitsWord, aBitsWord, roundConstantLookupPoly, encoder_choose2] using hslot2
    have hk :
        roundConstantPolyAtNext air row 2 1 = k_limb_at row_idx 2 1 :=
      roundConstantPolyAtNext_eq_k_limb_at air row 2 1 row_idx
        (by omega) (by omega) hrot hrow hflags_next hidx hidx_bound
    have hpow : (((2 ^ 16 : ℕ) : FBB) = 65536) := by norm_num
    rw [hround_next, hk, ← hpow] at hsrc
    simp only [mul_one] at hsrc
    have hperm :
        next_carry_e air 2 0 row +
            hi16Expr (rawConcatABitsWord air row 2) +
            hi16Expr (rawConcatEBitsWord air row 2) +
            round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 5) +
            round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 5)
              (rawConcatEBitsWord air row 4) (rawConcatEBitsWord air row 3) +
            hi16Expr (nextScheduleBitsWord air row 2) +
            k_limb_at row_idx 2 1 =
          hi16Expr (rawConcatABitsWord air row 2) +
            hi16Expr (rawConcatEBitsWord air row 2) +
            round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 5) +
            round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 5)
              (rawConcatEBitsWord air row 4) (rawConcatEBitsWord air row 3) +
            k_limb_at row_idx 2 1 +
            hi16Expr (nextScheduleBitsWord air row 2) +
            next_carry_e air 2 0 row := by
      ac_rfl
    rw [hperm] at hsrc
    rw [← composeHi16_eq_hi16Expr (rawConcatABitsWord air row 2),
      ← composeHi16_eq_hi16Expr (rawConcatEBitsWord air row 2),
      ← round_step_a_hi_sigma1_eq (rawConcatEBitsWord air row 5),
      ← round_step_a_hi_ch_eq (rawConcatEBitsWord air row 5)
        (rawConcatEBitsWord air row 4) (rawConcatEBitsWord air row 3) hrawE5_bits,
      ← composeHi16_eq_hi16Expr (nextScheduleBitsWord air row 2),
      ← composeHi16_eq_hi16Expr (nextEBitsWord air row 2)] at hsrc
    have hraw := sub_eq_zero.mp hsrc
    simpa only [nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 2 hrot hrow,
      nextEBitsWord_eq_eBitsWord_nextRow air row 2 hrot hrow,
      rawConcatABitsWord_eq_concatABitsWord air row 2 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 2 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 3 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 4 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 5 hrot hrow,
      add_assoc, add_left_comm, add_comm] using hraw
  · have hrawE6_bits : isBitsWord (rawConcatEBitsWord air row 6) := by
      simpa [rawConcatEBitsWord_eq_concatEBitsWord air row 6 hrot hrow] using
        concatEBits_boolean air row 6 (by omega) hbb hbb_next
    have hsrc :
        next_carry_e air 3 0 row +
          hi16Expr (rawConcatABitsWord air row 3) +
          hi16Expr (rawConcatEBitsWord air row 3) +
          round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 6) +
          round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 6)
            (rawConcatEBitsWord air row 5) (rawConcatEBitsWord air row 4) +
          hi16Expr (nextScheduleBitsWord air row 3) * next_is_round_row air row +
          roundConstantPolyAtNext air row 3 1 -
            (hi16Expr (nextEBitsWord air row 3) +
              next_carry_e air 3 1 row * 65536) = 0 := by
      have hslot3 : roundStepEHiConstraint air row 3 := round_step_e_hi air row 3 (by omega) hrs
      simpa only [roundStepEHiConstraint, constraint_736, roundConstantPolyAtNext,
        hi16Expr, round_step_a_hi_sigma1_rhs, round_step_a_hi_sigma1_bit,
        round_step_a_hi_ch_rhs, round_step_a_hi_ch_bit,
        nextScheduleBitsWord, nextEBitsWord, rawConcatABitsWord, rawConcatEBitsWord,
        eBitsWord, aBitsWord, roundConstantLookupPoly, encoder_choose2] using hslot3
    have hk :
        roundConstantPolyAtNext air row 3 1 = k_limb_at row_idx 3 1 :=
      roundConstantPolyAtNext_eq_k_limb_at air row 3 1 row_idx
        (by omega) (by omega) hrot hrow hflags_next hidx hidx_bound
    have hpow : (((2 ^ 16 : ℕ) : FBB) = 65536) := by norm_num
    rw [hround_next, hk, ← hpow] at hsrc
    simp only [mul_one] at hsrc
    have hperm :
        next_carry_e air 3 0 row +
            hi16Expr (rawConcatABitsWord air row 3) +
            hi16Expr (rawConcatEBitsWord air row 3) +
            round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 6) +
            round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 6)
              (rawConcatEBitsWord air row 5) (rawConcatEBitsWord air row 4) +
            hi16Expr (nextScheduleBitsWord air row 3) +
            k_limb_at row_idx 3 1 =
          hi16Expr (rawConcatABitsWord air row 3) +
            hi16Expr (rawConcatEBitsWord air row 3) +
            round_step_a_hi_sigma1_rhs (rawConcatEBitsWord air row 6) +
            round_step_a_hi_ch_rhs (rawConcatEBitsWord air row 6)
              (rawConcatEBitsWord air row 5) (rawConcatEBitsWord air row 4) +
            k_limb_at row_idx 3 1 +
            hi16Expr (nextScheduleBitsWord air row 3) +
            next_carry_e air 3 0 row := by
      ac_rfl
    rw [hperm] at hsrc
    rw [← composeHi16_eq_hi16Expr (rawConcatABitsWord air row 3),
      ← composeHi16_eq_hi16Expr (rawConcatEBitsWord air row 3),
      ← round_step_a_hi_sigma1_eq (rawConcatEBitsWord air row 6),
      ← round_step_a_hi_ch_eq (rawConcatEBitsWord air row 6)
        (rawConcatEBitsWord air row 5) (rawConcatEBitsWord air row 4) hrawE6_bits,
      ← composeHi16_eq_hi16Expr (nextScheduleBitsWord air row 3),
      ← composeHi16_eq_hi16Expr (nextEBitsWord air row 3)] at hsrc
    have hraw := sub_eq_zero.mp hsrc
    simpa only [nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 3 hrot hrow,
      nextEBitsWord_eq_eBitsWord_nextRow air row 3 hrot hrow,
      rawConcatABitsWord_eq_concatABitsWord air row 3 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 3 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 4 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 5 hrot hrow,
      rawConcatEBitsWord_eq_concatEBitsWord air row 6 hrot hrow,
      add_assoc, add_left_comm, add_comm] using hraw

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
