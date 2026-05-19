/-
  Layer B: Message Schedule Correctness (Core)

  Combined: W3 Helper + Intermed 4 common helpers + per-slot correctness.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.FieldArithmetic
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.Defs

set_option autoImplicit false
set_option maxHeartbeats 40000000

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

theorem msg_schedule_u16_limb_range_eq
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hlimb : limb < 4) :
    composeU16Limb (scheduleBitsWord air row slot) ⟨limb, hlimb⟩ =
      ∑ i ∈ Finset.range 16, msg_schedule_w air slot (i + 16 * limb) row * 2 ^ i := by
  calc
    composeU16Limb (scheduleBitsWord air row slot) ⟨limb, hlimb⟩ =
        ∑ i ∈ Finset.range 16,
          (if hi : i < 16 then
            scheduleBitsWord air row slot ⟨i + 16 * limb, by omega⟩ * 2 ^ i
           else 0) := by
            simpa using composeU16Limb_range_eq (scheduleBitsWord air row slot) ⟨limb, hlimb⟩
    _ = ∑ i ∈ Finset.range 16, msg_schedule_w air slot (i + 16 * limb) row * 2 ^ i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [scheduleBitsWord, Finset.mem_range.mp hi]

/-- Each `w_3` helper limb on the successor row equals the corresponding
    16-bit chunk of the local schedule word `w[slot + 1]`. -/
theorem w3_helper_correct_raw (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 3) (hlimb : limb < 4)
    (hs : schedule_constraints air row)
    (hround : is_round_row air row = 1) :
    next_schedule_helper_w_3 air slot limb row =
      concatScheduleU16Limb air row (slot + 1) limb := by
  rcases hs with ⟨h1050_1099, _, _, _, _, _, _, _⟩
  let h1052_1099 := h1050_1099.2.2
  have h1052 : constraint_1052 air row := h1052_1099.1
  let h1053_1099 := h1052_1099.2
  have h1053 : constraint_1053 air row := h1053_1099.1
  let h1054_1099 := h1053_1099.2
  have h1054 : constraint_1054 air row := h1054_1099.1
  let h1055_1099 := h1054_1099.2
  have h1055 : constraint_1055 air row := h1055_1099.1
  let h1056_1099 := h1055_1099.2
  have h1056 : constraint_1056 air row := h1056_1099.1
  let h1057_1099 := h1056_1099.2
  have h1057 : constraint_1057 air row := h1057_1099.1
  let h1058_1099 := h1057_1099.2
  have h1058 : constraint_1058 air row := h1058_1099.1
  let h1059_1099 := h1058_1099.2
  have h1059 : constraint_1059 air row := h1059_1099.1
  let h1060_1099 := h1059_1099.2
  have h1060 : constraint_1060 air row := h1060_1099.1
  let h1061_1099 := h1060_1099.2
  have h1061 : constraint_1061 air row := h1061_1099.1
  let h1062_1099 := h1061_1099.2
  have h1062 : constraint_1062 air row := h1062_1099.1
  let h1063_1099 := h1062_1099.2
  have h1063 : constraint_1063 air row := h1063_1099.1
  have hslot' : slot + 1 < 4 := by omega
  have hpoly :
      msg_schedule_u16_limb air (slot + 1) limb row -
        next_schedule_helper_w_3 air slot limb row = 0 := by
    interval_cases slot <;> interval_cases limb
    · have hraw :
        msg_schedule_w air 1 0 row + msg_schedule_w air 1 1 row * 2 +
            msg_schedule_w air 1 2 row * 4 + msg_schedule_w air 1 3 row * 8 +
            msg_schedule_w air 1 4 row * 16 + msg_schedule_w air 1 5 row * 32 +
            msg_schedule_w air 1 6 row * 64 + msg_schedule_w air 1 7 row * 128 +
            msg_schedule_w air 1 8 row * 256 + msg_schedule_w air 1 9 row * 512 +
            msg_schedule_w air 1 10 row * 1024 + msg_schedule_w air 1 11 row * 2048 +
            msg_schedule_w air 1 12 row * 4096 + msg_schedule_w air 1 13 row * 8192 +
            msg_schedule_w air 1 14 row * 16384 + msg_schedule_w air 1 15 row * 32768 -
          next_schedule_helper_w_3 air 0 0 row = 0 := by
        simpa [constraint_1052, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1052
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 1 16 row + msg_schedule_w air 1 17 row * 2 +
            msg_schedule_w air 1 18 row * 4 + msg_schedule_w air 1 19 row * 8 +
            msg_schedule_w air 1 20 row * 16 + msg_schedule_w air 1 21 row * 32 +
            msg_schedule_w air 1 22 row * 64 + msg_schedule_w air 1 23 row * 128 +
            msg_schedule_w air 1 24 row * 256 + msg_schedule_w air 1 25 row * 512 +
            msg_schedule_w air 1 26 row * 1024 + msg_schedule_w air 1 27 row * 2048 +
            msg_schedule_w air 1 28 row * 4096 + msg_schedule_w air 1 29 row * 8192 +
            msg_schedule_w air 1 30 row * 16384 + msg_schedule_w air 1 31 row * 32768 -
          next_schedule_helper_w_3 air 0 1 row = 0 := by
        simpa [constraint_1053, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1053
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 1 32 row + msg_schedule_w air 1 33 row * 2 +
            msg_schedule_w air 1 34 row * 4 + msg_schedule_w air 1 35 row * 8 +
            msg_schedule_w air 1 36 row * 16 + msg_schedule_w air 1 37 row * 32 +
            msg_schedule_w air 1 38 row * 64 + msg_schedule_w air 1 39 row * 128 +
            msg_schedule_w air 1 40 row * 256 + msg_schedule_w air 1 41 row * 512 +
            msg_schedule_w air 1 42 row * 1024 + msg_schedule_w air 1 43 row * 2048 +
            msg_schedule_w air 1 44 row * 4096 + msg_schedule_w air 1 45 row * 8192 +
            msg_schedule_w air 1 46 row * 16384 + msg_schedule_w air 1 47 row * 32768 -
          next_schedule_helper_w_3 air 0 2 row = 0 := by
        simpa [constraint_1054, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1054
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 1 48 row + msg_schedule_w air 1 49 row * 2 +
            msg_schedule_w air 1 50 row * 4 + msg_schedule_w air 1 51 row * 8 +
            msg_schedule_w air 1 52 row * 16 + msg_schedule_w air 1 53 row * 32 +
            msg_schedule_w air 1 54 row * 64 + msg_schedule_w air 1 55 row * 128 +
            msg_schedule_w air 1 56 row * 256 + msg_schedule_w air 1 57 row * 512 +
            msg_schedule_w air 1 58 row * 1024 + msg_schedule_w air 1 59 row * 2048 +
            msg_schedule_w air 1 60 row * 4096 + msg_schedule_w air 1 61 row * 8192 +
            msg_schedule_w air 1 62 row * 16384 + msg_schedule_w air 1 63 row * 32768 -
          next_schedule_helper_w_3 air 0 3 row = 0 := by
        simpa [constraint_1055, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1055
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 2 0 row + msg_schedule_w air 2 1 row * 2 +
            msg_schedule_w air 2 2 row * 4 + msg_schedule_w air 2 3 row * 8 +
            msg_schedule_w air 2 4 row * 16 + msg_schedule_w air 2 5 row * 32 +
            msg_schedule_w air 2 6 row * 64 + msg_schedule_w air 2 7 row * 128 +
            msg_schedule_w air 2 8 row * 256 + msg_schedule_w air 2 9 row * 512 +
            msg_schedule_w air 2 10 row * 1024 + msg_schedule_w air 2 11 row * 2048 +
            msg_schedule_w air 2 12 row * 4096 + msg_schedule_w air 2 13 row * 8192 +
            msg_schedule_w air 2 14 row * 16384 + msg_schedule_w air 2 15 row * 32768 -
          next_schedule_helper_w_3 air 1 0 row = 0 := by
        simpa [constraint_1056, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1056
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 2 16 row + msg_schedule_w air 2 17 row * 2 +
            msg_schedule_w air 2 18 row * 4 + msg_schedule_w air 2 19 row * 8 +
            msg_schedule_w air 2 20 row * 16 + msg_schedule_w air 2 21 row * 32 +
            msg_schedule_w air 2 22 row * 64 + msg_schedule_w air 2 23 row * 128 +
            msg_schedule_w air 2 24 row * 256 + msg_schedule_w air 2 25 row * 512 +
            msg_schedule_w air 2 26 row * 1024 + msg_schedule_w air 2 27 row * 2048 +
            msg_schedule_w air 2 28 row * 4096 + msg_schedule_w air 2 29 row * 8192 +
            msg_schedule_w air 2 30 row * 16384 + msg_schedule_w air 2 31 row * 32768 -
          next_schedule_helper_w_3 air 1 1 row = 0 := by
        simpa [constraint_1057, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1057
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 2 32 row + msg_schedule_w air 2 33 row * 2 +
            msg_schedule_w air 2 34 row * 4 + msg_schedule_w air 2 35 row * 8 +
            msg_schedule_w air 2 36 row * 16 + msg_schedule_w air 2 37 row * 32 +
            msg_schedule_w air 2 38 row * 64 + msg_schedule_w air 2 39 row * 128 +
            msg_schedule_w air 2 40 row * 256 + msg_schedule_w air 2 41 row * 512 +
            msg_schedule_w air 2 42 row * 1024 + msg_schedule_w air 2 43 row * 2048 +
            msg_schedule_w air 2 44 row * 4096 + msg_schedule_w air 2 45 row * 8192 +
            msg_schedule_w air 2 46 row * 16384 + msg_schedule_w air 2 47 row * 32768 -
          next_schedule_helper_w_3 air 1 2 row = 0 := by
        simpa [constraint_1058, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1058
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 2 48 row + msg_schedule_w air 2 49 row * 2 +
            msg_schedule_w air 2 50 row * 4 + msg_schedule_w air 2 51 row * 8 +
            msg_schedule_w air 2 52 row * 16 + msg_schedule_w air 2 53 row * 32 +
            msg_schedule_w air 2 54 row * 64 + msg_schedule_w air 2 55 row * 128 +
            msg_schedule_w air 2 56 row * 256 + msg_schedule_w air 2 57 row * 512 +
            msg_schedule_w air 2 58 row * 1024 + msg_schedule_w air 2 59 row * 2048 +
            msg_schedule_w air 2 60 row * 4096 + msg_schedule_w air 2 61 row * 8192 +
            msg_schedule_w air 2 62 row * 16384 + msg_schedule_w air 2 63 row * 32768 -
          next_schedule_helper_w_3 air 1 3 row = 0 := by
        simpa [constraint_1059, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1059
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 3 0 row + msg_schedule_w air 3 1 row * 2 +
            msg_schedule_w air 3 2 row * 4 + msg_schedule_w air 3 3 row * 8 +
            msg_schedule_w air 3 4 row * 16 + msg_schedule_w air 3 5 row * 32 +
            msg_schedule_w air 3 6 row * 64 + msg_schedule_w air 3 7 row * 128 +
            msg_schedule_w air 3 8 row * 256 + msg_schedule_w air 3 9 row * 512 +
            msg_schedule_w air 3 10 row * 1024 + msg_schedule_w air 3 11 row * 2048 +
            msg_schedule_w air 3 12 row * 4096 + msg_schedule_w air 3 13 row * 8192 +
            msg_schedule_w air 3 14 row * 16384 + msg_schedule_w air 3 15 row * 32768 -
          next_schedule_helper_w_3 air 2 0 row = 0 := by
        simpa [constraint_1060, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1060
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 3 16 row + msg_schedule_w air 3 17 row * 2 +
            msg_schedule_w air 3 18 row * 4 + msg_schedule_w air 3 19 row * 8 +
            msg_schedule_w air 3 20 row * 16 + msg_schedule_w air 3 21 row * 32 +
            msg_schedule_w air 3 22 row * 64 + msg_schedule_w air 3 23 row * 128 +
            msg_schedule_w air 3 24 row * 256 + msg_schedule_w air 3 25 row * 512 +
            msg_schedule_w air 3 26 row * 1024 + msg_schedule_w air 3 27 row * 2048 +
            msg_schedule_w air 3 28 row * 4096 + msg_schedule_w air 3 29 row * 8192 +
            msg_schedule_w air 3 30 row * 16384 + msg_schedule_w air 3 31 row * 32768 -
          next_schedule_helper_w_3 air 2 1 row = 0 := by
        simpa [constraint_1061, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1061
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 3 32 row + msg_schedule_w air 3 33 row * 2 +
            msg_schedule_w air 3 34 row * 4 + msg_schedule_w air 3 35 row * 8 +
            msg_schedule_w air 3 36 row * 16 + msg_schedule_w air 3 37 row * 32 +
            msg_schedule_w air 3 38 row * 64 + msg_schedule_w air 3 39 row * 128 +
            msg_schedule_w air 3 40 row * 256 + msg_schedule_w air 3 41 row * 512 +
            msg_schedule_w air 3 42 row * 1024 + msg_schedule_w air 3 43 row * 2048 +
            msg_schedule_w air 3 44 row * 4096 + msg_schedule_w air 3 45 row * 8192 +
            msg_schedule_w air 3 46 row * 16384 + msg_schedule_w air 3 47 row * 32768 -
          next_schedule_helper_w_3 air 2 2 row = 0 := by
        simpa [constraint_1062, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1062
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    · have hraw :
        msg_schedule_w air 3 48 row + msg_schedule_w air 3 49 row * 2 +
            msg_schedule_w air 3 50 row * 4 + msg_schedule_w air 3 51 row * 8 +
            msg_schedule_w air 3 52 row * 16 + msg_schedule_w air 3 53 row * 32 +
            msg_schedule_w air 3 54 row * 64 + msg_schedule_w air 3 55 row * 128 +
            msg_schedule_w air 3 56 row * 256 + msg_schedule_w air 3 57 row * 512 +
            msg_schedule_w air 3 58 row * 1024 + msg_schedule_w air 3 59 row * 2048 +
            msg_schedule_w air 3 60 row * 4096 + msg_schedule_w air 3 61 row * 8192 +
            msg_schedule_w air 3 62 row * 16384 + msg_schedule_w air 3 63 row * 32768 -
          next_schedule_helper_w_3 air 2 3 row = 0 := by
        simpa [constraint_1063, hround, is_round_row, msg_schedule_w,
          next_schedule_helper_w_3] using h1063
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
  have hsum_eq :
      msg_schedule_u16_limb air (slot + 1) limb row =
        concatScheduleU16Limb air row (slot + 1) limb := by
    have hrange := (msg_schedule_u16_limb_range_eq air row (slot + 1) limb hlimb).symm
    rw [msg_schedule_u16_limb]
    simp [concatScheduleU16Limb, hlimb, concatScheduleBitsWord, hslot', hrange]
  calc
    next_schedule_helper_w_3 air slot limb row =
        msg_schedule_u16_limb air (slot + 1) limb row := by
          exact (sub_eq_zero.mp hpoly).symm
    _ = concatScheduleU16Limb air row (slot + 1) limb := hsum_eq

/-- Transport the raw helper equality onto the actual successor row. -/
theorem w3_helper_correct (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 3) (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hround : is_round_row air row = 1) :
    schedule_helper_w_3 air slot limb (nextRow air row) =
      concatScheduleU16Limb air row (slot + 1) limb := by
  simpa [next_schedule_helper_w_3_eq_nextRow air hrot slot limb row hrow] using
    w3_helper_correct_raw air row slot limb hslot hlimb hs hround

theorem raw_concat_schedule_small_sigma0_u16_limb_eq
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hlimb : limb < 4) :
    raw_concat_schedule_small_sigma0_u16_limb air slot limb row =
      composeU16Limb (fieldSmallSigma0 (rawConcatScheduleBitsWord air row slot)) ⟨limb, hlimb⟩ := by
  symm
  calc
    composeU16Limb (fieldSmallSigma0 (rawConcatScheduleBitsWord air row slot)) ⟨limb, hlimb⟩ =
        ∑ i ∈ Finset.range 16,
          (if hi : i < 16 then
            fieldSmallSigma0 (rawConcatScheduleBitsWord air row slot) ⟨i + 16 * limb, by omega⟩ *
              2 ^ i
           else 0) := by
            simpa using
              composeU16Limb_range_eq
                (fieldSmallSigma0 (rawConcatScheduleBitsWord air row slot)) ⟨limb, hlimb⟩
    _ = ∑ i ∈ Finset.range 16, raw_concat_schedule_small_sigma0_bit air slot (i + 16 * limb) row * 2 ^ i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi16 : i < 16 := Finset.mem_range.mp hi
          by_cases hslot : slot < 4
          · simp [raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, fieldSmallSigma0,
              fieldRotr, fieldShr, fieldXor, field_xor_expr, rawConcatScheduleBitsWord,
              scheduleBitsWord, hslot, hi16]
          · simp [raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, fieldSmallSigma0,
              fieldRotr, fieldShr, fieldXor, field_xor_expr, rawConcatScheduleBitsWord, hslot,
              nextScheduleBitsWord, hi16]

theorem msg_schedule_u16_limb_eq_concatScheduleU16Limb
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4) :
    msg_schedule_u16_limb air slot limb row =
      concatScheduleU16Limb air row slot limb := by
  calc
    msg_schedule_u16_limb air slot limb row =
        ∑ i ∈ Finset.range 16,
          msg_schedule_w air slot (i + 16 * limb) row * 2 ^ i := by
            rw [msg_schedule_u16_limb]
    _ = composeU16Limb (scheduleBitsWord air row slot) ⟨limb, hlimb⟩ := by
          symm
          calc
            composeU16Limb (scheduleBitsWord air row slot) ⟨limb, hlimb⟩ =
                ∑ i ∈ Finset.range 16,
                  (if hi : i < 16 then
                    scheduleBitsWord air row slot ⟨i + 16 * limb, by omega⟩ * 2 ^ i
                   else 0) := by
                    simpa using
                      composeU16Limb_range_eq (scheduleBitsWord air row slot) ⟨limb, hlimb⟩
            _ = ∑ i ∈ Finset.range 16,
                  msg_schedule_w air slot (i + 16 * limb) row * 2 ^ i := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    have hi16 : i < 16 := Finset.mem_range.mp hi
                    simp [scheduleBitsWord, hi16]
    _ = concatScheduleU16Limb air row slot limb := by
          simp [concatScheduleU16Limb, hlimb, concatScheduleBitsWord, hslot]

theorem intermed_4_from_poly
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4)
    (hslot_next :
      rawConcatScheduleBitsWord air row (slot + 1) =
        concatScheduleBitsWord air row (slot + 1))
    (hpoly :
      intermed_4 air slot limb (nextRow air row) -
        (msg_schedule_u16_limb air slot limb row +
          raw_concat_schedule_small_sigma0_u16_limb air (slot + 1) limb row) = 0) :
    intermed_4 air slot limb (nextRow air row) =
      concatScheduleU16Limb air row slot limb +
        composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air row (slot + 1)))
          ⟨limb, hlimb⟩ := by
  have hmsg := msg_schedule_u16_limb_eq_concatScheduleU16Limb air row slot limb hslot hlimb
  have hsigma := raw_concat_schedule_small_sigma0_u16_limb_eq air row (slot + 1) limb hlimb
  have hpoly' := hpoly
  rw [hmsg, hsigma] at hpoly'
  exact sub_eq_zero.mp (by simpa [hslot_next] using hpoly')

-- Per-slot correctness theorems

private theorem intermed_4_correct_slot0 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row) :
    intermed_4 air 0 limb (nextRow air row) =
      concatScheduleU16Limb air row 0 limb +
        composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air row 1))
          ⟨limb, hlimb⟩ := by
  have hvalid : row ≤ Circuit.last_row air := hrow.le
  have hslot_next :
      rawConcatScheduleBitsWord air row 1 =
        concatScheduleBitsWord air row 1 := by
    simpa using rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 1 hrot hvalid
  rcases hs with ⟨h1050_1099, _, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1050_1099 at h1050_1099
  let h1052_1099 := h1050_1099.2.2
  let h1053_1099 := h1052_1099.2
  let h1054_1099 := h1053_1099.2
  let h1055_1099 := h1054_1099.2
  let h1056_1099 := h1055_1099.2
  let h1057_1099 := h1056_1099.2
  let h1058_1099 := h1057_1099.2
  let h1059_1099 := h1058_1099.2
  let h1060_1099 := h1059_1099.2
  let h1061_1099 := h1060_1099.2
  let h1062_1099 := h1061_1099.2
  let h1063_1099 := h1062_1099.2
  let h1064_1099 := h1063_1099.2
  have h1064 : constraint_1064 air row := h1064_1099.1
  let h1065_1099 := h1064_1099.2
  let h1066_1099 := h1065_1099.2
  let h1067_1099 := h1066_1099.2
  have h1067 : constraint_1067 air row := h1067_1099.1
  let h1068_1099 := h1067_1099.2
  let h1069_1099 := h1068_1099.2
  let h1070_1099 := h1069_1099.2
  have h1070 : constraint_1070 air row := h1070_1099.1
  let h1071_1099 := h1070_1099.2
  let h1072_1099 := h1071_1099.2
  let h1073_1099 := h1072_1099.2
  have h1073 : constraint_1073 air row := h1073_1099.1
  interval_cases limb
  · have hraw :
        next_intermed_4 air 0 0 row -
          ((msg_schedule_w air 0 0 row + msg_schedule_w air 0 1 row * 2 +
              msg_schedule_w air 0 2 row * 4 + msg_schedule_w air 0 3 row * 8 +
              msg_schedule_w air 0 4 row * 16 + msg_schedule_w air 0 5 row * 32 +
              msg_schedule_w air 0 6 row * 64 + msg_schedule_w air 0 7 row * 128 +
              msg_schedule_w air 0 8 row * 256 + msg_schedule_w air 0 9 row * 512 +
              msg_schedule_w air 0 10 row * 1024 + msg_schedule_w air 0 11 row * 2048 +
              msg_schedule_w air 0 12 row * 4096 + msg_schedule_w air 0 13 row * 8192 +
              msg_schedule_w air 0 14 row * 16384 + msg_schedule_w air 0 15 row * 32768) +
            raw_concat_schedule_small_sigma0_u16_limb air 1 0 row) = 0 := by
      rw [raw_concat_schedule_small_sigma0_u16_limb]
      have h1064' := h1064
      simp [constraint_1064, next_intermed_4, msg_schedule_w,
        raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
        Finset.sum_range_succ, zero_add] at h1064' ⊢
      ring_nf at h1064' ⊢
      exact h1064'
    have hpoly :
        next_intermed_4 air 0 0 row -
          (msg_schedule_u16_limb air 0 0 row +
            raw_concat_schedule_small_sigma0_u16_limb air 1 0 row) = 0 := by
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 0 0 row hvalid] at hpoly
    exact intermed_4_from_poly air row 0 0 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 0 1 row -
          (msg_schedule_u16_limb air 0 1 row +
            raw_concat_schedule_small_sigma0_u16_limb air 1 1 row) = 0 := by
      have hraw :
          next_intermed_4 air 0 1 row -
            ((msg_schedule_w air 0 16 row + msg_schedule_w air 0 17 row * 2 +
                msg_schedule_w air 0 18 row * 4 + msg_schedule_w air 0 19 row * 8 +
                msg_schedule_w air 0 20 row * 16 + msg_schedule_w air 0 21 row * 32 +
                msg_schedule_w air 0 22 row * 64 + msg_schedule_w air 0 23 row * 128 +
                msg_schedule_w air 0 24 row * 256 + msg_schedule_w air 0 25 row * 512 +
                msg_schedule_w air 0 26 row * 1024 + msg_schedule_w air 0 27 row * 2048 +
                msg_schedule_w air 0 28 row * 4096 + msg_schedule_w air 0 29 row * 8192 +
                msg_schedule_w air 0 30 row * 16384 + msg_schedule_w air 0 31 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 1 1 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1067' := h1067
        simp [constraint_1067, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1067' ⊢
        ring_nf at h1067' ⊢
        exact h1067'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 0 1 row hvalid] at hpoly
    exact intermed_4_from_poly air row 0 1 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 0 2 row -
          (msg_schedule_u16_limb air 0 2 row +
            raw_concat_schedule_small_sigma0_u16_limb air 1 2 row) = 0 := by
      have hraw :
          next_intermed_4 air 0 2 row -
            ((msg_schedule_w air 0 32 row + msg_schedule_w air 0 33 row * 2 +
                msg_schedule_w air 0 34 row * 4 + msg_schedule_w air 0 35 row * 8 +
                msg_schedule_w air 0 36 row * 16 + msg_schedule_w air 0 37 row * 32 +
                msg_schedule_w air 0 38 row * 64 + msg_schedule_w air 0 39 row * 128 +
                msg_schedule_w air 0 40 row * 256 + msg_schedule_w air 0 41 row * 512 +
                msg_schedule_w air 0 42 row * 1024 + msg_schedule_w air 0 43 row * 2048 +
                msg_schedule_w air 0 44 row * 4096 + msg_schedule_w air 0 45 row * 8192 +
                msg_schedule_w air 0 46 row * 16384 + msg_schedule_w air 0 47 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 1 2 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1070' := h1070
        simp [constraint_1070, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1070' ⊢
        ring_nf at h1070' ⊢
        exact h1070'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 0 2 row hvalid] at hpoly
    exact intermed_4_from_poly air row 0 2 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 0 3 row -
          (msg_schedule_u16_limb air 0 3 row +
            raw_concat_schedule_small_sigma0_u16_limb air 1 3 row) = 0 := by
      have hraw :
          next_intermed_4 air 0 3 row -
            ((msg_schedule_w air 0 48 row + msg_schedule_w air 0 49 row * 2 +
                msg_schedule_w air 0 50 row * 4 + msg_schedule_w air 0 51 row * 8 +
                msg_schedule_w air 0 52 row * 16 + msg_schedule_w air 0 53 row * 32 +
                msg_schedule_w air 0 54 row * 64 + msg_schedule_w air 0 55 row * 128 +
                msg_schedule_w air 0 56 row * 256 + msg_schedule_w air 0 57 row * 512 +
                msg_schedule_w air 0 58 row * 1024 + msg_schedule_w air 0 59 row * 2048 +
                msg_schedule_w air 0 60 row * 4096 + msg_schedule_w air 0 61 row * 8192 +
                msg_schedule_w air 0 62 row * 16384 + msg_schedule_w air 0 63 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 1 3 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1073' := h1073
        simp [constraint_1073, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1073' ⊢
        ring_nf at h1073' ⊢
        exact h1073'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 0 3 row hvalid] at hpoly
    exact intermed_4_from_poly air row 0 3 (by decide) (by decide) hslot_next hpoly

private theorem intermed_4_correct_slot1 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row) :
    intermed_4 air 1 limb (nextRow air row) =
      concatScheduleU16Limb air row 1 limb +
        composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air row 2))
          ⟨limb, hlimb⟩ := by
  have hvalid : row ≤ Circuit.last_row air := hrow.le
  have hslot_next :
      rawConcatScheduleBitsWord air row 2 =
        concatScheduleBitsWord air row 2 := by
    simpa using rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 2 hrot hvalid
  rcases hs with ⟨h1050_1099, _, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1050_1099 at h1050_1099
  let h1052_1099 := h1050_1099.2.2
  let h1053_1099 := h1052_1099.2
  let h1054_1099 := h1053_1099.2
  let h1055_1099 := h1054_1099.2
  let h1056_1099 := h1055_1099.2
  let h1057_1099 := h1056_1099.2
  let h1058_1099 := h1057_1099.2
  let h1059_1099 := h1058_1099.2
  let h1060_1099 := h1059_1099.2
  let h1061_1099 := h1060_1099.2
  let h1062_1099 := h1061_1099.2
  let h1063_1099 := h1062_1099.2
  let h1064_1099 := h1063_1099.2
  let h1065_1099 := h1064_1099.2
  let h1066_1099 := h1065_1099.2
  let h1067_1099 := h1066_1099.2
  let h1068_1099 := h1067_1099.2
  let h1069_1099 := h1068_1099.2
  let h1070_1099 := h1069_1099.2
  let h1071_1099 := h1070_1099.2
  let h1072_1099 := h1071_1099.2
  let h1073_1099 := h1072_1099.2
  let h1074_1099 := h1073_1099.2
  let h1075_1099 := h1074_1099.2
  let h1076_1099 := h1075_1099.2
  have h1076 : constraint_1076 air row := h1076_1099.1
  let h1077_1099 := h1076_1099.2
  let h1078_1099 := h1077_1099.2
  let h1079_1099 := h1078_1099.2
  have h1079 : constraint_1079 air row := h1079_1099.1
  let h1080_1099 := h1079_1099.2
  let h1081_1099 := h1080_1099.2
  let h1082_1099 := h1081_1099.2
  have h1082 : constraint_1082 air row := h1082_1099.1
  let h1083_1099 := h1082_1099.2
  let h1084_1099 := h1083_1099.2
  let h1085_1099 := h1084_1099.2
  have h1085 : constraint_1085 air row := h1085_1099.1
  interval_cases limb
  · have hpoly :
        next_intermed_4 air 1 0 row -
          (msg_schedule_u16_limb air 1 0 row +
            raw_concat_schedule_small_sigma0_u16_limb air 2 0 row) = 0 := by
      have hraw :
          next_intermed_4 air 1 0 row -
            ((msg_schedule_w air 1 0 row + msg_schedule_w air 1 1 row * 2 +
                msg_schedule_w air 1 2 row * 4 + msg_schedule_w air 1 3 row * 8 +
                msg_schedule_w air 1 4 row * 16 + msg_schedule_w air 1 5 row * 32 +
                msg_schedule_w air 1 6 row * 64 + msg_schedule_w air 1 7 row * 128 +
                msg_schedule_w air 1 8 row * 256 + msg_schedule_w air 1 9 row * 512 +
                msg_schedule_w air 1 10 row * 1024 + msg_schedule_w air 1 11 row * 2048 +
                msg_schedule_w air 1 12 row * 4096 + msg_schedule_w air 1 13 row * 8192 +
                msg_schedule_w air 1 14 row * 16384 + msg_schedule_w air 1 15 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 2 0 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1076' := h1076
        simp [constraint_1076, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1076' ⊢
        ring_nf at h1076' ⊢
        exact h1076'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 1 0 row hvalid] at hpoly
    exact intermed_4_from_poly air row 1 0 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 1 1 row -
          (msg_schedule_u16_limb air 1 1 row +
            raw_concat_schedule_small_sigma0_u16_limb air 2 1 row) = 0 := by
      have hraw :
          next_intermed_4 air 1 1 row -
            ((msg_schedule_w air 1 16 row + msg_schedule_w air 1 17 row * 2 +
                msg_schedule_w air 1 18 row * 4 + msg_schedule_w air 1 19 row * 8 +
                msg_schedule_w air 1 20 row * 16 + msg_schedule_w air 1 21 row * 32 +
                msg_schedule_w air 1 22 row * 64 + msg_schedule_w air 1 23 row * 128 +
                msg_schedule_w air 1 24 row * 256 + msg_schedule_w air 1 25 row * 512 +
                msg_schedule_w air 1 26 row * 1024 + msg_schedule_w air 1 27 row * 2048 +
                msg_schedule_w air 1 28 row * 4096 + msg_schedule_w air 1 29 row * 8192 +
                msg_schedule_w air 1 30 row * 16384 + msg_schedule_w air 1 31 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 2 1 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1079' := h1079
        simp [constraint_1079, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1079' ⊢
        ring_nf at h1079' ⊢
        exact h1079'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 1 1 row hvalid] at hpoly
    exact intermed_4_from_poly air row 1 1 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 1 2 row -
          (msg_schedule_u16_limb air 1 2 row +
            raw_concat_schedule_small_sigma0_u16_limb air 2 2 row) = 0 := by
      have hraw :
          next_intermed_4 air 1 2 row -
            ((msg_schedule_w air 1 32 row + msg_schedule_w air 1 33 row * 2 +
                msg_schedule_w air 1 34 row * 4 + msg_schedule_w air 1 35 row * 8 +
                msg_schedule_w air 1 36 row * 16 + msg_schedule_w air 1 37 row * 32 +
                msg_schedule_w air 1 38 row * 64 + msg_schedule_w air 1 39 row * 128 +
                msg_schedule_w air 1 40 row * 256 + msg_schedule_w air 1 41 row * 512 +
                msg_schedule_w air 1 42 row * 1024 + msg_schedule_w air 1 43 row * 2048 +
                msg_schedule_w air 1 44 row * 4096 + msg_schedule_w air 1 45 row * 8192 +
                msg_schedule_w air 1 46 row * 16384 + msg_schedule_w air 1 47 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 2 2 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1082' := h1082
        simp [constraint_1082, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1082' ⊢
        ring_nf at h1082' ⊢
        exact h1082'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 1 2 row hvalid] at hpoly
    exact intermed_4_from_poly air row 1 2 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 1 3 row -
          (msg_schedule_u16_limb air 1 3 row +
            raw_concat_schedule_small_sigma0_u16_limb air 2 3 row) = 0 := by
      have hraw :
          next_intermed_4 air 1 3 row -
            ((msg_schedule_w air 1 48 row + msg_schedule_w air 1 49 row * 2 +
                msg_schedule_w air 1 50 row * 4 + msg_schedule_w air 1 51 row * 8 +
                msg_schedule_w air 1 52 row * 16 + msg_schedule_w air 1 53 row * 32 +
                msg_schedule_w air 1 54 row * 64 + msg_schedule_w air 1 55 row * 128 +
                msg_schedule_w air 1 56 row * 256 + msg_schedule_w air 1 57 row * 512 +
                msg_schedule_w air 1 58 row * 1024 + msg_schedule_w air 1 59 row * 2048 +
                msg_schedule_w air 1 60 row * 4096 + msg_schedule_w air 1 61 row * 8192 +
                msg_schedule_w air 1 62 row * 16384 + msg_schedule_w air 1 63 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 2 3 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1085' := h1085
        simp [constraint_1085, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1085' ⊢
        ring_nf at h1085' ⊢
        exact h1085'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 1 3 row hvalid] at hpoly
    exact intermed_4_from_poly air row 1 3 (by decide) (by decide) hslot_next hpoly

private theorem intermed_4_correct_slot2 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row) :
    intermed_4 air 2 limb (nextRow air row) =
      concatScheduleU16Limb air row 2 limb +
        composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air row 3))
          ⟨limb, hlimb⟩ := by
  have hvalid : row ≤ Circuit.last_row air := hrow.le
  have hslot_next :
      rawConcatScheduleBitsWord air row 3 =
        concatScheduleBitsWord air row 3 := by
    simpa using rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 3 hrot hvalid
  rcases hs with ⟨h1050_1099, _, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1050_1099 at h1050_1099
  let h1052_1099 := h1050_1099.2.2
  let h1053_1099 := h1052_1099.2
  let h1054_1099 := h1053_1099.2
  let h1055_1099 := h1054_1099.2
  let h1056_1099 := h1055_1099.2
  let h1057_1099 := h1056_1099.2
  let h1058_1099 := h1057_1099.2
  let h1059_1099 := h1058_1099.2
  let h1060_1099 := h1059_1099.2
  let h1061_1099 := h1060_1099.2
  let h1062_1099 := h1061_1099.2
  let h1063_1099 := h1062_1099.2
  let h1064_1099 := h1063_1099.2
  let h1065_1099 := h1064_1099.2
  let h1066_1099 := h1065_1099.2
  let h1067_1099 := h1066_1099.2
  let h1068_1099 := h1067_1099.2
  let h1069_1099 := h1068_1099.2
  let h1070_1099 := h1069_1099.2
  let h1071_1099 := h1070_1099.2
  let h1072_1099 := h1071_1099.2
  let h1073_1099 := h1072_1099.2
  let h1074_1099 := h1073_1099.2
  let h1075_1099 := h1074_1099.2
  let h1076_1099 := h1075_1099.2
  let h1077_1099 := h1076_1099.2
  let h1078_1099 := h1077_1099.2
  let h1079_1099 := h1078_1099.2
  let h1080_1099 := h1079_1099.2
  let h1081_1099 := h1080_1099.2
  let h1082_1099 := h1081_1099.2
  let h1083_1099 := h1082_1099.2
  let h1084_1099 := h1083_1099.2
  let h1085_1099 := h1084_1099.2
  let h1086_1099 := h1085_1099.2
  let h1087_1099 := h1086_1099.2
  let h1088_1099 := h1087_1099.2
  have h1088 : constraint_1088 air row := h1088_1099.1
  let h1089_1099 := h1088_1099.2
  let h1090_1099 := h1089_1099.2
  let h1091_1099 := h1090_1099.2
  have h1091 : constraint_1091 air row := h1091_1099.1
  let h1092_1099 := h1091_1099.2
  let h1093_1099 := h1092_1099.2
  let h1094_1099 := h1093_1099.2
  have h1094 : constraint_1094 air row := h1094_1099.1
  let h1095_1099 := h1094_1099.2
  let h1096_1099 := h1095_1099.2
  let h1097_1099 := h1096_1099.2
  have h1097 : constraint_1097 air row := h1097_1099.1
  interval_cases limb
  · have hpoly :
        next_intermed_4 air 2 0 row -
          (msg_schedule_u16_limb air 2 0 row +
            raw_concat_schedule_small_sigma0_u16_limb air 3 0 row) = 0 := by
      have hraw :
          next_intermed_4 air 2 0 row -
            ((msg_schedule_w air 2 0 row + msg_schedule_w air 2 1 row * 2 +
                msg_schedule_w air 2 2 row * 4 + msg_schedule_w air 2 3 row * 8 +
                msg_schedule_w air 2 4 row * 16 + msg_schedule_w air 2 5 row * 32 +
                msg_schedule_w air 2 6 row * 64 + msg_schedule_w air 2 7 row * 128 +
                msg_schedule_w air 2 8 row * 256 + msg_schedule_w air 2 9 row * 512 +
                msg_schedule_w air 2 10 row * 1024 + msg_schedule_w air 2 11 row * 2048 +
                msg_schedule_w air 2 12 row * 4096 + msg_schedule_w air 2 13 row * 8192 +
                msg_schedule_w air 2 14 row * 16384 + msg_schedule_w air 2 15 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 3 0 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1088' := h1088
        simp [constraint_1088, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1088' ⊢
        ring_nf at h1088' ⊢
        exact h1088'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 2 0 row hvalid] at hpoly
    exact intermed_4_from_poly air row 2 0 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 2 1 row -
          (msg_schedule_u16_limb air 2 1 row +
            raw_concat_schedule_small_sigma0_u16_limb air 3 1 row) = 0 := by
      have hraw :
          next_intermed_4 air 2 1 row -
            ((msg_schedule_w air 2 16 row + msg_schedule_w air 2 17 row * 2 +
                msg_schedule_w air 2 18 row * 4 + msg_schedule_w air 2 19 row * 8 +
                msg_schedule_w air 2 20 row * 16 + msg_schedule_w air 2 21 row * 32 +
                msg_schedule_w air 2 22 row * 64 + msg_schedule_w air 2 23 row * 128 +
                msg_schedule_w air 2 24 row * 256 + msg_schedule_w air 2 25 row * 512 +
                msg_schedule_w air 2 26 row * 1024 + msg_schedule_w air 2 27 row * 2048 +
                msg_schedule_w air 2 28 row * 4096 + msg_schedule_w air 2 29 row * 8192 +
                msg_schedule_w air 2 30 row * 16384 + msg_schedule_w air 2 31 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 3 1 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1091' := h1091
        simp [constraint_1091, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1091' ⊢
        ring_nf at h1091' ⊢
        exact h1091'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 2 1 row hvalid] at hpoly
    exact intermed_4_from_poly air row 2 1 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 2 2 row -
          (msg_schedule_u16_limb air 2 2 row +
            raw_concat_schedule_small_sigma0_u16_limb air 3 2 row) = 0 := by
      have hraw :
          next_intermed_4 air 2 2 row -
            ((msg_schedule_w air 2 32 row + msg_schedule_w air 2 33 row * 2 +
                msg_schedule_w air 2 34 row * 4 + msg_schedule_w air 2 35 row * 8 +
                msg_schedule_w air 2 36 row * 16 + msg_schedule_w air 2 37 row * 32 +
                msg_schedule_w air 2 38 row * 64 + msg_schedule_w air 2 39 row * 128 +
                msg_schedule_w air 2 40 row * 256 + msg_schedule_w air 2 41 row * 512 +
                msg_schedule_w air 2 42 row * 1024 + msg_schedule_w air 2 43 row * 2048 +
                msg_schedule_w air 2 44 row * 4096 + msg_schedule_w air 2 45 row * 8192 +
                msg_schedule_w air 2 46 row * 16384 + msg_schedule_w air 2 47 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 3 2 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1094' := h1094
        simp [constraint_1094, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1094' ⊢
        ring_nf at h1094' ⊢
        exact h1094'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 2 2 row hvalid] at hpoly
    exact intermed_4_from_poly air row 2 2 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 2 3 row -
          (msg_schedule_u16_limb air 2 3 row +
            raw_concat_schedule_small_sigma0_u16_limb air 3 3 row) = 0 := by
      have hraw :
          next_intermed_4 air 2 3 row -
            ((msg_schedule_w air 2 48 row + msg_schedule_w air 2 49 row * 2 +
                msg_schedule_w air 2 50 row * 4 + msg_schedule_w air 2 51 row * 8 +
                msg_schedule_w air 2 52 row * 16 + msg_schedule_w air 2 53 row * 32 +
                msg_schedule_w air 2 54 row * 64 + msg_schedule_w air 2 55 row * 128 +
                msg_schedule_w air 2 56 row * 256 + msg_schedule_w air 2 57 row * 512 +
                msg_schedule_w air 2 58 row * 1024 + msg_schedule_w air 2 59 row * 2048 +
                msg_schedule_w air 2 60 row * 4096 + msg_schedule_w air 2 61 row * 8192 +
                msg_schedule_w air 2 62 row * 16384 + msg_schedule_w air 2 63 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 3 3 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1097' := h1097
        simp [constraint_1097, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1097' ⊢
        ring_nf at h1097' ⊢
        exact h1097'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 2 3 row hvalid] at hpoly
    exact intermed_4_from_poly air row 2 3 (by decide) (by decide) hslot_next hpoly

private theorem intermed_4_correct_slot3 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row) :
    intermed_4 air 3 limb (nextRow air row) =
      concatScheduleU16Limb air row 3 limb +
        composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air row 4))
          ⟨limb, hlimb⟩ := by
  have hvalid : row ≤ Circuit.last_row air := hrow.le
  have hslot_next :
      rawConcatScheduleBitsWord air row 4 =
        concatScheduleBitsWord air row 4 := by
    simpa using rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 4 hrot hvalid
  rcases hs with ⟨_, h1100_1149, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1100_1149 at h1100_1149
  have h1100 : constraint_1100 air row := h1100_1149.1
  let h1101_1149 := h1100_1149.2
  let h1102_1149 := h1101_1149.2
  let h1103_1149 := h1102_1149.2
  have h1103 : constraint_1103 air row := h1103_1149.1
  let h1104_1149 := h1103_1149.2
  let h1105_1149 := h1104_1149.2
  let h1106_1149 := h1105_1149.2
  have h1106 : constraint_1106 air row := h1106_1149.1
  let h1107_1149 := h1106_1149.2
  let h1108_1149 := h1107_1149.2
  let h1109_1149 := h1108_1149.2
  have h1109 : constraint_1109 air row := h1109_1149.1
  interval_cases limb
  · have hpoly :
        next_intermed_4 air 3 0 row -
          (msg_schedule_u16_limb air 3 0 row +
            raw_concat_schedule_small_sigma0_u16_limb air 4 0 row) = 0 := by
      have hraw :
          next_intermed_4 air 3 0 row -
            ((msg_schedule_w air 3 0 row + msg_schedule_w air 3 1 row * 2 +
                msg_schedule_w air 3 2 row * 4 + msg_schedule_w air 3 3 row * 8 +
                msg_schedule_w air 3 4 row * 16 + msg_schedule_w air 3 5 row * 32 +
                msg_schedule_w air 3 6 row * 64 + msg_schedule_w air 3 7 row * 128 +
                msg_schedule_w air 3 8 row * 256 + msg_schedule_w air 3 9 row * 512 +
                msg_schedule_w air 3 10 row * 1024 + msg_schedule_w air 3 11 row * 2048 +
                msg_schedule_w air 3 12 row * 4096 + msg_schedule_w air 3 13 row * 8192 +
                msg_schedule_w air 3 14 row * 16384 + msg_schedule_w air 3 15 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 4 0 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1100' := h1100
        simp [constraint_1100, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1100' ⊢
        ring_nf at h1100' ⊢
        exact h1100'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 3 0 row hvalid] at hpoly
    exact intermed_4_from_poly air row 3 0 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 3 1 row -
          (msg_schedule_u16_limb air 3 1 row +
            raw_concat_schedule_small_sigma0_u16_limb air 4 1 row) = 0 := by
      have hraw :
          next_intermed_4 air 3 1 row -
            ((msg_schedule_w air 3 16 row + msg_schedule_w air 3 17 row * 2 +
                msg_schedule_w air 3 18 row * 4 + msg_schedule_w air 3 19 row * 8 +
                msg_schedule_w air 3 20 row * 16 + msg_schedule_w air 3 21 row * 32 +
                msg_schedule_w air 3 22 row * 64 + msg_schedule_w air 3 23 row * 128 +
                msg_schedule_w air 3 24 row * 256 + msg_schedule_w air 3 25 row * 512 +
                msg_schedule_w air 3 26 row * 1024 + msg_schedule_w air 3 27 row * 2048 +
                msg_schedule_w air 3 28 row * 4096 + msg_schedule_w air 3 29 row * 8192 +
                msg_schedule_w air 3 30 row * 16384 + msg_schedule_w air 3 31 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 4 1 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1103' := h1103
        simp [constraint_1103, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1103' ⊢
        ring_nf at h1103' ⊢
        exact h1103'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 3 1 row hvalid] at hpoly
    exact intermed_4_from_poly air row 3 1 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 3 2 row -
          (msg_schedule_u16_limb air 3 2 row +
            raw_concat_schedule_small_sigma0_u16_limb air 4 2 row) = 0 := by
      have hraw :
          next_intermed_4 air 3 2 row -
            ((msg_schedule_w air 3 32 row + msg_schedule_w air 3 33 row * 2 +
                msg_schedule_w air 3 34 row * 4 + msg_schedule_w air 3 35 row * 8 +
                msg_schedule_w air 3 36 row * 16 + msg_schedule_w air 3 37 row * 32 +
                msg_schedule_w air 3 38 row * 64 + msg_schedule_w air 3 39 row * 128 +
                msg_schedule_w air 3 40 row * 256 + msg_schedule_w air 3 41 row * 512 +
                msg_schedule_w air 3 42 row * 1024 + msg_schedule_w air 3 43 row * 2048 +
                msg_schedule_w air 3 44 row * 4096 + msg_schedule_w air 3 45 row * 8192 +
                msg_schedule_w air 3 46 row * 16384 + msg_schedule_w air 3 47 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 4 2 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1106' := h1106
        simp [constraint_1106, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1106' ⊢
        ring_nf at h1106' ⊢
        exact h1106'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 3 2 row hvalid] at hpoly
    exact intermed_4_from_poly air row 3 2 (by decide) (by decide) hslot_next hpoly
  · have hpoly :
        next_intermed_4 air 3 3 row -
          (msg_schedule_u16_limb air 3 3 row +
            raw_concat_schedule_small_sigma0_u16_limb air 4 3 row) = 0 := by
      have hraw :
          next_intermed_4 air 3 3 row -
            ((msg_schedule_w air 3 48 row + msg_schedule_w air 3 49 row * 2 +
                msg_schedule_w air 3 50 row * 4 + msg_schedule_w air 3 51 row * 8 +
                msg_schedule_w air 3 52 row * 16 + msg_schedule_w air 3 53 row * 32 +
                msg_schedule_w air 3 54 row * 64 + msg_schedule_w air 3 55 row * 128 +
                msg_schedule_w air 3 56 row * 256 + msg_schedule_w air 3 57 row * 512 +
                msg_schedule_w air 3 58 row * 1024 + msg_schedule_w air 3 59 row * 2048 +
                msg_schedule_w air 3 60 row * 4096 + msg_schedule_w air 3 61 row * 8192 +
                msg_schedule_w air 3 62 row * 16384 + msg_schedule_w air 3 63 row * 32768) +
              raw_concat_schedule_small_sigma0_u16_limb air 4 3 row) = 0 := by
        rw [raw_concat_schedule_small_sigma0_u16_limb]
        have h1109' := h1109
        simp [constraint_1109, next_intermed_4, msg_schedule_w,
          raw_concat_schedule_small_sigma0_bit, raw_concat_schedule_bit, field_xor_expr,
          Finset.sum_range_succ, zero_add] at h1109' ⊢
        ring_nf at h1109' ⊢
        exact h1109'
      rw [msg_schedule_u16_limb]
      simpa [Finset.sum_range_succ] using hraw
    rw [next_intermed_4_eq_nextRow air hrot 3 3 row hvalid] at hpoly
    exact intermed_4_from_poly air row 3 3 (by decide) (by decide) hslot_next hpoly

/-- Transport the raw `intermed_4` equality onto the actual successor row. -/
theorem intermed_4_correct (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row) :
    intermed_4 air slot limb (nextRow air row) =
      concatScheduleU16Limb air row slot limb +
        composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air row (slot + 1)))
          ⟨limb, hlimb⟩ := by
  interval_cases slot
  · simpa using intermed_4_correct_slot0 air row limb hlimb hrow hrot hs
  · simpa using intermed_4_correct_slot1 air row limb hlimb hrow hrot hs
  · simpa using intermed_4_correct_slot2 air row limb hlimb hrow hrot hs
  · simpa using intermed_4_correct_slot3 air row limb hlimb hrow hrot hs


end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
