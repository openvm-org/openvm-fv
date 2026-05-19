/-
  Layer B: Message Schedule Correctness (Core)

  Proves that the message-schedule slice of `schedule_constraints` over a block
  window implies the trace's schedule words match `expandSchedule`.

  Part 1 covers:
  - B2: w_3 helper correctness (constraints 539–544)
  - B3: Intermediate accumulator pipeline (constraints 545–568)

  Bit booleanness (B1) lives in `BitBounds.lean`.

  Depends on: FieldArithmetic, BaseFacts, BitBounds
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.FieldArithmetic
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.BaseFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.MessageSchedule.BitBounds
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.MessageSchedule.CarryGates
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.Defs

set_option autoImplicit false

set_option maxHeartbeats 3000000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## B2: w_3 helper correctness (constraints 539–544) -/

private theorem schedule_lo16_range_eq (air : C FBB ExtF) (row slot : ℕ) :
    composeLo16 (scheduleBitsWord air row slot) =
      ∑ x ∈ Finset.range 16, msg_schedule_w air slot x row * 2 ^ x := by
  have hsum :
      (∑ x : Fin 16, msg_schedule_w air slot x.val row * 2 ^ x.val) =
        ∑ x ∈ Finset.range 16, msg_schedule_w air slot x row * 2 ^ x := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun x => msg_schedule_w air slot x row * 2 ^ x)
        (n := 16))
  simpa [composeLo16, scheduleBitsWord] using hsum.symm

private theorem schedule_hi16_range_eq (air : C FBB ExtF) (row slot : ℕ) :
    composeHi16 (scheduleBitsWord air row slot) =
      ∑ x ∈ Finset.range 16, msg_schedule_w air slot (x + 16) row * 2 ^ x := by
  have hsum :
      (∑ x : Fin 16, msg_schedule_w air slot (x.val + 16) row * 2 ^ x.val) =
        ∑ x ∈ Finset.range 16, msg_schedule_w air slot (x + 16) row * 2 ^ x := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun x => msg_schedule_w air slot (x + 16) row * 2 ^ x)
        (n := 16))
  simpa [composeHi16, scheduleBitsWord] using hsum.symm

private theorem concatScheduleLo16_local_eq (air : C FBB ExtF) (row slot : ℕ)
    (hslot : slot < 4) :
    concatScheduleLo16 air row slot =
      ∑ x ∈ Finset.range 16, msg_schedule_w air slot x row * 2 ^ x := by
  simp [concatScheduleLo16, concatScheduleBitsWord, hslot, schedule_lo16_range_eq]

private theorem concatScheduleHi16_local_eq (air : C FBB ExtF) (row slot : ℕ)
    (hslot : slot < 4) :
    concatScheduleHi16 air row slot =
      ∑ x ∈ Finset.range 16, msg_schedule_w air slot (x + 16) row * 2 ^ x := by
  simp [concatScheduleHi16, concatScheduleBitsWord, hslot, schedule_hi16_range_eq]

private theorem w3_helper_correct_raw (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 3) (hlimb : limb < 2)
    (hs : schedule_constraints air row)
    (hround : is_round_row air row = 1) :
    next_schedule_helper_w_3 air slot limb row =
      (if limb = 0 then concatScheduleLo16 air row (slot + 1)
       else concatScheduleHi16 air row (slot + 1)) := by
  have h539_549 := constraints_539_549_of_schedule_constraints air row hs
  unfold constraints_539_549 at h539_549
  interval_cases slot <;> interval_cases limb
  · have h539 : constraint_539 air row := by tauto
    have hraw :
        msg_schedule_w air 1 0 row + msg_schedule_w air 1 1 row * 2 +
            msg_schedule_w air 1 2 row * 4 + msg_schedule_w air 1 3 row * 8 +
            msg_schedule_w air 1 4 row * 16 + msg_schedule_w air 1 5 row * 32 +
            msg_schedule_w air 1 6 row * 64 + msg_schedule_w air 1 7 row * 128 +
            msg_schedule_w air 1 8 row * 256 + msg_schedule_w air 1 9 row * 512 +
            msg_schedule_w air 1 10 row * 1024 + msg_schedule_w air 1 11 row * 2048 +
            msg_schedule_w air 1 12 row * 4096 + msg_schedule_w air 1 13 row * 8192 +
            msg_schedule_w air 1 14 row * 16384 + msg_schedule_w air 1 15 row * 32768 -
          next_schedule_helper_w_3 air 0 0 row = 0 := by
      simpa [constraint_539, hround] using h539
    have hrange :
        (∑ x ∈ Finset.range 16, msg_schedule_w air 1 x row * 2 ^ x) -
          next_schedule_helper_w_3 air 0 0 row = 0 := by
      simpa [Finset.sum_range_succ] using hraw
    have hsum :
        concatScheduleLo16 air row 1 - next_schedule_helper_w_3 air 0 0 row = 0 := by
      rw [concatScheduleLo16_local_eq air row 1 (by omega)]
      exact hrange
    exact (sub_eq_zero.mp hsum).symm
  · have h540 : constraint_540 air row := by tauto
    have hraw :
        msg_schedule_w air 1 16 row + msg_schedule_w air 1 17 row * 2 +
            msg_schedule_w air 1 18 row * 4 + msg_schedule_w air 1 19 row * 8 +
            msg_schedule_w air 1 20 row * 16 + msg_schedule_w air 1 21 row * 32 +
            msg_schedule_w air 1 22 row * 64 + msg_schedule_w air 1 23 row * 128 +
            msg_schedule_w air 1 24 row * 256 + msg_schedule_w air 1 25 row * 512 +
            msg_schedule_w air 1 26 row * 1024 + msg_schedule_w air 1 27 row * 2048 +
            msg_schedule_w air 1 28 row * 4096 + msg_schedule_w air 1 29 row * 8192 +
            msg_schedule_w air 1 30 row * 16384 + msg_schedule_w air 1 31 row * 32768 -
          next_schedule_helper_w_3 air 0 1 row = 0 := by
      simpa [constraint_540, hround] using h540
    have hrange :
        (∑ x ∈ Finset.range 16, msg_schedule_w air 1 (x + 16) row * 2 ^ x) -
          next_schedule_helper_w_3 air 0 1 row = 0 := by
      simpa [Finset.sum_range_succ] using hraw
    have hsum :
        concatScheduleHi16 air row 1 - next_schedule_helper_w_3 air 0 1 row = 0 := by
      rw [concatScheduleHi16_local_eq air row 1 (by omega)]
      exact hrange
    exact (sub_eq_zero.mp hsum).symm
  · have h541 : constraint_541 air row := by tauto
    have hraw :
        msg_schedule_w air 2 0 row + msg_schedule_w air 2 1 row * 2 +
            msg_schedule_w air 2 2 row * 4 + msg_schedule_w air 2 3 row * 8 +
            msg_schedule_w air 2 4 row * 16 + msg_schedule_w air 2 5 row * 32 +
            msg_schedule_w air 2 6 row * 64 + msg_schedule_w air 2 7 row * 128 +
            msg_schedule_w air 2 8 row * 256 + msg_schedule_w air 2 9 row * 512 +
            msg_schedule_w air 2 10 row * 1024 + msg_schedule_w air 2 11 row * 2048 +
            msg_schedule_w air 2 12 row * 4096 + msg_schedule_w air 2 13 row * 8192 +
            msg_schedule_w air 2 14 row * 16384 + msg_schedule_w air 2 15 row * 32768 -
          next_schedule_helper_w_3 air 1 0 row = 0 := by
      simpa [constraint_541, hround] using h541
    have hrange :
        (∑ x ∈ Finset.range 16, msg_schedule_w air 2 x row * 2 ^ x) -
          next_schedule_helper_w_3 air 1 0 row = 0 := by
      simpa [Finset.sum_range_succ] using hraw
    have hsum :
        concatScheduleLo16 air row 2 - next_schedule_helper_w_3 air 1 0 row = 0 := by
      rw [concatScheduleLo16_local_eq air row 2 (by omega)]
      exact hrange
    exact (sub_eq_zero.mp hsum).symm
  · have h542 : constraint_542 air row := by tauto
    have hraw :
        msg_schedule_w air 2 16 row + msg_schedule_w air 2 17 row * 2 +
            msg_schedule_w air 2 18 row * 4 + msg_schedule_w air 2 19 row * 8 +
            msg_schedule_w air 2 20 row * 16 + msg_schedule_w air 2 21 row * 32 +
            msg_schedule_w air 2 22 row * 64 + msg_schedule_w air 2 23 row * 128 +
            msg_schedule_w air 2 24 row * 256 + msg_schedule_w air 2 25 row * 512 +
            msg_schedule_w air 2 26 row * 1024 + msg_schedule_w air 2 27 row * 2048 +
            msg_schedule_w air 2 28 row * 4096 + msg_schedule_w air 2 29 row * 8192 +
            msg_schedule_w air 2 30 row * 16384 + msg_schedule_w air 2 31 row * 32768 -
          next_schedule_helper_w_3 air 1 1 row = 0 := by
      simpa [constraint_542, hround] using h542
    have hrange :
        (∑ x ∈ Finset.range 16, msg_schedule_w air 2 (x + 16) row * 2 ^ x) -
          next_schedule_helper_w_3 air 1 1 row = 0 := by
      simpa [Finset.sum_range_succ] using hraw
    have hsum :
        concatScheduleHi16 air row 2 - next_schedule_helper_w_3 air 1 1 row = 0 := by
      rw [concatScheduleHi16_local_eq air row 2 (by omega)]
      exact hrange
    exact (sub_eq_zero.mp hsum).symm
  · have h543 : constraint_543 air row := by tauto
    have hraw :
        msg_schedule_w air 3 0 row + msg_schedule_w air 3 1 row * 2 +
            msg_schedule_w air 3 2 row * 4 + msg_schedule_w air 3 3 row * 8 +
            msg_schedule_w air 3 4 row * 16 + msg_schedule_w air 3 5 row * 32 +
            msg_schedule_w air 3 6 row * 64 + msg_schedule_w air 3 7 row * 128 +
            msg_schedule_w air 3 8 row * 256 + msg_schedule_w air 3 9 row * 512 +
            msg_schedule_w air 3 10 row * 1024 + msg_schedule_w air 3 11 row * 2048 +
            msg_schedule_w air 3 12 row * 4096 + msg_schedule_w air 3 13 row * 8192 +
            msg_schedule_w air 3 14 row * 16384 + msg_schedule_w air 3 15 row * 32768 -
          next_schedule_helper_w_3 air 2 0 row = 0 := by
      simpa [constraint_543, hround] using h543
    have hrange :
        (∑ x ∈ Finset.range 16, msg_schedule_w air 3 x row * 2 ^ x) -
          next_schedule_helper_w_3 air 2 0 row = 0 := by
      simpa [Finset.sum_range_succ] using hraw
    have hsum :
        concatScheduleLo16 air row 3 - next_schedule_helper_w_3 air 2 0 row = 0 := by
      rw [concatScheduleLo16_local_eq air row 3 (by omega)]
      exact hrange
    exact (sub_eq_zero.mp hsum).symm
  · have h544 : constraint_544 air row := by tauto
    have hraw :
        msg_schedule_w air 3 16 row + msg_schedule_w air 3 17 row * 2 +
            msg_schedule_w air 3 18 row * 4 + msg_schedule_w air 3 19 row * 8 +
            msg_schedule_w air 3 20 row * 16 + msg_schedule_w air 3 21 row * 32 +
            msg_schedule_w air 3 22 row * 64 + msg_schedule_w air 3 23 row * 128 +
            msg_schedule_w air 3 24 row * 256 + msg_schedule_w air 3 25 row * 512 +
            msg_schedule_w air 3 26 row * 1024 + msg_schedule_w air 3 27 row * 2048 +
            msg_schedule_w air 3 28 row * 4096 + msg_schedule_w air 3 29 row * 8192 +
            msg_schedule_w air 3 30 row * 16384 + msg_schedule_w air 3 31 row * 32768 -
          next_schedule_helper_w_3 air 2 1 row = 0 := by
      simpa [constraint_544, hround] using h544
    have hrange :
        (∑ x ∈ Finset.range 16, msg_schedule_w air 3 (x + 16) row * 2 ^ x) -
          next_schedule_helper_w_3 air 2 1 row = 0 := by
      simpa [Finset.sum_range_succ] using hraw
    have hsum :
        concatScheduleHi16 air row 3 - next_schedule_helper_w_3 air 2 1 row = 0 := by
      rw [concatScheduleHi16_local_eq air row 3 (by omega)]
      exact hrange
    exact (sub_eq_zero.mp hsum).symm

/-- Combined w_3 helper for all 6 constraints: schedule_helper_w_3[s][l]
    on the next row = compose16 of w[s+1] on local. -/
theorem w3_helper_correct (air : C FBB ExtF) (row : ℕ) (slot : ℕ) (limb : ℕ)
    (hslot : slot < 3) (hlimb : limb < 2)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hround : is_round_row air row = 1) :
    schedule_helper_w_3 air slot limb (nextRow air row) =
      (if limb = 0 then concatScheduleLo16 air row (slot + 1)
       else concatScheduleHi16 air row (slot + 1)) := by
  have hraw := w3_helper_correct_raw air row slot limb hslot hlimb hs hround
  simpa [next_schedule_helper_w_3_eq_nextRow air hrot slot limb row hrow] using hraw

/-! ## B3: Intermediate accumulator pipeline (constraints 545–568) -/

/-- intermed_4 stores w[slot] + σ₀(w[slot+1]) limbs on the next row. -/
theorem intermed_4_correct (air : C FBB ExtF) (row : ℕ) (slot : ℕ) (limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 2)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    :
    let w_limb := if limb = 0 then concatScheduleLo16 air row slot
                  else concatScheduleHi16 air row slot
    let sig0_limb := if limb = 0
      then composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air row (slot + 1)))
      else composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air row (slot + 1)))
    intermed_4 air slot limb (nextRow air row) = w_limb + sig0_limb := by
  have hvalid : row ≤ Circuit.last_row air := hrow.le
  have hslot_next :
      rawConcatScheduleBitsWord air row (slot + 1) =
        concatScheduleBitsWord air row (slot + 1) :=
    rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row (slot + 1) hrot hvalid
  have h539_549 := constraints_539_549_of_schedule_constraints air row hs
  have h550_599 := constraints_550_599_of_schedule_constraints air row hs
  unfold constraints_539_549 at h539_549
  unfold constraints_550_599 at h550_599
  interval_cases slot <;> interval_cases limb
  · have h545 : constraint_545 air row := by tauto
    have hraw :
        intermed_4 air 0 0 (nextRow air row) -
          (concatScheduleLo16 air row 0 +
            composeLo16 (fieldSmallSigma0 (rawConcatScheduleBitsWord air row 1))) = 0 := by
      simpa [constraint_545, Circuit.isTransitionRow, hrow.ne,
        next_intermed_4_eq_nextRow air hrot 0 0 row hvalid, concatScheduleLo16,
        composeLo16_range_eq, scheduleBitsWord, rawConcatScheduleBitsWord, nextScheduleBitsWord,
        fieldSmallSigma0, fieldRotr, fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h545
    exact sub_eq_zero.mp (by simpa [hslot_next] using hraw)
  · have h548 : constraint_548 air row := by tauto
    have hraw :
        intermed_4 air 0 1 (nextRow air row) -
          (concatScheduleHi16 air row 0 +
            composeHi16 (fieldSmallSigma0 (rawConcatScheduleBitsWord air row 1))) = 0 := by
      simpa [constraint_548, Circuit.isTransitionRow, hrow.ne,
        next_intermed_4_eq_nextRow air hrot 0 1 row hvalid, concatScheduleHi16,
        composeHi16_range_eq, scheduleBitsWord, rawConcatScheduleBitsWord, nextScheduleBitsWord,
        fieldSmallSigma0, fieldRotr, fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h548
    exact sub_eq_zero.mp (by simpa [hslot_next] using hraw)
  · have h551 : constraint_551 air row := by tauto
    have hraw :
        intermed_4 air 1 0 (nextRow air row) -
          (concatScheduleLo16 air row 1 +
            composeLo16 (fieldSmallSigma0 (rawConcatScheduleBitsWord air row 2))) = 0 := by
      simpa [constraint_551, Circuit.isTransitionRow, hrow.ne,
        next_intermed_4_eq_nextRow air hrot 1 0 row hvalid, concatScheduleLo16,
        composeLo16_range_eq, scheduleBitsWord, rawConcatScheduleBitsWord, nextScheduleBitsWord,
        fieldSmallSigma0, fieldRotr, fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h551
    exact sub_eq_zero.mp (by simpa [hslot_next] using hraw)
  · have h554 : constraint_554 air row := by tauto
    have hraw :
        intermed_4 air 1 1 (nextRow air row) -
          (concatScheduleHi16 air row 1 +
            composeHi16 (fieldSmallSigma0 (rawConcatScheduleBitsWord air row 2))) = 0 := by
      simpa [constraint_554, Circuit.isTransitionRow, hrow.ne,
        next_intermed_4_eq_nextRow air hrot 1 1 row hvalid, concatScheduleHi16,
        composeHi16_range_eq, scheduleBitsWord, rawConcatScheduleBitsWord, nextScheduleBitsWord,
        fieldSmallSigma0, fieldRotr, fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h554
    exact sub_eq_zero.mp (by simpa [hslot_next] using hraw)
  · have h557 : constraint_557 air row := by tauto
    have hraw :
        intermed_4 air 2 0 (nextRow air row) -
          (concatScheduleLo16 air row 2 +
            composeLo16 (fieldSmallSigma0 (rawConcatScheduleBitsWord air row 3))) = 0 := by
      simpa [constraint_557, Circuit.isTransitionRow, hrow.ne,
        next_intermed_4_eq_nextRow air hrot 2 0 row hvalid, concatScheduleLo16,
        composeLo16_range_eq, scheduleBitsWord, rawConcatScheduleBitsWord, nextScheduleBitsWord,
        fieldSmallSigma0, fieldRotr, fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h557
    exact sub_eq_zero.mp (by simpa [hslot_next] using hraw)
  · have h560 : constraint_560 air row := by tauto
    have hraw :
        intermed_4 air 2 1 (nextRow air row) -
          (concatScheduleHi16 air row 2 +
            composeHi16 (fieldSmallSigma0 (rawConcatScheduleBitsWord air row 3))) = 0 := by
      simpa [constraint_560, Circuit.isTransitionRow, hrow.ne,
        next_intermed_4_eq_nextRow air hrot 2 1 row hvalid, concatScheduleHi16,
        composeHi16_range_eq, scheduleBitsWord, rawConcatScheduleBitsWord, nextScheduleBitsWord,
        fieldSmallSigma0, fieldRotr, fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h560
    exact sub_eq_zero.mp (by simpa [hslot_next] using hraw)
  · have h563 : constraint_563 air row := by tauto
    have hraw :
        intermed_4 air 3 0 (nextRow air row) -
          (concatScheduleLo16 air row 3 +
            composeLo16 (fieldSmallSigma0 (rawConcatScheduleBitsWord air row 4))) = 0 := by
      simpa [constraint_563, Circuit.isTransitionRow, hrow.ne,
        next_intermed_4_eq_nextRow air hrot 3 0 row hvalid, concatScheduleLo16,
        composeLo16_range_eq, scheduleBitsWord, rawConcatScheduleBitsWord, nextScheduleBitsWord,
        fieldSmallSigma0, fieldRotr, fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h563
    exact sub_eq_zero.mp (by simpa [hslot_next] using hraw)
  · have h566 : constraint_566 air row := by tauto
    have hraw :
        intermed_4 air 3 1 (nextRow air row) -
          (concatScheduleHi16 air row 3 +
            composeHi16 (fieldSmallSigma0 (rawConcatScheduleBitsWord air row 4))) = 0 := by
      simpa [constraint_566, Circuit.isTransitionRow, hrow.ne,
        next_intermed_4_eq_nextRow air hrot 3 1 row hvalid, concatScheduleHi16,
        composeHi16_range_eq, scheduleBitsWord, rawConcatScheduleBitsWord, nextScheduleBitsWord,
        fieldSmallSigma0, fieldRotr, fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h566
    exact sub_eq_zero.mp (by simpa [hslot_next] using hraw)

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
