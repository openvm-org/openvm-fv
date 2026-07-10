/-
  Layer B: Message Schedule Correctness (Recurrence)

  Proves the low/high-limb recurrence equations for schedule expansion rows.

  Depends on: Core
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.MessageSchedule.Core

set_option autoImplicit false

set_option maxHeartbeats 2500000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## B4: Single schedule word recurrence (constraints 569–719) -/

/-- Each schedule carry limb is encoded by two boolean cells on expansion rows. -/
private theorem schedule_carry_bit_boolean_raw_slot0 (air : C FBB ExtF) (row bit : ℕ)
    (hbit : bit < 4)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    next_msg_schedule_carry_or_buffer air 0 bit row = 0 ∨
      next_msg_schedule_carry_or_buffer air 0 bit row = 1 := by
  have h550_599 := constraints_550_599_of_schedule_constraints air row hs
  unfold constraints_550_599 at h550_599
  interval_cases bit
  · have h571 : constraint_571 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 0 0 row *
          (next_msg_schedule_carry_or_buffer air 0 0 row - 1) = 0 := by
      simpa [constraint_571, hround_next, hnot_first4_next] using h571
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h572 : constraint_572 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 0 1 row *
          (next_msg_schedule_carry_or_buffer air 0 1 row - 1) = 0 := by
      simpa [constraint_572, hround_next, hnot_first4_next] using h572
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h573 : constraint_573 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 0 2 row *
          (next_msg_schedule_carry_or_buffer air 0 2 row - 1) = 0 := by
      simpa [constraint_573, hround_next, hnot_first4_next] using h573
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h574 : constraint_574 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 0 3 row *
          (next_msg_schedule_carry_or_buffer air 0 3 row - 1) = 0 := by
      simpa [constraint_574, hround_next, hnot_first4_next] using h574
    exact bit_boolean_of_sq_eq_zero _ hpoly

private theorem schedule_carry_bit_boolean_raw_slot1 (air : C FBB ExtF) (row bit : ℕ)
    (hbit : bit < 4)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    next_msg_schedule_carry_or_buffer air 1 bit row = 0 ∨
      next_msg_schedule_carry_or_buffer air 1 bit row = 1 := by
  have h600_649 := constraints_600_649_of_schedule_constraints air row hs
  unfold constraints_600_649 at h600_649
  interval_cases bit
  · have h609 : constraint_609 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 1 0 row *
          (next_msg_schedule_carry_or_buffer air 1 0 row - 1) = 0 := by
      simpa [constraint_609, hround_next, hnot_first4_next] using h609
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h610 : constraint_610 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 1 1 row *
          (next_msg_schedule_carry_or_buffer air 1 1 row - 1) = 0 := by
      simpa [constraint_610, hround_next, hnot_first4_next] using h610
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h611 : constraint_611 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 1 2 row *
          (next_msg_schedule_carry_or_buffer air 1 2 row - 1) = 0 := by
      simpa [constraint_611, hround_next, hnot_first4_next] using h611
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h612 : constraint_612 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 1 3 row *
          (next_msg_schedule_carry_or_buffer air 1 3 row - 1) = 0 := by
      simpa [constraint_612, hround_next, hnot_first4_next] using h612
    exact bit_boolean_of_sq_eq_zero _ hpoly

private theorem schedule_carry_bit_boolean_raw_slot2 (air : C FBB ExtF) (row bit : ℕ)
    (hbit : bit < 4)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    next_msg_schedule_carry_or_buffer air 2 bit row = 0 ∨
      next_msg_schedule_carry_or_buffer air 2 bit row = 1 := by
  have h600_649 := constraints_600_649_of_schedule_constraints air row hs
  have h650_699 := constraints_650_699_of_schedule_constraints air row hs
  unfold constraints_600_649 at h600_649
  unfold constraints_650_699 at h650_699
  interval_cases bit
  · have h647 : constraint_647 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 2 0 row *
          (next_msg_schedule_carry_or_buffer air 2 0 row - 1) = 0 := by
      simpa [constraint_647, hround_next, hnot_first4_next] using h647
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h648 : constraint_648 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 2 1 row *
          (next_msg_schedule_carry_or_buffer air 2 1 row - 1) = 0 := by
      simpa [constraint_648, hround_next, hnot_first4_next] using h648
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h649 : constraint_649 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 2 2 row *
          (next_msg_schedule_carry_or_buffer air 2 2 row - 1) = 0 := by
      simpa [constraint_649, hround_next, hnot_first4_next] using h649
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h650 : constraint_650 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 2 3 row *
          (next_msg_schedule_carry_or_buffer air 2 3 row - 1) = 0 := by
      simpa [constraint_650, hround_next, hnot_first4_next] using h650
    exact bit_boolean_of_sq_eq_zero _ hpoly

private theorem schedule_carry_bit_boolean_raw_slot3 (air : C FBB ExtF) (row bit : ℕ)
    (hbit : bit < 4)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    next_msg_schedule_carry_or_buffer air 3 bit row = 0 ∨
      next_msg_schedule_carry_or_buffer air 3 bit row = 1 := by
  have h650_699 := constraints_650_699_of_schedule_constraints air row hs
  unfold constraints_650_699 at h650_699
  interval_cases bit
  · have h685 : constraint_685 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 3 0 row *
          (next_msg_schedule_carry_or_buffer air 3 0 row - 1) = 0 := by
      simpa [constraint_685, hround_next, hnot_first4_next] using h685
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h686 : constraint_686 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 3 1 row *
          (next_msg_schedule_carry_or_buffer air 3 1 row - 1) = 0 := by
      simpa [constraint_686, hround_next, hnot_first4_next] using h686
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h687 : constraint_687 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 3 2 row *
          (next_msg_schedule_carry_or_buffer air 3 2 row - 1) = 0 := by
      simpa [constraint_687, hround_next, hnot_first4_next] using h687
    exact bit_boolean_of_sq_eq_zero _ hpoly
  · have h688 : constraint_688 air row := by tauto
    have hpoly :
        next_msg_schedule_carry_or_buffer air 3 3 row *
          (next_msg_schedule_carry_or_buffer air 3 3 row - 1) = 0 := by
      simpa [constraint_688, hround_next, hnot_first4_next] using h688
    exact bit_boolean_of_sq_eq_zero _ hpoly

theorem schedule_carry_bits_boolean (air : C FBB ExtF) (row : ℕ) (slot : ℕ) (limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 2)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    (msg_schedule_carry_or_buffer air slot (2 * limb) (nextRow air row) = 0 ∨
     msg_schedule_carry_or_buffer air slot (2 * limb) (nextRow air row) = 1) ∧
    (msg_schedule_carry_or_buffer air slot (2 * limb + 1) (nextRow air row) = 0 ∨
     msg_schedule_carry_or_buffer air slot (2 * limb + 1) (nextRow air row) = 1) := by
  interval_cases slot
  · have hb0_raw :=
      schedule_carry_bit_boolean_raw_slot0 air row (2 * limb) (by omega) hs hround_next
        hnot_first4_next
    have hb1_raw :=
      schedule_carry_bit_boolean_raw_slot0 air row (2 * limb + 1) (by omega) hs hround_next
        hnot_first4_next
    refine ⟨?_, ?_⟩
    · simpa [next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 0 (2 * limb) row hrow] using
        hb0_raw
    · simpa [next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 0 (2 * limb + 1) row hrow] using
        hb1_raw
  · have hb0_raw :=
      schedule_carry_bit_boolean_raw_slot1 air row (2 * limb) (by omega) hs hround_next
        hnot_first4_next
    have hb1_raw :=
      schedule_carry_bit_boolean_raw_slot1 air row (2 * limb + 1) (by omega) hs hround_next
        hnot_first4_next
    refine ⟨?_, ?_⟩
    · simpa [next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 1 (2 * limb) row hrow] using
        hb0_raw
    · simpa [next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 1 (2 * limb + 1) row hrow] using
        hb1_raw
  · have hb0_raw :=
      schedule_carry_bit_boolean_raw_slot2 air row (2 * limb) (by omega) hs hround_next
        hnot_first4_next
    have hb1_raw :=
      schedule_carry_bit_boolean_raw_slot2 air row (2 * limb + 1) (by omega) hs hround_next
        hnot_first4_next
    refine ⟨?_, ?_⟩
    · simpa [next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 2 (2 * limb) row hrow] using
        hb0_raw
    · simpa [next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 2 (2 * limb + 1) row hrow] using
        hb1_raw
  · have hb0_raw :=
      schedule_carry_bit_boolean_raw_slot3 air row (2 * limb) (by omega) hs hround_next
        hnot_first4_next
    have hb1_raw :=
      schedule_carry_bit_boolean_raw_slot3 air row (2 * limb + 1) (by omega) hs hround_next
        hnot_first4_next
    refine ⟨?_, ?_⟩
    · simpa [next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 3 (2 * limb) row hrow] using
        hb0_raw
    · simpa [next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 3 (2 * limb + 1) row hrow] using
        hb1_raw

/-- The decoded schedule carry value lies in `{0,1,2,3}` on expansion rows. -/
theorem schedule_carry_value_lt_four (air : C FBB ExtF) (row : ℕ) (slot : ℕ) (limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 2)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    (scheduleCarryValue air (nextRow air row) slot limb).val < 4 := by
  rcases
      schedule_carry_bits_boolean air row slot limb hslot hlimb hrow hrot hs hround_next
        hnot_first4_next with
    ⟨hb0, hb1⟩
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
    simp [scheduleCarryValue, hb0, hb1]

private theorem schedule_recurrence_lo_slot0 (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (h569 : constraint_569 air row) :
    composeLo16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 2)) +
    schedule_helper_w_3 air 0 0 row +
    intermed_12 air 0 0 row =
      composeLo16 (nextScheduleBitsWord air row 0) +
      (next_msg_schedule_carry_or_buffer air 0 0 row +
        2 * next_msg_schedule_carry_or_buffer air 0 1 row) * (2 ^ 16 : ℕ) := by
  have hraw :
      composeLo16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 2)) +
      schedule_helper_w_3 air 0 0 row +
      intermed_12 air 0 0 row -
        (composeLo16 (nextScheduleBitsWord air row 0) +
          (next_msg_schedule_carry_or_buffer air 0 0 row +
            2 * next_msg_schedule_carry_or_buffer air 0 1 row) * (2 ^ 16 : ℕ)) = 0 := by
    simpa [constraint_569, Circuit.isTransitionRow, hrow.ne, rawConcatScheduleBitsWord,
      nextScheduleBitsWord, scheduleBitsWord, composeLo16_range_eq, fieldSmallSigma1, fieldRotr,
      fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h569
  exact sub_eq_zero.mp hraw

private theorem schedule_recurrence_lo_slot1 (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (h607 : constraint_607 air row) :
    composeLo16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 3)) +
    schedule_helper_w_3 air 1 0 row +
    intermed_12 air 1 0 row =
      composeLo16 (nextScheduleBitsWord air row 1) +
      (next_msg_schedule_carry_or_buffer air 1 0 row +
        2 * next_msg_schedule_carry_or_buffer air 1 1 row) * (2 ^ 16 : ℕ) := by
  have hraw :
      composeLo16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 3)) +
      schedule_helper_w_3 air 1 0 row +
      intermed_12 air 1 0 row -
        (composeLo16 (nextScheduleBitsWord air row 1) +
          (next_msg_schedule_carry_or_buffer air 1 0 row +
            2 * next_msg_schedule_carry_or_buffer air 1 1 row) * (2 ^ 16 : ℕ)) = 0 := by
    simpa [constraint_607, Circuit.isTransitionRow, hrow.ne, rawConcatScheduleBitsWord,
      nextScheduleBitsWord, scheduleBitsWord, composeLo16_range_eq, fieldSmallSigma1, fieldRotr,
      fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h607
  exact sub_eq_zero.mp hraw

private theorem schedule_recurrence_lo_slot2 (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (h645 : constraint_645 air row) :
    composeLo16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 4)) +
    schedule_helper_w_3 air 2 0 row +
    intermed_12 air 2 0 row =
      composeLo16 (nextScheduleBitsWord air row 2) +
      (next_msg_schedule_carry_or_buffer air 2 0 row +
        2 * next_msg_schedule_carry_or_buffer air 2 1 row) * (2 ^ 16 : ℕ) := by
  have hraw :
      composeLo16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 4)) +
      schedule_helper_w_3 air 2 0 row +
      intermed_12 air 2 0 row -
        (composeLo16 (nextScheduleBitsWord air row 2) +
          (next_msg_schedule_carry_or_buffer air 2 0 row +
            2 * next_msg_schedule_carry_or_buffer air 2 1 row) * (2 ^ 16 : ℕ)) = 0 := by
    simpa [constraint_645, Circuit.isTransitionRow, hrow.ne, rawConcatScheduleBitsWord,
      nextScheduleBitsWord, scheduleBitsWord, composeLo16_range_eq, fieldSmallSigma1, fieldRotr,
      fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h645
  exact sub_eq_zero.mp hraw

private theorem schedule_recurrence_lo_slot3 (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (h683 : constraint_683 air row) :
    composeLo16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 5)) +
    concatScheduleLo16 air row 0 +
    intermed_12 air 3 0 row =
      composeLo16 (nextScheduleBitsWord air row 3) +
      (next_msg_schedule_carry_or_buffer air 3 0 row +
        2 * next_msg_schedule_carry_or_buffer air 3 1 row) * (2 ^ 16 : ℕ) := by
  have hraw :
      composeLo16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 5)) +
      concatScheduleLo16 air row 0 +
      intermed_12 air 3 0 row -
        (composeLo16 (nextScheduleBitsWord air row 3) +
          (next_msg_schedule_carry_or_buffer air 3 0 row +
            2 * next_msg_schedule_carry_or_buffer air 3 1 row) * (2 ^ 16 : ℕ)) = 0 := by
    simpa [constraint_683, Circuit.isTransitionRow, hrow.ne, rawConcatScheduleBitsWord,
      nextScheduleBitsWord, scheduleBitsWord, concatScheduleLo16, composeLo16_range_eq,
      fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h683
  exact sub_eq_zero.mp hraw

theorem schedule_recurrence_lo (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row) :
    composeLo16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) +
    scheduleW7Lo16 air row slot +
    intermed_12 air slot 0 row =
      composeLo16 (scheduleBitsWord air (nextRow air row) slot) +
      scheduleCarryValue air (nextRow air row) slot 0 * (2 ^ 16 : ℕ) := by
  have hvalid : row ≤ Circuit.last_row air := hrow.le
  have h550_599 := constraints_550_599_of_schedule_constraints air row hs
  have h600_649 := constraints_600_649_of_schedule_constraints air row hs
  have h650_699 := constraints_650_699_of_schedule_constraints air row hs
  unfold constraints_550_599 at h550_599
  unfold constraints_600_649 at h600_649
  unfold constraints_650_699 at h650_699
  interval_cases slot
  · have h569 : constraint_569 air row := by tauto
    simpa [rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 2 hrot hvalid,
      nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 0 hrot hvalid, scheduleCarryValue,
      scheduleW7Lo16,
      next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 0 0 row hvalid,
      next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 0 1 row hvalid] using
      schedule_recurrence_lo_slot0 air row hrow h569
  · have h607 : constraint_607 air row := by tauto
    simpa [rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 3 hrot hvalid,
      nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 1 hrot hvalid, scheduleCarryValue,
      scheduleW7Lo16,
      next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 1 0 row hvalid,
      next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 1 1 row hvalid] using
      schedule_recurrence_lo_slot1 air row hrow h607
  · have h645 : constraint_645 air row := by tauto
    simpa [rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 4 hrot hvalid,
      nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 2 hrot hvalid, scheduleCarryValue,
      scheduleW7Lo16,
      next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 2 0 row hvalid,
      next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 2 1 row hvalid] using
      schedule_recurrence_lo_slot2 air row hrow h645
  · have h683 : constraint_683 air row := by tauto
    simpa [rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 5 hrot hvalid,
      nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 3 hrot hvalid, scheduleCarryValue,
      scheduleW7Lo16,
      next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 3 0 row hvalid,
      next_msg_schedule_carry_or_buffer_eq_nextRow air hrot 3 1 row hvalid] using
      schedule_recurrence_lo_slot3 air row hrow h683

/-- Concrete high-limb recurrence for slot 0. -/
theorem schedule_recurrence_hi_slot0 (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (h570 : constraint_570 air row) :
    (next_msg_schedule_carry_or_buffer air 0 0 row +
      2 * next_msg_schedule_carry_or_buffer air 0 1 row) +
    composeHi16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 2)) +
    schedule_helper_w_3 air 0 1 row +
    intermed_12 air 0 1 row =
      composeHi16 (nextScheduleBitsWord air row 0) +
      (next_msg_schedule_carry_or_buffer air 0 2 row +
        2 * next_msg_schedule_carry_or_buffer air 0 3 row) * (2 ^ 16 : ℕ) := by
  have hraw :
      (next_msg_schedule_carry_or_buffer air 0 0 row +
        2 * next_msg_schedule_carry_or_buffer air 0 1 row) +
      composeHi16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 2)) +
      schedule_helper_w_3 air 0 1 row +
      intermed_12 air 0 1 row -
        (composeHi16 (nextScheduleBitsWord air row 0) +
          (next_msg_schedule_carry_or_buffer air 0 2 row +
            2 * next_msg_schedule_carry_or_buffer air 0 3 row) * (2 ^ 16 : ℕ)) = 0 := by
    simpa [constraint_570, Circuit.isTransitionRow, hrow.ne, rawConcatScheduleBitsWord,
      nextScheduleBitsWord, scheduleBitsWord, composeHi16_range_eq, fieldSmallSigma1, fieldRotr,
      fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h570
  exact sub_eq_zero.mp hraw

theorem schedule_recurrence_hi_slot1 (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (h608 : constraint_608 air row) :
    (next_msg_schedule_carry_or_buffer air 1 0 row +
      2 * next_msg_schedule_carry_or_buffer air 1 1 row) +
    composeHi16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 3)) +
    schedule_helper_w_3 air 1 1 row +
    intermed_12 air 1 1 row =
      composeHi16 (nextScheduleBitsWord air row 1) +
      (next_msg_schedule_carry_or_buffer air 1 2 row +
        2 * next_msg_schedule_carry_or_buffer air 1 3 row) * (2 ^ 16 : ℕ) := by
  have hraw :
      (next_msg_schedule_carry_or_buffer air 1 0 row +
        2 * next_msg_schedule_carry_or_buffer air 1 1 row) +
      composeHi16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 3)) +
      schedule_helper_w_3 air 1 1 row +
      intermed_12 air 1 1 row -
        (composeHi16 (nextScheduleBitsWord air row 1) +
          (next_msg_schedule_carry_or_buffer air 1 2 row +
            2 * next_msg_schedule_carry_or_buffer air 1 3 row) * (2 ^ 16 : ℕ)) = 0 := by
    simpa [constraint_608, Circuit.isTransitionRow, hrow.ne, rawConcatScheduleBitsWord,
      nextScheduleBitsWord, scheduleBitsWord, composeHi16_range_eq, fieldSmallSigma1, fieldRotr,
      fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h608
  exact sub_eq_zero.mp hraw

theorem schedule_recurrence_hi_slot2 (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (h646 : constraint_646 air row) :
    (next_msg_schedule_carry_or_buffer air 2 0 row +
      2 * next_msg_schedule_carry_or_buffer air 2 1 row) +
    composeHi16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 4)) +
    schedule_helper_w_3 air 2 1 row +
    intermed_12 air 2 1 row =
      composeHi16 (nextScheduleBitsWord air row 2) +
      (next_msg_schedule_carry_or_buffer air 2 2 row +
        2 * next_msg_schedule_carry_or_buffer air 2 3 row) * (2 ^ 16 : ℕ) := by
  have hraw :
      (next_msg_schedule_carry_or_buffer air 2 0 row +
        2 * next_msg_schedule_carry_or_buffer air 2 1 row) +
      composeHi16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 4)) +
      schedule_helper_w_3 air 2 1 row +
      intermed_12 air 2 1 row -
        (composeHi16 (nextScheduleBitsWord air row 2) +
          (next_msg_schedule_carry_or_buffer air 2 2 row +
            2 * next_msg_schedule_carry_or_buffer air 2 3 row) * (2 ^ 16 : ℕ)) = 0 := by
    simpa [constraint_646, Circuit.isTransitionRow, hrow.ne, rawConcatScheduleBitsWord,
      nextScheduleBitsWord, scheduleBitsWord, composeHi16_range_eq, fieldSmallSigma1, fieldRotr,
      fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h646
  exact sub_eq_zero.mp hraw

theorem schedule_recurrence_hi_slot3 (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (h684 : constraint_684 air row) :
    (next_msg_schedule_carry_or_buffer air 3 0 row +
      2 * next_msg_schedule_carry_or_buffer air 3 1 row) +
    composeHi16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 5)) +
    concatScheduleHi16 air row 0 +
    intermed_12 air 3 1 row =
      composeHi16 (nextScheduleBitsWord air row 3) +
      (next_msg_schedule_carry_or_buffer air 3 2 row +
        2 * next_msg_schedule_carry_or_buffer air 3 3 row) * (2 ^ 16 : ℕ) := by
  have hraw :
      (next_msg_schedule_carry_or_buffer air 3 0 row +
        2 * next_msg_schedule_carry_or_buffer air 3 1 row) +
      composeHi16 (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 5)) +
      concatScheduleHi16 air row 0 +
      intermed_12 air 3 1 row -
        (composeHi16 (nextScheduleBitsWord air row 3) +
          (next_msg_schedule_carry_or_buffer air 3 2 row +
            2 * next_msg_schedule_carry_or_buffer air 3 3 row) * (2 ^ 16 : ℕ)) = 0 := by
    simpa [constraint_684, Circuit.isTransitionRow, hrow.ne, rawConcatScheduleBitsWord,
      nextScheduleBitsWord, scheduleBitsWord, concatScheduleBitsWord, concatScheduleHi16,
      composeHi16_range_eq,
      fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly, Finset.sum_range_succ] using h684
  exact sub_eq_zero.mp hraw

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
