/-
  Layer B: Message Schedule Correctness (Carry Pipeline)

  Isolates the two carry-forward steps:
  `intermed_4 -> intermed_8` and `intermed_8 -> intermed_12`.

  Depends on: Core
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.MessageSchedule.Core

set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## intermed_4 -> intermed_8 carry -/

private theorem intermed8_carry_from_poly (air : C FBB ExtF) (row slot limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8CarryGateNext air row = 1)
    (hpoly :
      intermed8CarryGateNext air row *
        (next_intermed_8 air slot limb row - intermed_4 air slot limb row) = 0) :
    intermed_8 air slot limb (nextRow air row) = intermed_4 air slot limb row := by
  rw [hgate, one_mul] at hpoly
  have hraw : next_intermed_8 air slot limb row = intermed_4 air slot limb row :=
    sub_eq_zero.mp hpoly
  simpa [next_intermed_8_eq_nextRow air hrot slot limb row hrow] using hraw

private theorem intermed8_carry_00 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8CarryGateNext air row = 1)
    (h546 : constraint_546 air row) :
    intermed_8 air 0 0 (nextRow air row) = intermed_4 air 0 0 row := by
  have hpoly :
      intermed8CarryGateNext air row *
        (next_intermed_8 air 0 0 row - intermed_4 air 0 0 row) = 0 := by
    simpa only [constraint_546, intermed8CarryGateNext, intermed8CarryGatePoly] using h546
  exact intermed8_carry_from_poly air row 0 0 hrow hrot hgate hpoly

private theorem intermed8_carry_01 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8CarryGateNext air row = 1)
    (h549 : constraint_549 air row) :
    intermed_8 air 0 1 (nextRow air row) = intermed_4 air 0 1 row := by
  have hpoly :
      intermed8CarryGateNext air row *
        (next_intermed_8 air 0 1 row - intermed_4 air 0 1 row) = 0 := by
    simpa only [constraint_549, intermed8CarryGateNext, intermed8CarryGatePoly] using h549
  exact intermed8_carry_from_poly air row 0 1 hrow hrot hgate hpoly

private theorem intermed8_carry_10 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8CarryGateNext air row = 1)
    (h552 : constraint_552 air row) :
    intermed_8 air 1 0 (nextRow air row) = intermed_4 air 1 0 row := by
  have hpoly :
      intermed8CarryGateNext air row *
        (next_intermed_8 air 1 0 row - intermed_4 air 1 0 row) = 0 := by
    simpa only [constraint_552, intermed8CarryGateNext, intermed8CarryGatePoly] using h552
  exact intermed8_carry_from_poly air row 1 0 hrow hrot hgate hpoly

private theorem intermed8_carry_11 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8CarryGateNext air row = 1)
    (h555 : constraint_555 air row) :
    intermed_8 air 1 1 (nextRow air row) = intermed_4 air 1 1 row := by
  have hpoly :
      intermed8CarryGateNext air row *
        (next_intermed_8 air 1 1 row - intermed_4 air 1 1 row) = 0 := by
    simpa only [constraint_555, intermed8CarryGateNext, intermed8CarryGatePoly] using h555
  exact intermed8_carry_from_poly air row 1 1 hrow hrot hgate hpoly

private theorem intermed8_carry_20 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8CarryGateNext air row = 1)
    (h558 : constraint_558 air row) :
    intermed_8 air 2 0 (nextRow air row) = intermed_4 air 2 0 row := by
  have hpoly :
      intermed8CarryGateNext air row *
        (next_intermed_8 air 2 0 row - intermed_4 air 2 0 row) = 0 := by
    simpa only [constraint_558, intermed8CarryGateNext, intermed8CarryGatePoly] using h558
  exact intermed8_carry_from_poly air row 2 0 hrow hrot hgate hpoly

private theorem intermed8_carry_21 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8CarryGateNext air row = 1)
    (h561 : constraint_561 air row) :
    intermed_8 air 2 1 (nextRow air row) = intermed_4 air 2 1 row := by
  have hpoly :
      intermed8CarryGateNext air row *
        (next_intermed_8 air 2 1 row - intermed_4 air 2 1 row) = 0 := by
    simpa only [constraint_561, intermed8CarryGateNext, intermed8CarryGatePoly] using h561
  exact intermed8_carry_from_poly air row 2 1 hrow hrot hgate hpoly

private theorem intermed8_carry_30 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8CarryGateNext air row = 1)
    (h564 : constraint_564 air row) :
    intermed_8 air 3 0 (nextRow air row) = intermed_4 air 3 0 row := by
  have hpoly :
      intermed8CarryGateNext air row *
        (next_intermed_8 air 3 0 row - intermed_4 air 3 0 row) = 0 := by
    simpa only [constraint_564, intermed8CarryGateNext, intermed8CarryGatePoly] using h564
  exact intermed8_carry_from_poly air row 3 0 hrow hrot hgate hpoly

private theorem intermed8_carry_31 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8CarryGateNext air row = 1)
    (h567 : constraint_567 air row) :
    intermed_8 air 3 1 (nextRow air row) = intermed_4 air 3 1 row := by
  have hpoly :
      intermed8CarryGateNext air row *
        (next_intermed_8 air 3 1 row - intermed_4 air 3 1 row) = 0 := by
    simpa only [constraint_567, intermed8CarryGateNext, intermed8CarryGatePoly] using h567
  exact intermed8_carry_from_poly air row 3 1 hrow hrot hgate hpoly

/-- intermed_8 carries forward intermed_4 when next row_idx ∈ {2,...,13}. -/
theorem intermed_8_carry (air : C FBB ExtF) (row : ℕ) (slot : ℕ) (limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 2)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 2 ≤ n ∧ n ≤ 13 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_8 air slot limb (nextRow air row) = intermed_4 air slot limb row := by
  have hgate := intermed8CarryGateNext_eq_one air row hrow hrot hf_next hrow_idx
  have h539_549 := constraints_539_549_of_schedule_constraints air row hs
  have h550_599 := constraints_550_599_of_schedule_constraints air row hs
  unfold constraints_539_549 at h539_549
  unfold constraints_550_599 at h550_599
  rcases h539_549 with
    ⟨_, _, _, _, _, _, _, h546, _, _, h549⟩
  rcases h550_599 with
    ⟨_, _, h552, _, _, h555, _, _, h558, _, _, h561, _, _, h564, _, _, h567, _⟩
  interval_cases slot <;> interval_cases limb
  · exact intermed8_carry_00 air row hrow hrot hgate h546
  · exact intermed8_carry_01 air row hrow hrot hgate h549
  · exact intermed8_carry_10 air row hrow hrot hgate h552
  · exact intermed8_carry_11 air row hrow hrot hgate h555
  · exact intermed8_carry_20 air row hrow hrot hgate h558
  · exact intermed8_carry_21 air row hrow hrot hgate h561
  · exact intermed8_carry_30 air row hrow hrot hgate h564
  · exact intermed8_carry_31 air row hrow hrot hgate h567

/-! ## intermed_8 -> intermed_12 carry -/

private theorem intermed12_carry_from_poly (air : C FBB ExtF) (row slot limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12CarryGateNext air row = 1)
    (hpoly :
      intermed12CarryGateNext air row *
        (next_intermed_12 air slot limb row - intermed_8 air slot limb row) = 0) :
    intermed_12 air slot limb (nextRow air row) = intermed_8 air slot limb row := by
  rw [hgate, one_mul] at hpoly
  have hraw : next_intermed_12 air slot limb row = intermed_8 air slot limb row :=
    sub_eq_zero.mp hpoly
  simpa [next_intermed_12_eq_nextRow air hrot slot limb row hrow] using hraw

private theorem intermed12_carry_00 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12CarryGateNext air row = 1)
    (h547 : constraint_547 air row) :
    intermed_12 air 0 0 (nextRow air row) = intermed_8 air 0 0 row := by
  have hpoly :
      intermed12CarryGateNext air row *
        (next_intermed_12 air 0 0 row - intermed_8 air 0 0 row) = 0 := by
    simpa only [constraint_547, intermed12CarryGateNext, intermed12CarryGatePoly] using h547
  exact intermed12_carry_from_poly air row 0 0 hrow hrot hgate hpoly

private theorem intermed12_carry_01 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12CarryGateNext air row = 1)
    (h550 : constraint_550 air row) :
    intermed_12 air 0 1 (nextRow air row) = intermed_8 air 0 1 row := by
  have hpoly :
      intermed12CarryGateNext air row *
        (next_intermed_12 air 0 1 row - intermed_8 air 0 1 row) = 0 := by
    simpa only [constraint_550, intermed12CarryGateNext, intermed12CarryGatePoly] using h550
  exact intermed12_carry_from_poly air row 0 1 hrow hrot hgate hpoly

private theorem intermed12_carry_10 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12CarryGateNext air row = 1)
    (h553 : constraint_553 air row) :
    intermed_12 air 1 0 (nextRow air row) = intermed_8 air 1 0 row := by
  have hpoly :
      intermed12CarryGateNext air row *
        (next_intermed_12 air 1 0 row - intermed_8 air 1 0 row) = 0 := by
    simpa only [constraint_553, intermed12CarryGateNext, intermed12CarryGatePoly] using h553
  exact intermed12_carry_from_poly air row 1 0 hrow hrot hgate hpoly

private theorem intermed12_carry_11 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12CarryGateNext air row = 1)
    (h556 : constraint_556 air row) :
    intermed_12 air 1 1 (nextRow air row) = intermed_8 air 1 1 row := by
  have hpoly :
      intermed12CarryGateNext air row *
        (next_intermed_12 air 1 1 row - intermed_8 air 1 1 row) = 0 := by
    simpa only [constraint_556, intermed12CarryGateNext, intermed12CarryGatePoly] using h556
  exact intermed12_carry_from_poly air row 1 1 hrow hrot hgate hpoly

private theorem intermed12_carry_20 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12CarryGateNext air row = 1)
    (h559 : constraint_559 air row) :
    intermed_12 air 2 0 (nextRow air row) = intermed_8 air 2 0 row := by
  have hpoly :
      intermed12CarryGateNext air row *
        (next_intermed_12 air 2 0 row - intermed_8 air 2 0 row) = 0 := by
    simpa only [constraint_559, intermed12CarryGateNext, intermed12CarryGatePoly] using h559
  exact intermed12_carry_from_poly air row 2 0 hrow hrot hgate hpoly

private theorem intermed12_carry_21 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12CarryGateNext air row = 1)
    (h562 : constraint_562 air row) :
    intermed_12 air 2 1 (nextRow air row) = intermed_8 air 2 1 row := by
  have hpoly :
      intermed12CarryGateNext air row *
        (next_intermed_12 air 2 1 row - intermed_8 air 2 1 row) = 0 := by
    simpa only [constraint_562, intermed12CarryGateNext, intermed12CarryGatePoly] using h562
  exact intermed12_carry_from_poly air row 2 1 hrow hrot hgate hpoly

private theorem intermed12_carry_30 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12CarryGateNext air row = 1)
    (h565 : constraint_565 air row) :
    intermed_12 air 3 0 (nextRow air row) = intermed_8 air 3 0 row := by
  have hpoly :
      intermed12CarryGateNext air row *
        (next_intermed_12 air 3 0 row - intermed_8 air 3 0 row) = 0 := by
    simpa only [constraint_565, intermed12CarryGateNext, intermed12CarryGatePoly] using h565
  exact intermed12_carry_from_poly air row 3 0 hrow hrot hgate hpoly

private theorem intermed12_carry_31 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12CarryGateNext air row = 1)
    (h568 : constraint_568 air row) :
    intermed_12 air 3 1 (nextRow air row) = intermed_8 air 3 1 row := by
  have hpoly :
      intermed12CarryGateNext air row *
        (next_intermed_12 air 3 1 row - intermed_8 air 3 1 row) = 0 := by
    simpa only [constraint_568, intermed12CarryGateNext, intermed12CarryGatePoly] using h568
  exact intermed12_carry_from_poly air row 3 1 hrow hrot hgate hpoly

/-- intermed_12 carries forward intermed_8 when next row_idx ∈ {3,...,14}. -/
theorem intermed_12_carry (air : C FBB ExtF) (row : ℕ) (slot : ℕ) (limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 2)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 3 ≤ n ∧ n ≤ 14 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_12 air slot limb (nextRow air row) = intermed_8 air slot limb row := by
  have hgate := intermed12CarryGateNext_eq_one air row hrow hrot hf_next hrow_idx
  have h539_549 := constraints_539_549_of_schedule_constraints air row hs
  have h550_599 := constraints_550_599_of_schedule_constraints air row hs
  unfold constraints_539_549 at h539_549
  unfold constraints_550_599 at h550_599
  rcases h539_549 with
    ⟨_, _, _, _, _, _, _, _, h547, _, _⟩
  rcases h550_599 with
    ⟨h550, _, _, h553, _, _, h556, _, _, h559, _, _, h562, _, _, h565, _, _, h568, _⟩
  interval_cases slot <;> interval_cases limb
  · exact intermed12_carry_00 air row hrow hrot hgate h547
  · exact intermed12_carry_01 air row hrow hrot hgate h550
  · exact intermed12_carry_10 air row hrow hrot hgate h553
  · exact intermed12_carry_11 air row hrow hrot hgate h556
  · exact intermed12_carry_20 air row hrow hrot hgate h559
  · exact intermed12_carry_21 air row hrow hrot hgate h562
  · exact intermed12_carry_30 air row hrow hrot hgate h565
  · exact intermed12_carry_31 air row hrow hrot hgate h568

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
