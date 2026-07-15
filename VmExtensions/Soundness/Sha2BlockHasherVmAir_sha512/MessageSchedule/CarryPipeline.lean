/-
  Layer B: Message Schedule Correctness (Carry Pipeline)

  Combined carry-pipeline proofs for both the `intermed_4 -> intermed_8` and
  `intermed_8 -> intermed_12` carry transports across all four SHA-512
  schedule slots.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.Defs
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.MessageSchedule.CarryGates

set_option autoImplicit false

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ### intermed_8 slot-0 gate -/

def intermed8Slot0CarryGatePoly (d0 d1 d2 d3 d4 d5 : FBB) : FBB :=
  let s := d0 + d1 + d2 + d3 + d4 + d5
  d5 * (d5 - 1) * 1006632961 +
  d4 * (2 - s) +
  d4 * d5 +
  d4 * (d4 - 1) * 1006632961 +
  d3 * (2 - s) +
  d3 * d5 +
  d3 * d4 +
  d3 * (d3 - 1) * 1006632961 +
  d2 * (2 - s) +
  d2 * d5 +
  d2 * d4 +
  d2 * d3 +
  d2 * (d2 - 1) * 1006632961 +
  d1 * (2 - s) +
  d1 * d5 +
  d1 * d4

def intermed8Slot0CarryGateNext (air : C FBB ExtF) (row : ℕ) : FBB :=
  intermed8Slot0CarryGatePoly
    (encoder_idx_next air 0 row)
    (encoder_idx_next air 1 row)
    (encoder_idx_next air 2 row)
    (encoder_idx_next air 3 row)
    (encoder_idx_next air 4 row)
    (encoder_idx_next air 5 row)

private theorem intermed8_slot0_gate_lookup_fin :
    ∀ n0 n1 n2 n3 n4 n5 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val + n5.val ≤ 2 →
      encoderConstraint11Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = 0 →
      (intermed8Slot0CarryGatePoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = 1 ↔
        ∃ sel : Fin 16,
          encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
            (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = ((sel.val + 2 : ℕ) : FBB)) := by
  decide

theorem intermed8Slot0CarryGateNext_eq_one (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 2 ≤ n ∧ n ≤ 17 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed8Slot0CarryGateNext air row = 1 := by
  have hf_next' := hf_next
  rcases hf_next with ⟨_, _, _, _, _, _, _, _, _, _, _, h11, _, _, _, _, _⟩
  have hd0 := encoder_digits_ternary air (nextRow air row) hf_next' 0 (by omega)
  have hd1 := encoder_digits_ternary air (nextRow air row) hf_next' 1 (by omega)
  have hd2 := encoder_digits_ternary air (nextRow air row) hf_next' 2 (by omega)
  have hd3 := encoder_digits_ternary air (nextRow air row) hf_next' 3 (by omega)
  have hd4 := encoder_digits_ternary air (nextRow air row) hf_next' 4 (by omega)
  have hd5 := encoder_digits_ternary air (nextRow air row) hf_next' 5 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 (nextRow air row)) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 (nextRow air row)) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 (nextRow air row)) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 (nextRow air row)) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 (nextRow air row)) hd4 with ⟨n4, h4⟩
  rcases ternary_as_fin3 (encoder_idx air 5 (nextRow air row)) hd5 with ⟨n5, h5⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val + n5.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4, h5] using
      encoder_digit_sum_ternary air (nextRow air row) hf_next'
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hc11 : encoderConstraint11Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
      (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = 0 := by
    simpa [encoderConstraint11Poly, constraint_11, encoder_choose2, h0, h1, h2, h3, h4, h5]
      using h11
  rcases hrow_idx with ⟨n, hnlo, hnhi, hsel⟩
  let sel : Fin 16 := ⟨n - 2, by omega⟩
  have hsel_shift :
      ∃ sel' : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = ((sel'.val + 2 : ℕ) : FBB) := by
    refine ⟨sel, ?_⟩
    have hsel_nat : sel.val + 2 = n := by
      simp [sel]
      omega
    calc
      encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) =
          encoder_selector_idx air (nextRow air row) := by
            simp [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
              encoderSelectorPoly, h0, h1, h2, h3, h4, h5]
      _ = (n : FBB) := hsel
      _ = ((sel.val + 2 : ℕ) : FBB) := by
            rw [← hsel_nat]
  have hgate :
      intermed8Slot0CarryGatePoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = 1 := by
    exact (intermed8_slot0_gate_lookup_fin n0 n1 n2 n3 n4 n5 htotal_le hc11).mpr hsel_shift
  rw [intermed8Slot0CarryGateNext]
  rw [encoder_idx_next_eq_nextRow air hrot 0 row hrow,
    encoder_idx_next_eq_nextRow air hrot 1 row hrow,
    encoder_idx_next_eq_nextRow air hrot 2 row hrow,
    encoder_idx_next_eq_nextRow air hrot 3 row hrow,
    encoder_idx_next_eq_nextRow air hrot 4 row hrow,
    encoder_idx_next_eq_nextRow air hrot 5 row hrow]
  simpa [h0, h1, h2, h3, h4, h5] using hgate

/-! ### intermed_8 slot 0 -/

set_option maxHeartbeats 10000000 in
private theorem intermed8_slot0_from_poly (air : C FBB ExtF) (row limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 0 limb row - intermed_4 air 0 limb row) = 0) :
    intermed_8 air 0 limb (nextRow air row) = intermed_4 air 0 limb row := by
  rw [hgate, one_mul] at hpoly
  have hraw : next_intermed_8 air 0 limb row = intermed_4 air 0 limb row :=
    sub_eq_zero.mp hpoly
  simpa [next_intermed_8_eq_nextRow air hrot 0 limb row hrow] using hraw

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_00 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1065 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1065 air row) :
    intermed_8 air 0 0 (nextRow air row) = intermed_4 air 0 0 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 0 0 row - intermed_4 air 0 0 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1065,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1065
  exact intermed8_slot0_from_poly air row 0 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_01 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1068 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1068 air row) :
    intermed_8 air 0 1 (nextRow air row) = intermed_4 air 0 1 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 0 1 row - intermed_4 air 0 1 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1068,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1068
  exact intermed8_slot0_from_poly air row 1 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_02 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1071 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1071 air row) :
    intermed_8 air 0 2 (nextRow air row) = intermed_4 air 0 2 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 0 2 row - intermed_4 air 0 2 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1071,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1071
  exact intermed8_slot0_from_poly air row 2 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_03 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1074 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1074 air row) :
    intermed_8 air 0 3 (nextRow air row) = intermed_4 air 0 3 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 0 3 row - intermed_4 air 0 3 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1074,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1074
  exact intermed8_slot0_from_poly air row 3 hrow hrot hgate hpoly

/-- Slot-0 branch of `intermed_8_carry`. -/
theorem intermed_8_carry_slot0 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 2 ≤ n ∧ n ≤ 17 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_8 air 0 limb (nextRow air row) = intermed_4 air 0 limb row := by
  have hgate := intermed8Slot0CarryGateNext_eq_one air row hrow hrot hf_next hrow_idx
  rcases hs with ⟨h1050_1099, _, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1050_1099 at h1050_1099
  have h1065_1099 := h1050_1099.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h1068_1099 := h1065_1099.2.2.2
  have h1071_1099 := h1068_1099.2.2.2
  have h1074_1099 := h1071_1099.2.2.2
  have h1065 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1065 air row := h1065_1099.1
  have h1068 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1068 air row := h1068_1099.1
  have h1071 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1071 air row := h1071_1099.1
  have h1074 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1074 air row := h1074_1099.1
  interval_cases limb
  · exact intermed8_carry_00 air row hrow hrot hgate h1065
  · exact intermed8_carry_01 air row hrow hrot hgate h1068
  · exact intermed8_carry_02 air row hrow hrot hgate h1071
  · exact intermed8_carry_03 air row hrow hrot hgate h1074

/-! ### intermed_8 slot 1 -/

set_option maxHeartbeats 10000000 in
private theorem intermed8_slot1_from_poly (air : C FBB ExtF) (row limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 1 limb row - intermed_4 air 1 limb row) = 0) :
    intermed_8 air 1 limb (nextRow air row) = intermed_4 air 1 limb row := by
  rw [hgate, one_mul] at hpoly
  have hraw : next_intermed_8 air 1 limb row = intermed_4 air 1 limb row :=
    sub_eq_zero.mp hpoly
  simpa [next_intermed_8_eq_nextRow air hrot 1 limb row hrow] using hraw

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_10 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1077 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1077 air row) :
    intermed_8 air 1 0 (nextRow air row) = intermed_4 air 1 0 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 1 0 row - intermed_4 air 1 0 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1077,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1077
  exact intermed8_slot1_from_poly air row 0 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_11 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1080 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1080 air row) :
    intermed_8 air 1 1 (nextRow air row) = intermed_4 air 1 1 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 1 1 row - intermed_4 air 1 1 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1080,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1080
  exact intermed8_slot1_from_poly air row 1 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_12 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1083 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1083 air row) :
    intermed_8 air 1 2 (nextRow air row) = intermed_4 air 1 2 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 1 2 row - intermed_4 air 1 2 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1083,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1083
  exact intermed8_slot1_from_poly air row 2 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_13 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1086 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1086 air row) :
    intermed_8 air 1 3 (nextRow air row) = intermed_4 air 1 3 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 1 3 row - intermed_4 air 1 3 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1086,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1086
  exact intermed8_slot1_from_poly air row 3 hrow hrot hgate hpoly

/-- Slot-1 branch of `intermed_8_carry`. -/
theorem intermed_8_carry_slot1 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 2 ≤ n ∧ n ≤ 17 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_8 air 1 limb (nextRow air row) = intermed_4 air 1 limb row := by
  have hgate := intermed8Slot0CarryGateNext_eq_one air row hrow hrot hf_next hrow_idx
  rcases hs with ⟨h1050_1099, _, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1050_1099 at h1050_1099
  have h1065_1099 := h1050_1099.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h1068_1099 := h1065_1099.2.2.2
  have h1071_1099 := h1068_1099.2.2.2
  have h1074_1099 := h1071_1099.2.2.2
  have h1077_1099 := h1074_1099.2.2.2
  have h1080_1099 := h1077_1099.2.2.2
  have h1083_1099 := h1080_1099.2.2.2
  have h1077 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1077 air row := h1077_1099.1
  have h1080 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1080 air row := h1080_1099.1
  have h1083 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1083 air row := h1083_1099.1
  have h1086 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1086 air row := h1083_1099.2.2.2.1
  interval_cases limb
  · exact intermed8_carry_10 air row hrow hrot hgate h1077
  · exact intermed8_carry_11 air row hrow hrot hgate h1080
  · exact intermed8_carry_12 air row hrow hrot hgate h1083
  · exact intermed8_carry_13 air row hrow hrot hgate h1086

/-! ### intermed_8 slot 2 -/

set_option maxHeartbeats 10000000 in
private theorem intermed8_slot2_from_poly (air : C FBB ExtF) (row limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 2 limb row - intermed_4 air 2 limb row) = 0) :
    intermed_8 air 2 limb (nextRow air row) = intermed_4 air 2 limb row := by
  rw [hgate, one_mul] at hpoly
  have hraw : next_intermed_8 air 2 limb row = intermed_4 air 2 limb row :=
    sub_eq_zero.mp hpoly
  simpa [next_intermed_8_eq_nextRow air hrot 2 limb row hrow] using hraw

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_20 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1089 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1089 air row) :
    intermed_8 air 2 0 (nextRow air row) = intermed_4 air 2 0 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 2 0 row - intermed_4 air 2 0 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1089,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1089
  exact intermed8_slot2_from_poly air row 0 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_21 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1092 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1092 air row) :
    intermed_8 air 2 1 (nextRow air row) = intermed_4 air 2 1 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 2 1 row - intermed_4 air 2 1 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1092,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1092
  exact intermed8_slot2_from_poly air row 1 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_22 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1095 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1095 air row) :
    intermed_8 air 2 2 (nextRow air row) = intermed_4 air 2 2 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 2 2 row - intermed_4 air 2 2 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1095,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1095
  exact intermed8_slot2_from_poly air row 2 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_23 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1098 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1098 air row) :
    intermed_8 air 2 3 (nextRow air row) = intermed_4 air 2 3 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 2 3 row - intermed_4 air 2 3 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1098,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1098
  exact intermed8_slot2_from_poly air row 3 hrow hrot hgate hpoly

/-- Slot-2 branch of `intermed_8_carry`. -/
theorem intermed_8_carry_slot2 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 2 ≤ n ∧ n ≤ 17 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_8 air 2 limb (nextRow air row) = intermed_4 air 2 limb row := by
  have hgate := intermed8Slot0CarryGateNext_eq_one air row hrow hrot hf_next hrow_idx
  rcases hs with ⟨h1050_1099, _, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1050_1099 at h1050_1099
  have h1065_1099 := h1050_1099.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h1068_1099 := h1065_1099.2.2.2
  have h1071_1099 := h1068_1099.2.2.2
  have h1074_1099 := h1071_1099.2.2.2
  have h1077_1099 := h1074_1099.2.2.2
  have h1080_1099 := h1077_1099.2.2.2
  have h1083_1099 := h1080_1099.2.2.2
  have h1086_1099 := h1083_1099.2.2.2
  have h1089_1099 := h1086_1099.2.2.2
  have h1092_1099 := h1089_1099.2.2.2
  have h1095_1099 := h1092_1099.2.2.2
  have h1089 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1089 air row := h1089_1099.1
  have h1092 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1092 air row := h1092_1099.1
  have h1095 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1095 air row := h1095_1099.1
  have h1098 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1098 air row := h1095_1099.2.2.2.1
  interval_cases limb
  · exact intermed8_carry_20 air row hrow hrot hgate h1089
  · exact intermed8_carry_21 air row hrow hrot hgate h1092
  · exact intermed8_carry_22 air row hrow hrot hgate h1095
  · exact intermed8_carry_23 air row hrow hrot hgate h1098

/-! ### intermed_8 slot 3 -/

set_option maxHeartbeats 10000000 in
private theorem intermed8_slot3_from_poly (air : C FBB ExtF) (row limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 3 limb row - intermed_4 air 3 limb row) = 0) :
    intermed_8 air 3 limb (nextRow air row) = intermed_4 air 3 limb row := by
  rw [hgate, one_mul] at hpoly
  have hraw : next_intermed_8 air 3 limb row = intermed_4 air 3 limb row :=
    sub_eq_zero.mp hpoly
  simpa [next_intermed_8_eq_nextRow air hrot 3 limb row hrow] using hraw

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_30 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1101 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1101 air row) :
    intermed_8 air 3 0 (nextRow air row) = intermed_4 air 3 0 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 3 0 row - intermed_4 air 3 0 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1101,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1101
  exact intermed8_slot3_from_poly air row 0 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_31 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1104 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1104 air row) :
    intermed_8 air 3 1 (nextRow air row) = intermed_4 air 3 1 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 3 1 row - intermed_4 air 3 1 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1104,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1104
  exact intermed8_slot3_from_poly air row 1 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_32 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1107 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1107 air row) :
    intermed_8 air 3 2 (nextRow air row) = intermed_4 air 3 2 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 3 2 row - intermed_4 air 3 2 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1107,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1107
  exact intermed8_slot3_from_poly air row 2 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed8_carry_33 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed8Slot0CarryGateNext air row = 1)
    (h1110 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1110 air row) :
    intermed_8 air 3 3 (nextRow air row) = intermed_4 air 3 3 row := by
  have hpoly :
      intermed8Slot0CarryGateNext air row *
        (next_intermed_8 air 3 3 row - intermed_4 air 3 3 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1110,
      intermed8Slot0CarryGateNext, intermed8Slot0CarryGatePoly, next_intermed_8, intermed_4,
      encoder_idx_next] using h1110
  exact intermed8_slot3_from_poly air row 3 hrow hrot hgate hpoly

/-- Slot-3 branch of `intermed_8_carry`. -/
theorem intermed_8_carry_slot3 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 2 ≤ n ∧ n ≤ 17 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_8 air 3 limb (nextRow air row) = intermed_4 air 3 limb row := by
  have hgate := intermed8Slot0CarryGateNext_eq_one air row hrow hrot hf_next hrow_idx
  rcases hs with ⟨h1050_1099, h1100_1149, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1100_1149 at h1100_1149
  have h1101_1149 := h1100_1149.2
  have h1104_1149 := h1101_1149.2.2.2
  have h1107_1149 := h1104_1149.2.2.2
  have h1110_1149 := h1107_1149.2.2.2
  have h1101 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1101 air row := h1101_1149.1
  have h1104 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1104 air row := h1104_1149.1
  have h1107 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1107 air row := h1107_1149.1
  have h1110 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1110 air row := h1110_1149.1
  interval_cases limb
  · exact intermed8_carry_30 air row hrow hrot hgate h1101
  · exact intermed8_carry_31 air row hrow hrot hgate h1104
  · exact intermed8_carry_32 air row hrow hrot hgate h1107
  · exact intermed8_carry_33 air row hrow hrot hgate h1110

/-! ### intermed_8 dispatcher -/

set_option maxHeartbeats 10000000 in
/-- `intermed_8` carries forward `intermed_4` when the successor selector is in
    `2..17`. -/
theorem intermed_8_carry (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 2 ≤ n ∧ n ≤ 17 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_8 air slot limb (nextRow air row) = intermed_4 air slot limb row := by
  rcases hrow_idx with ⟨n, hnlo, hnhi, hsel⟩
  interval_cases slot
  · exact intermed_8_carry_slot0 air row limb hlimb hrow hrot hs hf_next ⟨n, hnlo, hnhi, hsel⟩
  · exact intermed_8_carry_slot1 air row limb hlimb hrow hrot hs hf_next
      ⟨n, hnlo, by omega, hsel⟩
  · exact intermed_8_carry_slot2 air row limb hlimb hrow hrot hs hf_next
      ⟨n, hnlo, by omega, hsel⟩
  · exact intermed_8_carry_slot3 air row limb hlimb hrow hrot hs hf_next
      ⟨n, hnlo, by omega, hsel⟩

/-! ### intermed_12 extracted gate -/

def intermed12ExtractedCarryGatePoly (d0 d1 d2 d3 d4 d5 : FBB) : FBB :=
  let s := d0 + d1 + d2 + d3 + d4 + d5
  d4 * (2 - s) +
  d4 * d5 +
  d4 * (d4 - 1) * 1006632961 +
  d3 * (2 - s) +
  d3 * d5 +
  d3 * d4 +
  d3 * (d3 - 1) * 1006632961 +
  d2 * (2 - s) +
  d2 * d5 +
  d2 * d4 +
  d2 * d3 +
  d2 * (d2 - 1) * 1006632961 +
  d1 * (2 - s) +
  d1 * d5 +
  d1 * d4 +
  d1 * d3

def intermed12ExtractedCarryGateNext (air : C FBB ExtF) (row : ℕ) : FBB :=
  intermed12ExtractedCarryGatePoly
    (encoder_idx_next air 0 row)
    (encoder_idx_next air 1 row)
    (encoder_idx_next air 2 row)
    (encoder_idx_next air 3 row)
    (encoder_idx_next air 4 row)
    (encoder_idx_next air 5 row)

private theorem intermed12_extracted_gate_lookup_fin :
    ∀ n0 n1 n2 n3 n4 n5 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val + n5.val ≤ 2 →
      encoderConstraint11Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = 0 →
      (intermed12ExtractedCarryGatePoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = 1 ↔
        ∃ sel : Fin 16,
          encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
            (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = ((sel.val + 3 : ℕ) : FBB)) := by
  decide

theorem intermed12ExtractedCarryGateNext_eq_one (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 3 ≤ n ∧ n ≤ 18 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed12ExtractedCarryGateNext air row = 1 := by
  have hf_next' := hf_next
  rcases hf_next with ⟨_, _, _, _, _, _, _, _, _, _, _, h11, _, _, _, _, _⟩
  have hd0 := encoder_digits_ternary air (nextRow air row) hf_next' 0 (by omega)
  have hd1 := encoder_digits_ternary air (nextRow air row) hf_next' 1 (by omega)
  have hd2 := encoder_digits_ternary air (nextRow air row) hf_next' 2 (by omega)
  have hd3 := encoder_digits_ternary air (nextRow air row) hf_next' 3 (by omega)
  have hd4 := encoder_digits_ternary air (nextRow air row) hf_next' 4 (by omega)
  have hd5 := encoder_digits_ternary air (nextRow air row) hf_next' 5 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 (nextRow air row)) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 (nextRow air row)) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 (nextRow air row)) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 (nextRow air row)) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 (nextRow air row)) hd4 with ⟨n4, h4⟩
  rcases ternary_as_fin3 (encoder_idx air 5 (nextRow air row)) hd5 with ⟨n5, h5⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val + n5.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4, h5] using
      encoder_digit_sum_ternary air (nextRow air row) hf_next'
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hc11 : encoderConstraint11Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
      (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = 0 := by
    simpa [encoderConstraint11Poly, constraint_11, encoder_choose2, h0, h1, h2, h3, h4, h5]
      using h11
  rcases hrow_idx with ⟨n, hnlo, hnhi, hsel⟩
  let sel : Fin 16 := ⟨n - 3, by omega⟩
  have hsel_shift :
      ∃ sel' : Fin 16,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = ((sel'.val + 3 : ℕ) : FBB) := by
    refine ⟨sel, ?_⟩
    have hsel_nat : sel.val + 3 = n := by
      simp [sel]
      omega
    calc
      encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) =
          encoder_selector_idx air (nextRow air row) := by
            simp [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
              encoderSelectorPoly, h0, h1, h2, h3, h4, h5]
      _ = (n : FBB) := hsel
      _ = ((sel.val + 3 : ℕ) : FBB) := by
            rw [← hsel_nat]
  have hgate :
      intermed12ExtractedCarryGatePoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) (n5.val : FBB) = 1 := by
    exact (intermed12_extracted_gate_lookup_fin n0 n1 n2 n3 n4 n5 htotal_le hc11).mpr hsel_shift
  rw [intermed12ExtractedCarryGateNext]
  rw [encoder_idx_next_eq_nextRow air hrot 0 row hrow,
    encoder_idx_next_eq_nextRow air hrot 1 row hrow,
    encoder_idx_next_eq_nextRow air hrot 2 row hrow,
    encoder_idx_next_eq_nextRow air hrot 3 row hrow,
    encoder_idx_next_eq_nextRow air hrot 4 row hrow,
    encoder_idx_next_eq_nextRow air hrot 5 row hrow]
  simpa [h0, h1, h2, h3, h4, h5] using hgate

/-! ### intermed_12 slot 0 -/

set_option maxHeartbeats 10000000 in
private theorem intermed12_slot0_from_poly (air : C FBB ExtF) (row limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 0 limb row - intermed_8 air 0 limb row) = 0) :
    intermed_12 air 0 limb (nextRow air row) = intermed_8 air 0 limb row := by
  rw [hgate, one_mul] at hpoly
  have hraw : next_intermed_12 air 0 limb row = intermed_8 air 0 limb row :=
    sub_eq_zero.mp hpoly
  simpa [next_intermed_12_eq_nextRow air hrot 0 limb row hrow] using hraw

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_00 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1066 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1066 air row) :
    intermed_12 air 0 0 (nextRow air row) = intermed_8 air 0 0 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 0 0 row - intermed_8 air 0 0 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1066,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1066
  exact intermed12_slot0_from_poly air row 0 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_01 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1069 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1069 air row) :
    intermed_12 air 0 1 (nextRow air row) = intermed_8 air 0 1 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 0 1 row - intermed_8 air 0 1 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1069,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1069
  exact intermed12_slot0_from_poly air row 1 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_02 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1072 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1072 air row) :
    intermed_12 air 0 2 (nextRow air row) = intermed_8 air 0 2 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 0 2 row - intermed_8 air 0 2 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1072,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1072
  exact intermed12_slot0_from_poly air row 2 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_03 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1075 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1075 air row) :
    intermed_12 air 0 3 (nextRow air row) = intermed_8 air 0 3 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 0 3 row - intermed_8 air 0 3 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1075,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1075
  exact intermed12_slot0_from_poly air row 3 hrow hrot hgate hpoly

/-- Slot-0 branch of `intermed_12_carry`. -/
theorem intermed_12_carry_slot0 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 3 ≤ n ∧ n ≤ 18 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_12 air 0 limb (nextRow air row) = intermed_8 air 0 limb row := by
  have hgate := intermed12ExtractedCarryGateNext_eq_one air row hrow hrot hf_next hrow_idx
  rcases hs with ⟨h1050_1099, _, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1050_1099 at h1050_1099
  have h1065_1099 := h1050_1099.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h1066_1099 := h1065_1099.2
  have h1069_1099 := h1066_1099.2.2.2
  have h1072_1099 := h1069_1099.2.2.2
  have h1075_1099 := h1072_1099.2.2.2
  have h1066 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1066 air row := h1066_1099.1
  have h1069 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1069 air row := h1069_1099.1
  have h1072 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1072 air row := h1072_1099.1
  have h1075 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1075 air row := h1075_1099.1
  interval_cases limb
  · exact intermed12_carry_00 air row hrow hrot hgate h1066
  · exact intermed12_carry_01 air row hrow hrot hgate h1069
  · exact intermed12_carry_02 air row hrow hrot hgate h1072
  · exact intermed12_carry_03 air row hrow hrot hgate h1075

/-! ### intermed_12 slot 1 -/

set_option maxHeartbeats 10000000 in
private theorem intermed12_slot1_from_poly (air : C FBB ExtF) (row limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 1 limb row - intermed_8 air 1 limb row) = 0) :
    intermed_12 air 1 limb (nextRow air row) = intermed_8 air 1 limb row := by
  rw [hgate, one_mul] at hpoly
  have hraw : next_intermed_12 air 1 limb row = intermed_8 air 1 limb row :=
    sub_eq_zero.mp hpoly
  simpa [next_intermed_12_eq_nextRow air hrot 1 limb row hrow] using hraw

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_10 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1078 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1078 air row) :
    intermed_12 air 1 0 (nextRow air row) = intermed_8 air 1 0 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 1 0 row - intermed_8 air 1 0 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1078,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1078
  exact intermed12_slot1_from_poly air row 0 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_11 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1081 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1081 air row) :
    intermed_12 air 1 1 (nextRow air row) = intermed_8 air 1 1 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 1 1 row - intermed_8 air 1 1 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1081,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1081
  exact intermed12_slot1_from_poly air row 1 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_12 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1084 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1084 air row) :
    intermed_12 air 1 2 (nextRow air row) = intermed_8 air 1 2 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 1 2 row - intermed_8 air 1 2 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1084,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1084
  exact intermed12_slot1_from_poly air row 2 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_13 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1087 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1087 air row) :
    intermed_12 air 1 3 (nextRow air row) = intermed_8 air 1 3 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 1 3 row - intermed_8 air 1 3 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1087,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1087
  exact intermed12_slot1_from_poly air row 3 hrow hrot hgate hpoly

/-- Slot-1 branch of `intermed_12_carry`. -/
theorem intermed_12_carry_slot1 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 3 ≤ n ∧ n ≤ 18 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_12 air 1 limb (nextRow air row) = intermed_8 air 1 limb row := by
  have hgate := intermed12ExtractedCarryGateNext_eq_one air row hrow hrot hf_next hrow_idx
  rcases hs with ⟨h1050_1099, _, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1050_1099 at h1050_1099
  have h1065_1099 := h1050_1099.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h1066_1099 := h1065_1099.2
  have h1069_1099 := h1066_1099.2.2.2
  have h1072_1099 := h1069_1099.2.2.2
  have h1075_1099 := h1072_1099.2.2.2
  have h1078_1099 := h1075_1099.2.2.2
  have h1081_1099 := h1078_1099.2.2.2
  have h1084_1099 := h1081_1099.2.2.2
  have h1078 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1078 air row := h1078_1099.1
  have h1081 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1081 air row := h1081_1099.1
  have h1084 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1084 air row := h1084_1099.1
  have h1087 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1087 air row := h1084_1099.2.2.2.1
  interval_cases limb
  · exact intermed12_carry_10 air row hrow hrot hgate h1078
  · exact intermed12_carry_11 air row hrow hrot hgate h1081
  · exact intermed12_carry_12 air row hrow hrot hgate h1084
  · exact intermed12_carry_13 air row hrow hrot hgate h1087

/-! ### intermed_12 slot 2 -/

set_option maxHeartbeats 10000000 in
private theorem intermed12_slot2_from_poly (air : C FBB ExtF) (row limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 2 limb row - intermed_8 air 2 limb row) = 0) :
    intermed_12 air 2 limb (nextRow air row) = intermed_8 air 2 limb row := by
  rw [hgate, one_mul] at hpoly
  have hraw : next_intermed_12 air 2 limb row = intermed_8 air 2 limb row :=
    sub_eq_zero.mp hpoly
  simpa [next_intermed_12_eq_nextRow air hrot 2 limb row hrow] using hraw

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_20 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1090 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1090 air row) :
    intermed_12 air 2 0 (nextRow air row) = intermed_8 air 2 0 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 2 0 row - intermed_8 air 2 0 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1090,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1090
  exact intermed12_slot2_from_poly air row 0 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_21 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1093 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1093 air row) :
    intermed_12 air 2 1 (nextRow air row) = intermed_8 air 2 1 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 2 1 row - intermed_8 air 2 1 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1093,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1093
  exact intermed12_slot2_from_poly air row 1 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_22 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1096 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1096 air row) :
    intermed_12 air 2 2 (nextRow air row) = intermed_8 air 2 2 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 2 2 row - intermed_8 air 2 2 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1096,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1096
  exact intermed12_slot2_from_poly air row 2 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_23 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1099 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1099 air row) :
    intermed_12 air 2 3 (nextRow air row) = intermed_8 air 2 3 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 2 3 row - intermed_8 air 2 3 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1099,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1099
  exact intermed12_slot2_from_poly air row 3 hrow hrot hgate hpoly

/-- Slot-2 branch of `intermed_12_carry`. -/
theorem intermed_12_carry_slot2 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 3 ≤ n ∧ n ≤ 18 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_12 air 2 limb (nextRow air row) = intermed_8 air 2 limb row := by
  have hgate := intermed12ExtractedCarryGateNext_eq_one air row hrow hrot hf_next hrow_idx
  rcases hs with ⟨h1050_1099, _, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1050_1099 at h1050_1099
  have h1065_1099 := h1050_1099.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h1066_1099 := h1065_1099.2
  have h1069_1099 := h1066_1099.2.2.2
  have h1072_1099 := h1069_1099.2.2.2
  have h1075_1099 := h1072_1099.2.2.2
  have h1078_1099 := h1075_1099.2.2.2
  have h1081_1099 := h1078_1099.2.2.2
  have h1084_1099 := h1081_1099.2.2.2
  have h1087_1099 := h1084_1099.2.2.2
  have h1090_1099 := h1087_1099.2.2.2
  have h1093_1099 := h1090_1099.2.2.2
  have h1096_1099 := h1093_1099.2.2.2
  have h1090 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1090 air row := h1090_1099.1
  have h1093 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1093 air row := h1093_1099.1
  have h1096 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1096 air row := h1096_1099.1
  have h1099 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1099 air row := h1096_1099.2.2.2
  interval_cases limb
  · exact intermed12_carry_20 air row hrow hrot hgate h1090
  · exact intermed12_carry_21 air row hrow hrot hgate h1093
  · exact intermed12_carry_22 air row hrow hrot hgate h1096
  · exact intermed12_carry_23 air row hrow hrot hgate h1099

/-! ### intermed_12 slot 3 -/

set_option maxHeartbeats 10000000 in
private theorem intermed12_slot3_from_poly (air : C FBB ExtF) (row limb : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 3 limb row - intermed_8 air 3 limb row) = 0) :
    intermed_12 air 3 limb (nextRow air row) = intermed_8 air 3 limb row := by
  rw [hgate, one_mul] at hpoly
  have hraw : next_intermed_12 air 3 limb row = intermed_8 air 3 limb row :=
    sub_eq_zero.mp hpoly
  simpa [next_intermed_12_eq_nextRow air hrot 3 limb row hrow] using hraw

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_30 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1102 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1102 air row) :
    intermed_12 air 3 0 (nextRow air row) = intermed_8 air 3 0 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 3 0 row - intermed_8 air 3 0 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1102,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1102
  exact intermed12_slot3_from_poly air row 0 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_31 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1105 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1105 air row) :
    intermed_12 air 3 1 (nextRow air row) = intermed_8 air 3 1 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 3 1 row - intermed_8 air 3 1 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1105,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1105
  exact intermed12_slot3_from_poly air row 1 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_32 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1108 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1108 air row) :
    intermed_12 air 3 2 (nextRow air row) = intermed_8 air 3 2 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 3 2 row - intermed_8 air 3 2 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1108,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1108
  exact intermed12_slot3_from_poly air row 2 hrow hrot hgate hpoly

set_option maxHeartbeats 10000000 in
private theorem intermed12_carry_33 (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hgate : intermed12ExtractedCarryGateNext air row = 1)
    (h1111 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1111 air row) :
    intermed_12 air 3 3 (nextRow air row) = intermed_8 air 3 3 row := by
  have hpoly :
      intermed12ExtractedCarryGateNext air row *
        (next_intermed_12 air 3 3 row - intermed_8 air 3 3 row) = 0 := by
    simpa only [Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1111,
      intermed12ExtractedCarryGateNext, intermed12ExtractedCarryGatePoly, next_intermed_12,
      intermed_8, encoder_idx_next] using h1111
  exact intermed12_slot3_from_poly air row 3 hrow hrot hgate hpoly

/-- Slot-3 branch of `intermed_12_carry`. -/
theorem intermed_12_carry_slot3 (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 3 ≤ n ∧ n ≤ 18 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_12 air 3 limb (nextRow air row) = intermed_8 air 3 limb row := by
  have hgate := intermed12ExtractedCarryGateNext_eq_one air row hrow hrot hf_next hrow_idx
  rcases hs with ⟨h1050_1099, h1100_1149, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1100_1149 at h1100_1149
  have h1101_1149 := h1100_1149.2
  have h1102_1149 := h1101_1149.2
  have h1105_1149 := h1102_1149.2.2.2
  have h1108_1149 := h1105_1149.2.2.2
  have h1111_1149 := h1108_1149.2.2.2
  have h1102 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1102 air row := h1102_1149.1
  have h1105 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1105 air row := h1105_1149.1
  have h1108 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1108 air row := h1108_1149.1
  have h1111 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1111 air row := h1111_1149.1
  interval_cases limb
  · exact intermed12_carry_30 air row hrow hrot hgate h1102
  · exact intermed12_carry_31 air row hrow hrot hgate h1105
  · exact intermed12_carry_32 air row hrow hrot hgate h1108
  · exact intermed12_carry_33 air row hrow hrot hgate h1111

/-! ### intermed_12 dispatcher -/

set_option maxHeartbeats 10000000 in
/-- `intermed_12` carries forward `intermed_8` when the successor selector is in
    `3..18`. -/
theorem intermed_12_carry (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 3 ≤ n ∧ n ≤ 18 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed_12 air slot limb (nextRow air row) = intermed_8 air slot limb row := by
  interval_cases slot
  · exact intermed_12_carry_slot0 air row limb hlimb hrow hrot hs hf_next hrow_idx
  · exact intermed_12_carry_slot1 air row limb hlimb hrow hrot hs hf_next hrow_idx
  · exact intermed_12_carry_slot2 air row limb hlimb hrow hrot hs hf_next hrow_idx
  · exact intermed_12_carry_slot3 air row limb hlimb hrow hrot hs hf_next hrow_idx

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
