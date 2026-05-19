/- 
  Layer B: Message Schedule Correctness (Carry Gates)

  Small finite-lookup helpers for the schedule pipeline carry gates.
  These are separated from the core schedule proof so the gate lookup facts
  stay grouped around the selector arithmetic they justify.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.SelectorCore

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

def intermed8CarryGatePoly (d0 d1 d2 d3 d4 : FBB) : FBB :=
  let s := d0 + d1 + d2 + d3 + d4
  d4 * (d4 - 1) * 1006632961 +
  d3 * (2 - s) +
  d3 * d4 +
  d3 * (d3 - 1) * 1006632961 +
  d2 * (2 - s) +
  d2 * d4 +
  d2 * d3 +
  d2 * (d2 - 1) * 1006632961 +
  d1 * (2 - s) +
  d1 * d4 +
  d1 * d3 +
  d1 * d2

def intermed12CarryGatePoly (d0 d1 d2 d3 d4 : FBB) : FBB :=
  let s := d0 + d1 + d2 + d3 + d4
  d3 * (2 - s) +
  d3 * d4 +
  d3 * (d3 - 1) * 1006632961 +
  d2 * (2 - s) +
  d2 * d4 +
  d2 * d3 +
  d2 * (d2 - 1) * 1006632961 +
  d1 * (2 - s) +
  d1 * d4 +
  d1 * d3 +
  d1 * d2 +
  d1 * (d1 - 1) * 1006632961

def intermed8CarryGateNext (air : C FBB ExtF) (row : ℕ) : FBB :=
  intermed8CarryGatePoly
    (encoder_idx_next air 0 row)
    (encoder_idx_next air 1 row)
    (encoder_idx_next air 2 row)
    (encoder_idx_next air 3 row)
    (encoder_idx_next air 4 row)

def intermed12CarryGateNext (air : C FBB ExtF) (row : ℕ) : FBB :=
  intermed12CarryGatePoly
    (encoder_idx_next air 0 row)
    (encoder_idx_next air 1 row)
    (encoder_idx_next air 2 row)
    (encoder_idx_next air 3 row)
    (encoder_idx_next air 4 row)

private theorem intermed8_gate_lookup_fin :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      (intermed8CarryGatePoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = 1 ↔
        ∃ sel : Fin 12,
          encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
            (n3.val : FBB) (n4.val : FBB) = ((sel.val + 2 : ℕ) : FBB)) := by
  native_decide

private theorem intermed12_gate_lookup_fin :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      (intermed12CarryGatePoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = 1 ↔
        ∃ sel : Fin 12,
          encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
            (n3.val : FBB) (n4.val : FBB) = ((sel.val + 3 : ℕ) : FBB)) := by
  native_decide

theorem intermed8CarryGateNext_eq_one (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 2 ≤ n ∧ n ≤ 13 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed8CarryGateNext air row = 1 := by
  have hf_next' := hf_next
  rcases hf_next with ⟨_, _, _, _, _, _, _, _, _, _, h10, _, _, _, _, _⟩
  have hd0 := encoder_digits_ternary air (nextRow air row) hf_next' 0 (by omega)
  have hd1 := encoder_digits_ternary air (nextRow air row) hf_next' 1 (by omega)
  have hd2 := encoder_digits_ternary air (nextRow air row) hf_next' 2 (by omega)
  have hd3 := encoder_digits_ternary air (nextRow air row) hf_next' 3 (by omega)
  have hd4 := encoder_digits_ternary air (nextRow air row) hf_next' 4 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 (nextRow air row)) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 (nextRow air row)) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 (nextRow air row)) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 (nextRow air row)) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 (nextRow air row)) hd4 with ⟨n4, h4⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4] using
      encoder_digit_sum_ternary air (nextRow air row) hf_next'
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hc10 : encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 := by
    have h10c : constraint_10 air (nextRow air row) :=
      (constraint_10_of_extraction air (nextRow air row)).mp h10
    simpa [encoderConstraint10Poly, constraint_10, encoder_choose2, h0, h1, h2] using h10c
  rcases hrow_idx with ⟨n, hnlo, hnhi, hsel⟩
  let sel : Fin 12 := ⟨n - 2, by omega⟩
  have hsel_shift :
      ∃ sel' : Fin 12,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = ((sel'.val + 2 : ℕ) : FBB) := by
    refine ⟨sel, ?_⟩
    have hsel_nat : sel.val + 2 = n := by
      simp [sel]
      omega
    calc
      encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) =
          encoder_selector_idx air (nextRow air row) := by
            simp [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
              encoderSelectorPoly, h0, h1, h2, h3, h4]
      _ = (n : FBB) := hsel
      _ = ((sel.val + 2 : ℕ) : FBB) := by
            rw [← hsel_nat]
  have hgate :
      intermed8CarryGatePoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = 1 := by
    exact (intermed8_gate_lookup_fin n0 n1 n2 n3 n4 htotal_le hc10).mpr hsel_shift
  rw [intermed8CarryGateNext]
  rw [encoder_idx_next_eq_nextRow air hrot 0 row hrow,
    encoder_idx_next_eq_nextRow air hrot 1 row hrow,
    encoder_idx_next_eq_nextRow air hrot 2 row hrow,
    encoder_idx_next_eq_nextRow air hrot 3 row hrow,
    encoder_idx_next_eq_nextRow air hrot 4 row hrow]
  simpa [h0, h1, h2, h3, h4] using hgate

theorem intermed12CarryGateNext_eq_one (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hf_next : flag_constraints air (nextRow air row))
    (hrow_idx : ∃ n : ℕ, 3 ≤ n ∧ n ≤ 14 ∧
      encoder_selector_idx air (nextRow air row) = (n : FBB)) :
    intermed12CarryGateNext air row = 1 := by
  have hf_next' := hf_next
  rcases hf_next with ⟨_, _, _, _, _, _, _, _, _, _, h10, _, _, _, _, _⟩
  have hd0 := encoder_digits_ternary air (nextRow air row) hf_next' 0 (by omega)
  have hd1 := encoder_digits_ternary air (nextRow air row) hf_next' 1 (by omega)
  have hd2 := encoder_digits_ternary air (nextRow air row) hf_next' 2 (by omega)
  have hd3 := encoder_digits_ternary air (nextRow air row) hf_next' 3 (by omega)
  have hd4 := encoder_digits_ternary air (nextRow air row) hf_next' 4 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 (nextRow air row)) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 (nextRow air row)) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 (nextRow air row)) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 (nextRow air row)) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 (nextRow air row)) hd4 with ⟨n4, h4⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4] using
      encoder_digit_sum_ternary air (nextRow air row) hf_next'
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hc10 : encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 := by
    have h10c : constraint_10 air (nextRow air row) :=
      (constraint_10_of_extraction air (nextRow air row)).mp h10
    simpa [encoderConstraint10Poly, constraint_10, encoder_choose2, h0, h1, h2] using h10c
  rcases hrow_idx with ⟨n, hnlo, hnhi, hsel⟩
  let sel : Fin 12 := ⟨n - 3, by omega⟩
  have hsel_shift :
      ∃ sel' : Fin 12,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = ((sel'.val + 3 : ℕ) : FBB) := by
    refine ⟨sel, ?_⟩
    have hsel_nat : sel.val + 3 = n := by
      simp [sel]
      omega
    calc
      encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) =
          encoder_selector_idx air (nextRow air row) := by
            simp [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
              encoderSelectorPoly, h0, h1, h2, h3, h4]
      _ = (n : FBB) := hsel
      _ = ((sel.val + 3 : ℕ) : FBB) := by
            rw [← hsel_nat]
  have hgate :
      intermed12CarryGatePoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = 1 := by
    exact (intermed12_gate_lookup_fin n0 n1 n2 n3 n4 htotal_le hc10).mpr hsel_shift
  rw [intermed12CarryGateNext]
  rw [encoder_idx_next_eq_nextRow air hrot 0 row hrow,
    encoder_idx_next_eq_nextRow air hrot 1 row hrow,
    encoder_idx_next_eq_nextRow air hrot 2 row hrow,
    encoder_idx_next_eq_nextRow air hrot 3 row hrow,
    encoder_idx_next_eq_nextRow air hrot 4 row hrow]
  simpa [h0, h1, h2, h3, h4] using hgate

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
