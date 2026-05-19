/-
  Layer A: Per-Row Facts (Selector Continuation)

  Builds the flag-consistency consequences on top of the selector-core lookup
  lemmas in `SelectorCore.lean`.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.SelectorCore

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## Flag-selector consistency (constraints 12-15) -/

/-- `is_round_row = 1` ↔ `encoder_selector_idx ∈ {0,...,15}`. -/
theorem is_round_iff_selector_lt_16 (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    is_round_row air row = 1 ↔ ∃ n : ℕ, n < 16 ∧ encoder_selector_idx air row = (n : FBB) := by
  have hf' := hf
  rcases hf' with ⟨_, _, _, _, _, _, _, _, _, _, h10, _, _, h13, _, _⟩
  have hd0 := encoder_digits_ternary air row hf 0 (by omega)
  have hd1 := encoder_digits_ternary air row hf 1 (by omega)
  have hd2 := encoder_digits_ternary air row hf 2 (by omega)
  have hd3 := encoder_digits_ternary air row hf 3 (by omega)
  have hd4 := encoder_digits_ternary air row hf 4 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 row) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 row) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 row) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 row) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 row) hd4 with ⟨n4, h4⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4] using
      encoder_digit_sum_ternary air row hf
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hc10 : encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 := by
    have h10c : constraint_10 air row := (constraint_10_of_extraction air row).mp h10
    simpa [encoderConstraint10Poly, constraint_10, encoder_choose2, h0, h1, h2] using h10c
  have hpoly_eq : encoderRoundPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
      (n3.val : FBB) (n4.val : FBB) = is_round_row air row := by
    have hzero : encoderRoundPoly (encoder_idx air 0 row) (encoder_idx air 1 row)
        (encoder_idx air 2 row) (encoder_idx air 3 row) (encoder_idx air 4 row) -
        is_round_row air row = 0 := by
      simpa [constraint_13, encoderRoundPoly, encoder_choose2] using h13
    exact by simpa [h0, h1, h2, h3, h4] using sub_eq_zero.mp hzero
  constructor
  · intro hround
    have hpoly_one : encoderRoundPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = 1 := by
      calc
        encoderRoundPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) (n3.val : FBB) (n4.val : FBB)
            = is_round_row air row := hpoly_eq
        _ = 1 := hround
    rcases (round_indicator_lookup_fin n0 n1 n2 n3 n4 htotal_le hc10).mp hpoly_one with
        ⟨sel, hsel⟩
    exact ⟨sel.val, sel.isLt, by
      simpa [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
        encoderSelectorPoly, h0, h1, h2, h3, h4] using hsel⟩
  · rintro ⟨n, hn, hsel⟩
    let sel : Fin 16 := ⟨n, hn⟩
    have hsel' :
        ∃ sel' : Fin 16,
          encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
            (n3.val : FBB) (n4.val : FBB) = (sel'.val : FBB) := by
      refine ⟨sel, ?_⟩
      simpa [sel, encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
        encoderSelectorPoly, h0, h1, h2, h3, h4] using hsel
    have hpoly_one := (round_indicator_lookup_fin n0 n1 n2 n3 n4 htotal_le hc10).mpr hsel'
    calc
      is_round_row air row = encoderRoundPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) := hpoly_eq.symm
      _ = 1 := hpoly_one

/-- `is_first_4_rows = 1` ↔ `encoder_selector_idx ∈ {0,...,3}`. -/
theorem is_first_4_iff_selector_lt_4 (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    is_first_4_rows air row = 1 ↔ ∃ n : ℕ, n < 4 ∧ encoder_selector_idx air row = (n : FBB) := by
  have hf' := hf
  rcases hf' with ⟨_, _, _, _, _, _, _, _, _, _, h10, _, h12, _, _, _⟩
  have hd0 := encoder_digits_ternary air row hf 0 (by omega)
  have hd1 := encoder_digits_ternary air row hf 1 (by omega)
  have hd2 := encoder_digits_ternary air row hf 2 (by omega)
  have hd3 := encoder_digits_ternary air row hf 3 (by omega)
  have hd4 := encoder_digits_ternary air row hf 4 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 row) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 row) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 row) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 row) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 row) hd4 with ⟨n4, h4⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4] using
      encoder_digit_sum_ternary air row hf
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hc10 : encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 := by
    have h10c : constraint_10 air row := (constraint_10_of_extraction air row).mp h10
    simpa [encoderConstraint10Poly, constraint_10, encoder_choose2, h0, h1, h2] using h10c
  have hpoly_eq : encoderFirst4Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
      (n3.val : FBB) (n4.val : FBB) = is_first_4_rows air row := by
    have hzero : encoderFirst4Poly (encoder_idx air 0 row) (encoder_idx air 1 row)
        (encoder_idx air 2 row) (encoder_idx air 3 row) (encoder_idx air 4 row) -
        is_first_4_rows air row = 0 := by
      simpa [constraint_12, encoderFirst4Poly, encoder_choose2] using h12
    exact by simpa [h0, h1, h2, h3, h4] using sub_eq_zero.mp hzero
  constructor
  · intro hfirst4
    have hpoly_one : encoderFirst4Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = 1 := by
      calc
        encoderFirst4Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) (n3.val : FBB) (n4.val : FBB)
            = is_first_4_rows air row := hpoly_eq
        _ = 1 := hfirst4
    rcases (first4_indicator_lookup_fin n0 n1 n2 n3 n4 htotal_le hc10).mp hpoly_one with
        ⟨sel, hsel⟩
    exact ⟨sel.val, sel.isLt, by
      simpa [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
        encoderSelectorPoly, h0, h1, h2, h3, h4] using hsel⟩
  · rintro ⟨n, hn, hsel⟩
    let sel : Fin 4 := ⟨n, hn⟩
    have hsel' :
        ∃ sel' : Fin 4,
          encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
            (n3.val : FBB) (n4.val : FBB) = (sel'.val : FBB) := by
      refine ⟨sel, ?_⟩
      simpa [sel, encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
        encoderSelectorPoly, h0, h1, h2, h3, h4] using hsel
    have hpoly_one := (first4_indicator_lookup_fin n0 n1 n2 n3 n4 htotal_le hc10).mpr hsel'
    calc
      is_first_4_rows air row = encoderFirst4Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) := hpoly_eq.symm
      _ = 1 := hpoly_one

/-- `is_digest_row = 1` ↔ `encoder_selector_idx = 16`. -/
theorem is_digest_iff_selector_eq_16 (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    is_digest_row air row = 1 ↔ encoder_selector_idx air row = 16 := by
  have hf' := hf
  rcases hf' with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h14, _⟩
  have hd0 := encoder_digits_ternary air row hf 0 (by omega)
  have hd1 := encoder_digits_ternary air row hf 1 (by omega)
  have hd2 := encoder_digits_ternary air row hf 2 (by omega)
  have hd3 := encoder_digits_ternary air row hf 3 (by omega)
  have hd4 := encoder_digits_ternary air row hf 4 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 row) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 row) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 row) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 row) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 row) hd4 with ⟨n4, h4⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4] using
      encoder_digit_sum_ternary air row hf
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hprod_eq : (n0.val : FBB) * (n4.val : FBB) = is_digest_row air row := by
    have hzero : encoder_idx air 0 row * encoder_idx air 4 row - is_digest_row air row = 0 := by
      simpa [constraint_14] using h14
    exact by simpa [h0, h4] using sub_eq_zero.mp hzero
  constructor
  · intro hdigest
    have hprod_one : (n0.val : FBB) * (n4.val : FBB) = 1 := by
      calc
        (n0.val : FBB) * (n4.val : FBB) = is_digest_row air row := hprod_eq
        _ = 1 := hdigest
    have hsel := (digest_indicator_lookup_fin n0 n1 n2 n3 n4 htotal_le).mp hprod_one
    simpa [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
      encoderSelectorPoly, h0, h1, h2, h3, h4] using hsel
  · intro hsel
    have hprod_one := (digest_indicator_lookup_fin n0 n1 n2 n3 n4 htotal_le).mpr <| by
      simpa [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from,
        encoderSelectorPoly, h0, h1, h2, h3, h4] using hsel
    calc
      is_digest_row air row = (n0.val : FBB) * (n4.val : FBB) := hprod_eq.symm
      _ = 1 := hprod_one

/-- Assembly: flag_constraints → flagsWellFormed. -/
theorem flagsWellFormed_of_flag_constraints (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    flagsWellFormed air row :=
  ⟨is_round_row_boolean air row hf,
   is_first_4_rows_boolean air row hf,
   is_digest_row_boolean air row hf,
   round_plus_digest_boolean air row hf,
   encoder_digits_ternary air row hf⟩

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
