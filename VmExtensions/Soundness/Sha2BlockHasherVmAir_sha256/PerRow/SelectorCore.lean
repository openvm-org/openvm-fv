/-
  Layer A: Per-Row Facts (Selector Core)

  Finite lookup and bounded-natural bridges for the encoder selector value.
  The flag-consistency consequences built from these helpers live in
  `SelectorFacts.lean`.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.BaseFacts

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## Encoder selector (constraint 11)

The encoder polynomial maps the 18 valid encoder points to {0,...,17}.
Split by digit sum into 3 cases (sum=0, sum=1, sum=2). -/

/-- Helper: the encoder selector polynomial applied to 5 digits. -/
def encoderSelectorPoly (d0 d1 d2 d3 d4 : FBB) : FBB :=
  let s := d0 + d1 + d2 + d3 + d4
  d4 * (2 - s) + 2 * encoder_choose2 d4 + 3 * d3 * (2 - s) +
  4 * d3 * d4 + 5 * encoder_choose2 d3 + 6 * d2 * (2 - s) +
  7 * d2 * d4 + 8 * d2 * d3 + 9 * encoder_choose2 d2 +
  10 * d1 * (2 - s) + 11 * d1 * d4 + 12 * d1 * d3 +
  13 * d1 * d2 + 14 * encoder_choose2 d1 + 15 * d0 * (2 - s) +
  16 * d0 * d4 + 17 * d0 * d3

/-- Helper: the constraint-12 polynomial indicating selectors `0..3`. -/
def encoderFirst4Poly (d0 d1 d2 d3 d4 : FBB) : FBB :=
  let s := d0 + d1 + d2 + d3 + d4
  (2 - s) * (1 - s) * 1006632961 + d4 * (2 - s) + encoder_choose2 d4 + d3 * (2 - s)

/-- Helper: the constraint-13 polynomial indicating selectors `0..15`. -/
def encoderRoundPoly (d0 d1 d2 d3 d4 : FBB) : FBB :=
  let s := d0 + d1 + d2 + d3 + d4
  (2 - s) * (1 - s) * 1006632961 + d4 * (2 - s) + encoder_choose2 d4 +
  d3 * (2 - s) + d3 * d4 + encoder_choose2 d3 + d2 * (2 - s) +
  d2 * d4 + d2 * d3 + encoder_choose2 d2 + d1 * (2 - s) + d1 * d4 +
  d1 * d3 + d1 * d2 + encoder_choose2 d1 + d0 * (2 - s)

/-- Helper: the constraint-10 polynomial ruling out unused encoder points. -/
def encoderConstraint10Poly (d0 d1 d2 : FBB) : FBB :=
  d0 * d2 + d0 * d1 + encoder_choose2 d0

theorem ternary_as_fin3 (d : FBB) (hd : d = 0 ∨ d = 1 ∨ d = 2) :
    ∃ n : Fin 3, d = (n.val : FBB) := by
  rcases hd with h | h | h
  · exact ⟨⟨0, by omega⟩, h⟩
  · exact ⟨⟨1, by omega⟩, h⟩
  · exact ⟨⟨2, by omega⟩, h⟩

private theorem nat_eq_of_small_cast_eq {m n : ℕ}
    (hm : m < BB_prime) (hn : n < BB_prime)
    (h : ((m : ℕ) : FBB) = ((n : ℕ) : FBB)) :
    m = n := by
  have hval := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at hval
  exact hval

theorem nat_sum_le_two_of_field_ternary {total : ℕ}
    (htotal : total < BB_prime)
    (hsum : ((total : ℕ) : FBB) = 0 ∨
      ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2) :
    total ≤ 2 := by
  rcases hsum with h0 | h1 | h2
  · have htotal_zero : total = 0 := by
      exact nat_eq_of_small_cast_eq htotal (by norm_num) h0
    omega
  · have htotal_one : total = 1 := by
      exact nat_eq_of_small_cast_eq htotal (by norm_num) h1
    omega
  · have htotal_two : total = 2 := by
      exact nat_eq_of_small_cast_eq htotal (by norm_num) h2
    omega

private theorem selector_lookup_fin :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      ∃ sel : Fin 18,
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = (sel.val : FBB) := by
  decide

theorem first4_indicator_lookup_fin :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      (encoderFirst4Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = 1 ↔
        ∃ sel : Fin 4,
          encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
            (n3.val : FBB) (n4.val : FBB) = (sel.val : FBB)) := by
  decide

theorem round_indicator_lookup_fin :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderConstraint10Poly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB) = 0 →
      (encoderRoundPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = 1 ↔
        ∃ sel : Fin 16,
          encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
            (n3.val : FBB) (n4.val : FBB) = (sel.val : FBB)) := by
  decide

theorem digest_indicator_lookup_fin :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      (((n0.val : FBB) * (n4.val : FBB) = 1) ↔
        encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
          (n3.val : FBB) (n4.val : FBB) = 16) := by
  decide

/-- Combined: 18 valid encodings → selector ∈ 0..17. Case split on digit sum. -/
theorem encoder_selector_of_ternary_digits (d0 d1 d2 d3 d4 : FBB)
    (hd0 : d0 = 0 ∨ d0 = 1 ∨ d0 = 2) (hd1 : d1 = 0 ∨ d1 = 1 ∨ d1 = 2)
    (hd2 : d2 = 0 ∨ d2 = 1 ∨ d2 = 2) (hd3 : d3 = 0 ∨ d3 = 1 ∨ d3 = 2)
    (hd4 : d4 = 0 ∨ d4 = 1 ∨ d4 = 2)
    (hsum : d0 + d1 + d2 + d3 + d4 = 0 ∨ d0 + d1 + d2 + d3 + d4 = 1 ∨
            d0 + d1 + d2 + d3 + d4 = 2) :
    ∃ n : ℕ, n ≤ 17 ∧ encoderSelectorPoly d0 d1 d2 d3 d4 = (n : FBB) := by
  rcases ternary_as_fin3 d0 hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 d1 hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 d2 hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 d3 hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 d4 hd4 with ⟨n4, h4⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, h0, h1, h2, h3, h4] using hsum
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  rcases selector_lookup_fin n0 n1 n2 n3 n4 htotal_le with ⟨sel, hsel⟩
  exact ⟨sel.val, Nat.le_of_lt_succ sel.isLt, by simpa [h0, h1, h2, h3, h4] using hsel⟩

/-- Constraint 11: `encoder_selector_idx` lies in {0, ..., 17}. -/
theorem encoder_selector_valid (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    ∃ n : ℕ, n ≤ 17 ∧ encoder_selector_idx air row = (n : FBB) := by
  exact
    encoder_selector_of_ternary_digits
      (encoder_idx air 0 row) (encoder_idx air 1 row) (encoder_idx air 2 row)
      (encoder_idx air 3 row) (encoder_idx air 4 row)
      (encoder_digits_ternary air row hf 0 (by omega))
      (encoder_digits_ternary air row hf 1 (by omega))
      (encoder_digits_ternary air row hf 2 (by omega))
      (encoder_digits_ternary air row hf 3 (by omega))
      (encoder_digits_ternary air row hf 4 (by omega))
      (by simpa [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from] using
        encoder_digit_sum_ternary air row hf)

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
