/-
  Field algebra utility lemmas for KeccakfPermAir constraint reasoning.

  These lemmas extract binary / equality information from the polynomial
  constraint forms that the AIR row constraints produce.
-/
import Mathlib

set_option autoImplicit false

namespace KeccakfPermAir.Soundness

variable {F : Type} [Field F]

/-- If `x * (x - 1) = 0` in a field, then `x = 0 ∨ x = 1`. -/
lemma binary_of_mul_sub_one_eq_zero {x : F} (h : x * (x - 1) = 0) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with hx | hx
  · exact Or.inl hx
  · exact Or.inr (sub_eq_zero.mp hx)

/-- If `en * (a - b) = 0` and `en = 1`, then `a = b`. -/
lemma eq_of_enabled_mul_sub {en a b : F}
    (h : en * (a - b) = 0) (h_en : en = 1) : a = b := by
  rw [h_en, one_mul] at h
  exact sub_eq_zero.mp h

/-- If `en * x = 0` and `en = 1`, then `x = 0`. -/
lemma eq_zero_of_enabled_mul {en x : F}
    (h : en * x = 0) (h_en : en = 1) : x = 0 := by
  rw [h_en, one_mul] at h; exact h

/-- `a * b = 0` iff `a = 0` or `b = 0` in a field. -/
lemma mul_eq_zero_iff {a b : F} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  mul_eq_zero

/-- If `(a - b) * (a - b - 2) * (a - b - 4) = 0`, the difference is 0, 2, or 4. -/
lemma diff_parity_constraint {a b : F}
    (h : (a - b) * ((a - b) - 2) * ((a - b) - 4) = 0) :
    a - b = 0 ∨ a - b = 2 ∨ a - b = 4 := by
  rcases mul_eq_zero.mp h with hab | hab
  · rcases mul_eq_zero.mp hab with hab' | hab'
    · exact Or.inl hab'
    · exact Or.inr (Or.inl (sub_eq_zero.mp hab'))
  · exact Or.inr (Or.inr (sub_eq_zero.mp hab))

end KeccakfPermAir.Soundness
