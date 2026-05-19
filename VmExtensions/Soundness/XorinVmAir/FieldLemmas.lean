/-
  Field algebra utility lemmas for XorinVmAir constraint reasoning.

  These lemmas extract binary / equality information from the polynomial
  constraint forms that the AIR row constraints produce.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Basic

set_option autoImplicit false

namespace XorinVmAir.Soundness

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

end XorinVmAir.Soundness
