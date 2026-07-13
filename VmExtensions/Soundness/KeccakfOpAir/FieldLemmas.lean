import Mathlib
import OpenvmFv.Fundamentals.BabyBear

set_option autoImplicit false

open BabyBear

namespace KeccakfOpAir.Soundness

/-!
# Field Lemmas for KeccakfOpAir

Generic field algebra utilities (not FBB-specific).
-/

-- If x * (x - 1) = 0 then x = 0 ∨ x = 1
lemma binary_of_mul_sub_one_eq_zero {F : Type} [Field F] {x : F}
    (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · left; exact h
  · right; exact sub_eq_zero.mp h

-- If en * (a - b) = 0 and en = 1 then a = b
lemma eq_of_enabled_mul_sub {F : Type} [Field F] {en a b : F}
    (h : en * (a - b) = 0) (hen : en = 1) : a = b := by
  subst hen; simp at h; exact sub_eq_zero.mp h

-- If en * x = 0 and en = 1 then x = 0
lemma eq_zero_of_enabled_mul {F : Type} [Field F] {en x : F}
    (h : en * x = 0) (hen : en = 1) : x = 0 := by
  subst hen; simpa using h

-- If en * (a - 1 - (b + c * k)) = 0 and en = 1 then a = 1 + b + c * k
lemma lt_decomp_of_enabled {F : Type} [Field F] {en a b c : F} {k : F}
    (h : en * ((a - 1) - (b + c * k)) = 0) (hen : en = 1) : a = 1 + b + c * k := by
  have h0 := eq_zero_of_enabled_mul h hen
  have : a - 1 = b + c * k := sub_eq_zero.mp h0
  linear_combination this

/-!
# FBB (Baby Bear) arithmetic helpers

FBB = Fin 2013265921. These lemmas help prove timestamp ordering
by showing Fin arithmetic doesn't wrap around for bounded values.
-/

-- FBB value of addition (no wrap-around)
lemma fbb_val_add {a b : FBB} (h : a.val + b.val < 2013265921) :
    (a + b).val = a.val + b.val := by
  simp [Fin.val_add, Nat.mod_eq_of_lt h]

-- FBB value of multiplication (no wrap-around)
lemma fbb_val_mul {a b : FBB} (h : a.val * b.val < 2013265921) :
    (a * b).val = a.val * b.val := by
  simp [Fin.val_mul, Nat.mod_eq_of_lt h]

-- FBB value of nat cast (no wrap-around)
lemma fbb_val_natCast {n : ℕ} (h : n < 2013265921) :
    (n : FBB).val = n := by
  simp [Nat.mod_eq_of_lt h]

-- Core timestamp ordering lemma:
-- If a - b - 1 = d in FBB and b.val + d.val + 1 < p, then b.val < a.val.
-- Proof: a = d + b + 1 (field), .val = d.val + b.val + 1 (no wrap), > b.val.
lemma fbb_lt_of_sub_decomp {a b d : FBB}
    (h_eq : a - b - 1 = d)
    (h_sum : b.val + d.val + 1 < 2013265921)
    : b.val < a.val := by
  have h1 : a = d + b + 1 := by linear_combination h_eq
  have h2 : (d + b).val = d.val + b.val :=
    fbb_val_add (by omega)
  have h3 : (1 : FBB).val = 1 := by decide
  have h4 : (d + b + 1 : FBB).val = d.val + b.val + 1 := by
    rw [show d + b + 1 = (d + b) + 1 from by ring]
    rw [fbb_val_add (by rw [h2, h3]; omega)]
    rw [h2, h3]
  rw [h1, h4]; omega

-- Literal FBB value
private lemma fbb_val_131072 : (131072 : FBB).val = 131072 := by decide

-- Decomposition value bound: lo + hi * 131072 has .val < 2^30 when range-checked
lemma decomp_val_bound {lo hi : FBB}
    (h_lo : lo.val < 2^17) (h_hi : hi.val < 2^12) :
    (lo + hi * 131072).val < 2^30 := by
  have h_hi_mul : (hi * 131072 : FBB).val = hi.val * 131072 := by
    rw [Fin.val_mul, fbb_val_131072, Nat.mod_eq_of_lt (by omega)]
  have h_add : (lo + hi * 131072 : FBB).val = lo.val + hi.val * 131072 := by
    rw [show lo + hi * 131072 = lo + (hi * 131072) from rfl]
    rw [@fbb_val_add lo (hi * 131072) (by rw [h_hi_mul]; omega), h_hi_mul]
  rw [h_add]; omega

-- Combined: sum of prev_ts + decomp + 1 < p
lemma decomp_sum_lt_p {b lo hi : FBB}
    (h_b : b.val < 2^29)
    (h_lo : ∃ n : ℕ, lo = ↑n ∧ n < 2^17)
    (h_hi : ∃ n : ℕ, hi = ↑n ∧ n < 2^12)
    : b.val + (lo + hi * 131072).val + 1 < 2013265921 := by
  obtain ⟨n_lo, rfl, hn_lo⟩ := h_lo
  obtain ⟨n_hi, rfl, hn_hi⟩ := h_hi
  have hlo : (↑n_lo : FBB).val < 2^17 := by rw [fbb_val_natCast (by omega)]; exact hn_lo
  have hhi : (↑n_hi : FBB).val < 2^12 := by rw [fbb_val_natCast (by omega)]; exact hn_hi
  have := decomp_val_bound hlo hhi
  omega

-- FBB inequality helpers (used for vacuous bus assert conditions)
lemma fbb_zero_ne_one : ¬ (0 : FBB) = 1 := by decide
lemma fbb_zero_ne_neg_one : ¬ (0 : FBB) = -1 := by decide
lemma fbb_neg_one_ne_one : ¬ (-1 : FBB) = 1 := by decide
lemma fbb_one_ne_neg_one : ¬ (1 : FBB) = -1 := by decide

-- Convert from ∃ n, x = ↑n ∧ n < k to x.val < k
lemma fbb_val_lt_of_exists {x : FBB} {k : ℕ} (h : ∃ n : ℕ, x = ↑n ∧ n < k)
    (hk : k ≤ 2013265921) : x.val < k := by
  obtain ⟨n, rfl, hn⟩ := h
  rw [fbb_val_natCast (by omega)]
  exact hn

-- FBB constant values
private lemma fbb_val_one_eq : (1 : FBB).val = 1 := by decide
private lemma fbb_val_two_eq : (2 : FBB).val = 2 := by decide

-- u16 limb bound: if a, b are bytes then a + b * 256 < 2^16
lemma u16_limb_bound {a b : FBB} (ha : a.val < 256) (hb : b.val < 256) :
    (a + b * 256).val < 2^16 := by
  have h256 : (256 : FBB).val = 256 := by decide
  have hmul : (b * 256).val = b.val * 256 := by
    rw [Fin.val_mul, h256, Nat.mod_eq_of_lt (by omega)]
  have hadd : (a + b * 256).val = a.val + b.val * 256 := by
    rw [Fin.val_add, hmul, Nat.mod_eq_of_lt (by omega)]
  rw [hadd]; omega

end KeccakfOpAir.Soundness
