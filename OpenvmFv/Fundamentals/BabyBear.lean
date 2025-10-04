import OpenvmFv.Fundamentals.Core
import OpenvmFv.Fundamentals.U32

set_option maxHeartbeats 1_000_000_000

notation "BB_prime" => 2013265921
@[simp] lemma BB_eq : BB_prime = 2013265921 := rfl

namespace BabyBear

-- notation "F" => Fin BB_prime
notation "FBB" => Fin BB_prime
@[simp] lemma F_eq : FBB = Fin BB_prime := rfl

lemma prime_BabyBearPrime : Nat.Prime BB_prime := by native_decide

instance Fact_BBPrime : Fact (Nat.Prime BB_prime) := ⟨prime_BabyBearPrime⟩
instance : NeZero BB_prime := by constructor; decide

instance : Field FBB := ZMod.instField BB_prime
instance : NoZeroDivisors FBB := Fin.noZeroDivisors_of_prime _ (hp := Fact_BBPrime)

section inverses

lemma inv_255 : (465814468 : FBB) = 255⁻¹ := by native_decide
lemma inv_256 : (2005401601 : FBB) = 256⁻¹ := by native_decide

lemma inv_255_eq_one_lr : (465814468 : FBB) * 255 = 1 := by rfl
lemma inv_255_eq_one_rl : 255 * (465814468 : FBB) = 1 := by rfl
lemma inv_256_eq_one_lr : (2005401601 : FBB) * 256 = 1 := by rfl
lemma inv_256_eq_one_rl : 256 * (2005401601 : FBB) = 1 := by rfl

@[simp] lemma inv_255_eq_255_lr : (465814468 : FBB) * x = 1 ↔ x = 255 := by rw [inv_255, inv_mul_eq_one₀ (by simp), eq_comm]
@[simp] lemma inv_255_eq_255_rl : x * (465814468 : FBB) = 1 ↔ x = 255 := by rw [mul_comm, inv_255_eq_255_lr]
@[simp] lemma inv_256_eq_256_lr : (2005401601 : FBB) * x = 1 ↔ x = 256 := by rw [inv_256, inv_mul_eq_one₀ (by simp), eq_comm]
@[simp] lemma inv_256_eq_256_rl : x * (2005401601 : FBB) = 1 ↔ x = 256 := by rw [mul_comm, inv_256_eq_256_lr]

end inverses

section coercions

instance : Coe (BitVec 8) FBB where
  coe b := ⟨ b.toNat, by omega ⟩

instance : Coe FBB (BitVec 8) where
  coe bb := { toFin := ⟨ bb.val % 256, by omega ⟩ }

end coercions

section U32

@[simp, grind]
def isU32 (v : Vector FBB 4) :=
  v[0].val < 256 ∧ v[1].val < 256 ∧ v[2].val < 256 ∧ v[3].val < 256

@[simp, grind]
def toU32 (v : Vector FBB 4) : U32 :=
  #v[ { toFin := ⟨ v[0].val % 256, (by grind)⟩ },
      { toFin := ⟨ v[1].val % 256, (by grind)⟩ },
      { toFin := ⟨ v[2].val % 256, (by grind)⟩ },
      { toFin := ⟨ v[3].val % 256, (by grind)⟩ } ]

@[simp, grind]
def toBV32 (v : Vector FBB 4) : BitVec 32 :=
  (toU32 v).toBV

end U32

section conversions

def toInt (a : FBB) : ℤ :=
  if a.val ≤ BB_prime / 2 then a.val else a.val - BB_prime

def ofBVInt (a : FBB) {w : ℕ} (b : BitVec w) : Prop :=
  a = b.toInt

lemma toInt_eq_ofBVInt
  (a : FBB)
  (b : BitVec w)
  (lb_w : 0 < w)
  (ub_w : w < 30)
  (ofBV : ofBVInt a b)
:
  toInt a = b.toInt
:= by
  have ub_b : (b.toNat : ℤ) < 2 ^ w := by
    have : b.toNat < 2 ^ w := by omega
    zify at this; exact this
  have ub_w_pow : 2 ^ w ≤ 2 ^ 29 := by
    apply Nat.pow_le_pow_right (by simp) (by omega)
  rw [ofBVInt, Fin.intCast_def] at ofBV
  rw [toInt, BitVec.toInt] at *
  subst a; simp_all
  split_ifs with b_neg₁ bb_neg b_neg₂ b_neg₂ bb_neg b_neg₂ b_neg₂ <;> simp_all
  . have ub_bnat : b.toNat < 2 ^ 29
    := by
      apply lt_of_lt_of_le (b := 2 ^ (w - 1))
      . rw [← mul_lt_mul_left (a := 2) (by simp), mul_comm (b := _ ^ _), ← pow_succ]
        have : w - 1 + 1 = w := by omega
        simp_all
      . trans 2 ^ 29
        . apply Nat.pow_le_pow_right (by simp) (by omega)
        . decide
    rw [Int.emod_eq_of_lt (by simp) (by omega)]
  . have ub_bnat : b.toNat < 2 ^ 29
    := by
      apply lt_of_lt_of_le (b := 2 ^ (w - 1))
      . rw [← mul_lt_mul_left (a := 2) (by simp), mul_comm (b := _ ^ _), ← pow_succ]
        have : w - 1 + 1 = w := by omega
        simp_all
      . trans 2 ^ 29
        . apply Nat.pow_le_pow_right (by simp) (by omega)
        . decide
    omega
  . omega
  . omega
  . rw [abs_of_nonpos (by omega)] at *
    simp_all
    replace b_neg₁ : 2 ^ (w - 1) ≤ b.toNat
    := by
      rw [← mul_le_mul_left (a := 2) (by simp), mul_comm (b := _ ^ _), ← pow_succ]
      have : w - 1 + 1 = w := by omega
      simp_all
    have lb : (2 ^ w : FBB) ≤ 2 ^ 29
    := by
      simp [Fin.le_def]
      grind
    have lb_diff : - 2 ^ w ≤ (b.toNat : FBB) - 2 ^ w
    := by
      simp [Fin.le_def, Fin.neg_def, Fin.sub_def]
      simp [Fin.sub_def] at b_neg₂
      simp [Fin.le_def] at lb
      grind
    grind
  . rw [abs_of_nonpos (by omega)] at *
    simp_all
    replace b_neg₁ : 2 ^ (w - 1) ≤ b.toNat
    := by
      rw [← mul_le_mul_left (a := 2) (by simp), mul_comm (b := _ ^ _), ← pow_succ]
      have : w - 1 + 1 = w := by omega
      simp_all
    simp [Fin.sub_def] at *
    zify at b_neg₂; rw [Int.natCast_sub (by omega)] at b_neg₂
    simp_all
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at *
    ring_nf
    suffices : (2 : ℤ) ^ w = (((2 : FBB) ^ w) : FBB)
    . rw [this]; omega
    . clear *- ub_w
      interval_cases w <;> simp

lemma ofBVInt_ex
  {a : FBB} {w : ℕ}
  (ub_w : w < 30)
  (lb_a : -2^w ≤ toInt a)
  (ub_a : toInt a < 2^w)
:
  ∃ (b : BitVec (w + 1)), ofBVInt a b
:= by
  exists BitVec.ofInt (w + 1) (toInt a)
  simp [ofBVInt, toInt] at *
  split_ifs with sgn_a
  . simp_all
    have : a.val < 2 ^ (w + 1) := by zify; grind
    rw [Int.bmod_def]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    have : ((Nat.cast (R := ℤ) (2 ^ (w + 1))) + 1) / 2 = 2 ^ w := by grind
    simp_all
  . simp_all only [↓reduceIte, not_le]
    rw [Int.bmod_def]
    have : ((Nat.cast (R := ℤ) (2 ^ (w + 1))) + 1) / 2 = 2 ^ w := by grind
    simp only [this]; clear this
    split_ifs with sgn_a'
    . simp_all [-neg_le_sub_iff_le_add]
      set a' := (a : ℤ) - 2013265921
      replace ub_a : a' < 0 := by omega
      have : a' % 2 ^ (w + 1) = 2 ^ (w + 1) + a' := by
        rw [Int.emod_def]
        suffices : (a' / 2 ^ (w + 1)) = -1
        . rw [this]; omega
        . suffices : - 2 ^ (w + 1) ≤ a'
          . clear *- ub_a this
            have lb_c : 0 < (2 : ℤ) ^ (w + 1) := by grind
            rw [Int.ediv_eq_iff_of_pos (by omega)]
            omega
          . omega
      omega
    . simp_all [-neg_le_sub_iff_le_add, -Lean.Grind.Fin.pow_succ]
      set a' := (a : ℤ) - 2013265921
      replace ub_a : a' < 0 := by omega
      have : a' % 2 ^ (w + 1) = 2 ^ (w + 1) + a' := by
        rw [Int.emod_def]
        suffices : (a' / 2 ^ (w + 1)) = -1
        . rw [this]; omega
        . suffices : - 2 ^ (w + 1) ≤ a'
          . clear *- ub_a this
            have lb_c : 0 < (2 : ℤ) ^ (w + 1) := by grind
            rw [Int.ediv_eq_iff_of_pos (by omega)]
            omega
          . omega
      simp [this]
      subst a'
      simp

end conversions

section auxiliaries

lemma lt_via_diff_and_range_check
  (a b c d : FBB)
  (h_c : c.val < 2^17)
  (h_d : d.val < 2^12)
  (h_diff : (a - b - 1).val < c + d * 131072)
: b.val < BB_prime - 2^29 + 1 → b.val < a.val := by
  grind

@[simp low] lemma to_the_right_FBB_0 : (0 : FBB) = a ↔ a = 0 := by omega
@[simp low] lemma to_the_right_FBB_1 : (1 : FBB) = a ↔ a = 1 := by omega
@[simp low] lemma to_the_right_FBB_255 : (255 : FBB) = a ↔ a = 255 := by omega

@[simp low] lemma one_plus_eq_zero : (1 : FBB) + a = 0 ↔ a = 2013265920 := by omega
@[simp low] lemma neg_one_plus_eq_zero : (2013265920 : FBB) + a = 0 ↔ a = 1 := by omega

lemma xor_as_and
  {a b c : FBB}
  (ub_b : b.val < 256)
  (ub_c : c.val < 256)
  (h_eq : (b + c - 2 * a).val = b.val ^^^ c.val)
:
  a.val < 256 ∧ a.val = b.val &&& c.val
:= by
  have := @Nat.and_le_left b c
  have := @Nat.and_le_right b c
  rw [BitVec.xor_as_and ub_b ub_c] at h_eq
  simp [Fin.add_def, Fin.sub_def, Fin.mul_def] at *
  grind

lemma xor_as_or
  {a b c : FBB}
  (ub_b : b.val < 256)
  (ub_c : c.val < 256)
  (h_eq : (2 * a - b - c).val = b.val ^^^ c.val)
:
  a.val < 256 ∧ a.val = b.val ||| c.val
:= by
  have := @Nat.or_lt_two_pow b c 8 ub_b ub_c
  have := @Nat.left_le_or b c
  have := @Nat.right_le_or b c
  rw [BitVec.xor_as_or ub_b ub_c] at h_eq
  grind

lemma inv256_prod_lt_256
  (x : Fin 256)
:
  x = 0 ∨ (¬x = 0 ∧ 7864320 < (2005401601 : FBB) * (⟨ x.val, by omega⟩ : FBB) ∧ (2005401601 : FBB) * (⟨ x.val, by omega⟩ : FBB) ≤ 2005401601)
:= by
  simp [Fin.lt_def, Fin.val_mul]
  fin_cases x <;> simp

lemma inv256_prod_mod
  (x : FBB)
:
  x % 256 = 0 ∨ (¬ x % 256 = 0 ∧ 7864320 < (2005401601 : FBB) * (x % 256) ∧ (2005401601 : FBB) * (x % 256) ≤ 2005401601)
:= by
  have := inv256_prod_lt_256 ⟨ (x % 256).val, by grind⟩
  rcases this with hz | ⟨ h_nz, h_lt ⟩ <;> simp_all
  . grind
  . right; constructor
    . grind
    . simp_all [Fin.lt_def, Fin.mul_def]

lemma inv256_prod_lt_256_mod_zero
  {x : FBB}
  (h_le : (2005401601 : FBB) * x ≤ 7864320)
:
  x % 256 = 0
:= by
  by_cases hnz : x = 0 <;> [ simp_all; skip ]
  have h_div_mod : x = (x / 256) * 256 + x % 256
  := by
    simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]
    grind
  rw [h_div_mod] at h_le ⊢; clear h_div_mod
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]
  rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
  simp [Nat.add_mod]
  have := inv256_prod_mod x
  rcases this with hz | ⟨ hnz, hmod ⟩
  . simp [Fin.ext_iff] at hz; assumption
  . rw [mul_add, mul_comm (b := 256), ← mul_assoc, inv_256_eq_one_lr] at h_le
    simp at h_le
    have ub_x_div : x / 256 ≤ 7864320 := by simp [Fin.le_def]; omega
    suffices : 7864320 < x / 256 + 2005401601 * (x % 256)
    . omega
    . obtain ⟨ lb_mod, ub_mod ⟩ := hmod
      rw [Fin.lt_def] at lb_mod ⊢
      rw [Fin.le_def] at ub_mod h_le ub_x_div
      simp_all [Fin.val_add, Fin.val_mul]
      rw [Nat.add_mod] at h_le ⊢
      rw [Nat.mod_eq_of_lt (a := _ / _) (by omega)] at h_le ⊢
      by_cases hmmm : x.val / 256 = 7864320
      . have : x = 2013265920 := by omega
        simp_all
      . have ub_div : x.val / 256 < 7864320 := by omega
        clear ub_x_div hmmm
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

lemma inv256_prod_diff_div_mod
  {a b : FBB}
  (ub_a : a.val < 256)
  (h_le : ((2005401601 : FBB) * (b - a)).val < 7864320)
:
  a = b % 256 ∧ (2005401601 : FBB) * (b - a) = b / 256
:= by
  have h_mod_zero := @inv256_prod_lt_256_mod_zero (b - a) (by omega)
  have a_le_b : a ≤ b := by grind
  clear h_le
  suffices h_mod : a = b % 256 <;> [ skip; grind ]
  . simp_all
    have : b = (b / 256 * 256) + b % 256
      := by simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]; grind
    (conv => lhs; arg 2; arg 1; rw [this]); simp
    rw [mul_comm (b := 256), ← mul_assoc, inv_256_eq_one_lr]; simp

end auxiliaries

end BabyBear
