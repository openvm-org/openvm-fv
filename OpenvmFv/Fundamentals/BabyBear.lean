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

instance : NatCast FBB where


  natCast := (Lean.Grind.Fin.instCommRingFinOfNeZeroNat BB_prime).toCommSemiring.toSemiring.natCast.natCast

instance : Field FBB := ZMod.instField BB_prime
instance : NoZeroDivisors FBB := Fin.noZeroDivisors_of_prime _ (hp := Fact_BBPrime)

section inverses

lemma inv_4 : (1509949441 : FBB) = 4⁻¹ := by native_decide
lemma inv_255 : (465814468 : FBB) = 255⁻¹ := by native_decide
lemma inv_256 : (2005401601 : FBB) = 256⁻¹ := by native_decide
lemma inv_65536 : (2013235201 : FBB) = 65536⁻¹ := by native_decide
lemma inv_2_24 : (2013265801 : FBB) = 16777216⁻¹ := by native_decide

lemma inv_4_eq_one_lr : (1509949441 : FBB) * 4 = 1 := by rfl
lemma inv_4_eq_one_rl : 4 * (1509949441 : FBB) = 1 := by rfl
lemma inv_255_eq_one_lr : (465814468 : FBB) * 255 = 1 := by rfl
lemma inv_255_eq_one_rl : 255 * (465814468 : FBB) = 1 := by rfl
lemma inv_256_eq_one_lr : (2005401601 : FBB) * 256 = 1 := by rfl
lemma inv_256_eq_one_rl : 256 * (2005401601 : FBB) = 1 := by rfl
lemma inv_65536_eq_one_lr : (2013235201 : FBB) * 65536 = 1 := by rfl
lemma inv_65536_eq_one_rl : 65536 * (2013235201 : FBB) = 1 := by rfl
lemma inv_2_24_eq_one_lr : (2013265801 : FBB) * 16777216 = 1 := by rfl
lemma inv_2_24_eq_one_rl : 16777216 * (2013265801 : FBB) = 1 := by rfl

@[simp] lemma inv_4_eq_4_lr : (1509949441 : FBB) * x = 1 ↔ x = 4 := by rw [inv_4, inv_mul_eq_one₀ (by simp), eq_comm]
@[simp] lemma inv_4_eq_4_rl : x * (1509949441 : FBB) = 1 ↔ x = 4 := by rw [mul_comm, inv_4_eq_4_lr]
@[simp] lemma inv_255_eq_255_lr : (465814468 : FBB) * x = 1 ↔ x = 255 := by rw [inv_255, inv_mul_eq_one₀ (by simp), eq_comm]
@[simp] lemma inv_255_eq_255_rl : x * (465814468 : FBB) = 1 ↔ x = 255 := by rw [mul_comm, inv_255_eq_255_lr]
@[simp] lemma inv_256_eq_256_lr : (2005401601 : FBB) * x = 1 ↔ x = 256 := by rw [inv_256, inv_mul_eq_one₀ (by simp), eq_comm]
@[simp] lemma inv_256_eq_256_rl : x * (2005401601 : FBB) = 1 ↔ x = 256 := by rw [mul_comm, inv_256_eq_256_lr]
@[simp] lemma inv_65536_eq_65536_lr : (2013235201 : FBB) * x = 1 ↔ x = 65536 := by rw [inv_65536, inv_mul_eq_one₀ (by simp), eq_comm]
@[simp] lemma inv_65536_eq_65536_rl : x * (2013235201 : FBB) = 1 ↔ x = 65536 := by rw [mul_comm, inv_65536_eq_65536_lr]
@[simp] lemma inv_2_24_eq_2_24_lr : (2013265801 : FBB) * x = 1 ↔ x = 16777216 := by rw [inv_2_24, inv_mul_eq_one₀ (by simp), eq_comm]
@[simp] lemma inv_2_24_eq_2_24_rl : x * (2013265801 : FBB) = 1 ↔ x = 16777216 := by rw [mul_comm, inv_2_24_eq_2_24_lr]

lemma neg_inv_4 : (1509949441 : FBB) = -503316480 := by grind
lemma neg_inv_2_256 : (2005401601 : FBB) = -7864320 := by grind
lemma neg_inv_2_24 : (2013265801 : FBB) = -120 := by grind

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

section toInt

def toInt (a : FBB) : ℤ :=
  if a.val ≤ BB_prime / 2 then a.val else a.val - BB_prime

@[simp]
lemma toInt_inv
  (a : FBB)
:
  ((toInt a) : FBB) = a
:= by
  simp [toInt]

end toInt

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

lemma lt_neg
  {x y : FBB}
  (lb_x : 0 < x)
  (h_lt : x < y)
:
  -y < -x
:= by
  grind

lemma inv2_24_mono
  (x y : Fin 16777216)
  (lb_x : 0 < x)
  (h_lt : x < y)
:
  (2013265801 : FBB) * (⟨ y.val, by omega⟩ : FBB) < (2013265801 : FBB) * (⟨ x.val, by omega⟩ : FBB)
:= by
  rw [neg_inv_2_24, neg_mul, neg_mul]
  apply lt_neg
  . rw [Fin.lt_def, Fin.val_mul]; simp; omega
  . rw [Fin.lt_def, Fin.val_mul, Fin.val_mul]; simp; grind

lemma inv2_24_prod_lt_2_24
  (x : Fin 16777216)
:
  x = 0 ∨ (¬x = 0 ∧ 120 < (2013265801 : FBB) * (⟨ x.val, by omega⟩ : FBB) ∧ (2013265801 : FBB) * (⟨ x.val, by omega⟩ : FBB) ≤ 2013265801)
:= by
  by_cases lb_x : 0 < x
  . right; constructor
    . omega
    . by_cases ub_x : x < 16777215
      . split_ands
        . have := @inv2_24_mono x 16777215 lb_x ub_x
          simp_all; omega
        . by_cases eq_x : x = 1
          . simp_all
          . have := @inv2_24_mono 1 x (by simp) (by omega)
            simp_all; omega
      . have eq_x : x = 16777215 := by omega
        simp_all
  . omega

lemma inv2_24_prod_mod
  (x : FBB)
:
  x % 16777216 = 0 ∨ (¬ x % 16777216 = 0 ∧ 120 < (2013265801 : FBB) * (x % 16777216) ∧ (2013265801 : FBB) * (x % 16777216) ≤ 2013265801)
:= by
  have := inv2_24_prod_lt_2_24 ⟨ (x % 16777216).val, by grind⟩
  rcases this with hz | ⟨ h_nz, h_lt ⟩ <;> simp_all
  . grind
  . right; constructor
    . grind
    . simp_all [Fin.lt_def, Fin.mul_def]

lemma inv2_24_prod_lt_2_24_mod_zero
  {x : FBB}
  (h_le : (2013265801 : FBB) * x ≤ 120)
:
  x % 16777216 = 0
:= by
  by_cases hnz : x = 0 <;> [ simp_all; skip ]
  have h_div_mod : x = (x / 16777216) * 16777216 + x % 16777216
  := by
    simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]
    grind
  rw [h_div_mod] at h_le ⊢; clear h_div_mod
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]
  rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
  simp [Nat.add_mod]
  have := inv2_24_prod_mod x
  rcases this with hz | ⟨ hnz, hmod ⟩
  . simp [Fin.ext_iff] at hz; assumption
  . rw [mul_add, mul_comm (b := 16777216), ← mul_assoc, inv_2_24_eq_one_lr] at h_le
    simp at h_le
    have ub_x_div : x / 16777216 ≤ 120 := by simp [Fin.le_def]; omega
    suffices : 120 < x / 16777216 + 2013265801 * (x % 16777216)
    . omega
    . obtain ⟨ lb_mod, ub_mod ⟩ := hmod
      rw [Fin.lt_def] at lb_mod ⊢
      rw [Fin.le_def] at ub_mod h_le ub_x_div
      simp_all [Fin.val_add, Fin.val_mul]
      rw [Nat.add_mod] at h_le ⊢
      rw [Nat.mod_eq_of_lt (a := _ / _) (by omega)] at h_le ⊢
      by_cases hmmm : x.val / 16777216 = 120
      . have : x = 2013265920 := by omega
        simp_all
      . have ub_div : x.val / 16777216 < 120 := by omega
        clear ub_x_div hmmm
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

lemma inv2_24_prod_diff_div_mod
  {a b : FBB}
  (ub_a : a.val < 16777216)
  (h_le : ((2013265801 : FBB) * (b - a)).val < 120)
:
  a = b % 16777216 ∧ (2013265801 : FBB) * (b - a) = b / 16777216
:= by
  have h_mod_zero := @inv2_24_prod_lt_2_24_mod_zero (b - a) (by omega)
  have a_le_b : a ≤ b
  := by
    rw [neg_inv_2_24, neg_mul, mul_comm, ← neg_mul, neg_sub] at h_le
    grind
  clear h_le
  suffices h_mod : a = b % 16777216
  . simp_all
    have : b = (b / 16777216 * 16777216) + b % 16777216
      := by simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]; grind
    (conv => lhs; arg 2; arg 1; rw [this]); simp
    rw [mul_comm (b := 16777216), ← mul_assoc, inv_2_24_eq_one_lr]; simp
  . simp [Fin.ext_iff] at h_mod_zero
    rw [Fin.sub_val_of_le a_le_b] at h_mod_zero
    grind

lemma inv4_mono
  (x y : Fin 4)
  (lb_x : 0 < x)
  (h_lt : x < y)
:
  (2013265801 : FBB) * (⟨ y.val, by omega⟩ : FBB) < (2013265801 : FBB) * (⟨ x.val, by omega⟩ : FBB)
:= by
  rw [neg_inv_2_24, neg_mul, neg_mul]
  apply lt_neg
  . rw [Fin.lt_def, Fin.val_mul]; simp; omega
  . rw [Fin.lt_def, Fin.val_mul, Fin.val_mul]; simp; grind

lemma inv4_prod_lt_4
  (x : Fin 4)
:
  x = 0 ∨ (¬x = 0 ∧ 503316480 < (1509949441 : FBB) * (⟨ x.val, by omega⟩ : FBB) ∧ (1509949441 : FBB) * (⟨ x.val, by omega⟩ : FBB) ≤ 1509949441)
:= by
  fin_cases x <;> simp

lemma inv4_prod_mod
  (x : FBB)
:
  x % 4 = 0 ∨ (¬ x % 4 = 0 ∧ 503316480 < (1509949441 : FBB) * (x % 4) ∧ (1509949441 : FBB) * (x % 4) ≤ 1509949441)
:= by
  have := inv4_prod_lt_4 ⟨ (x % 4).val, by grind⟩
  rcases this with hz | ⟨ h_nz, h_lt ⟩ <;> simp_all
  . grind
  . right; constructor
    . grind
    . simp_all [Fin.lt_def, Fin.mul_def]

lemma inv4_prod_lt_4_mod_zero
  {x : FBB}
  (h_le : x * (1509949441 : FBB) ≤ 503316480)
:
  x % 4 = 0
:= by
  rw [mul_comm] at h_le
  by_cases hnz : x = 0 <;> [ simp_all; skip ]
  have h_div_mod : x = (x / 4) * 4 + x % 4
  := by
    simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]
    grind
  rw [h_div_mod] at h_le ⊢; clear h_div_mod
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]
  rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
  simp [Nat.add_mod]
  have := inv4_prod_mod x
  rcases this with hz | ⟨ hnz, hmod ⟩
  . simp [Fin.ext_iff] at hz; assumption
  . rw [mul_add, mul_comm (b := 4), ← mul_assoc, inv_4_eq_one_lr] at h_le
    simp at h_le
    have ub_x_div : x / 4 ≤ 1509949441 := by simp [Fin.le_def]; omega
    suffices : 503316480 < x / 4 + 1509949441 * (x % 4)
    . omega
    . obtain ⟨ lb_mod, ub_mod ⟩ := hmod
      rw [Fin.lt_def] at lb_mod ⊢
      rw [Fin.le_def] at ub_mod h_le ub_x_div
      simp_all [Fin.val_add, Fin.val_mul]
      rw [Nat.add_mod] at h_le ⊢
      rw [Nat.mod_eq_of_lt (a := _ / _) (by omega)] at h_le ⊢
      by_cases hmmm : x.val / 16777216 = 120
      . have : x = 2013265920 := by omega
        simp_all
      . have ub_div : x.val / 16777216 < 120 := by omega
        clear ub_x_div hmmm
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

lemma mod_4_zero_bits_zero
  (a : FBB)
:
  a % 4 = 0
    ↔
  (BitVec.ofNat 32 a.val)[0] = false ∧
  (BitVec.ofNat 32 a.val)[1] = false
:= by
  have : a % (4 : FBB) = (1 : FBB) * ((BitVec.ofNat 32 a.val)[0]).toNat + (2 : FBB) * (BitVec.ofNat 32 a.val)[1].toNat
  := by
    simp only [BitVec.getElem_eq_testBit_toNat]
    simp [Nat.testBit_eq_decide_div_mod_eq]
    rw [Nat.mod_eq_of_lt (b := 4294967296) (by omega)]
    simp [Fin.ext_iff]
    by_cases a.val % 2 = 1 <;>
    by_cases a.val / 2 % 2 = 1 <;>
    simp_all <;> omega
  rw [this]; clear this
  by_cases (BitVec.ofNat 32 ↑a)[0] <;>
  by_cases (BitVec.ofNat 32 ↑a)[1] <;> simp_all

/-- Inverse of zero -/
lemma toInt_0_inv {a b c d : FBB}
  (ub_a : a.val < 256)
  (ub_b : b.val < 256)
  (ub_c : c.val < 256)
  (ub_d : d.val < 256)
:
  U32.toInt #v[BitVec.ofNat 8 a, BitVec.ofNat 8 b, BitVec.ofNat 8 c, BitVec.ofNat 8 d] = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0
:= by
  simp [U32.toInt, U32.negative, U32.toNat]
  omega

lemma toInt_neg_1_inv {a b c d : FBB}
  (ub_a : a.val < 256)
  (ub_b : b.val < 256)
  (ub_c : c.val < 256)
  (ub_d : d.val < 256)
:
  U32.toInt #v[BitVec.ofNat 8 a, BitVec.ofNat 8 b, BitVec.ofNat 8 c, BitVec.ofNat 8 d] = -1 ↔ a = 255 ∧ b = 255 ∧ c = 255 ∧ d = 255
:= by
  simp [U32.toInt, U32.negative, U32.toNat]
  omega

lemma toInt_neg_2_pow_32_inv {a b c d : FBB}
  (ub_a : a.val < 256)
  (ub_b : b.val < 256)
  (ub_c : c.val < 256)
  (ub_d : d.val < 256)
:
  U32.toInt #v[BitVec.ofNat 8 a, BitVec.ofNat 8 b, BitVec.ofNat 8 c, BitVec.ofNat 8 d] = -2147483648 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 128
:= by
  simp [U32.toInt, U32.negative, U32.toNat]
  omega

end auxiliaries

namespace Circuits

  lemma signed_top_byte
    {x x_stb : FBB}
    (ub_x : x.val < 256)
    (ub_x_stb : (x_stb + 128).val < 256)
    (h_msb : x = x_stb ∨ x - x_stb = 256)
  :
    x_stb = if 128 ≤ x.val then x - 256 else x
  := by grind

  lemma less_than
    {x0 x1 x2 x3 y0 y1 y2 y3 dm0 dm1 dm2 dm3 diff stb_x stb_y is_signed result : FBB}
    (ub_x0 : x0.val < 256)
    (ub_x1 : x1.val < 256)
    (ub_x2 : x2.val < 256)
    (ub_x3 : x3.val < 256)
    (ub_y0 : y0.val < 256)
    (ub_y1 : y1.val < 256)
    (ub_y2 : y2.val < 256)
    (ub_y3 : y3.val < 256)
    (b_result : result = 0 ∨ result = 1)
    (h_stb_diff_x : x3 = stb_x ∨ x3 - stb_x = 256)
    (h_stb_diff_y : y3 = stb_y ∨ y3 - stb_y = 256)
    (b_dm0 : dm0 = 0 ∨ dm0 = 1)
    (b_dm1 : dm1 = 0 ∨ dm1 = 1)
    (b_dm2 : dm2 = 0 ∨ dm2 = 1)
    (b_dm3 : dm3 = 0 ∨ dm3 = 1)
    (b_sum : dm3 + dm2 + dm1 + dm0 = 0 ∨ dm3 + dm2 + dm1 + dm0 = 1)
    (dm3_diff : dm3 = 0 ∨ diff = (stb_y - stb_x) * (2 * result - 1))
    (dm2_diff : dm2 = 0 ∨ diff = (y2 - x2) * (2 * result - 1))
    (dm1_diff : dm1 = 0 ∨ diff = (y1 - x1) * (2 * result - 1))
    (dm0_diff : dm0 = 0 ∨ diff = (y0 - x0) * (2 * result - 1))
    (sum0_result1 : dm3 + dm2 + dm1 + dm0 = 1 ∨ result = 0)
    (sum3_diff : dm3 = 1 ∨ stb_y = stb_x)
    (sum2_diff : dm3 + dm2 = 1 ∨ y2 = x2)
    (sum1_diff : dm3 + dm2 + dm1 = 1 ∨ y1 = x1)
    (sum0_diff : dm3 + dm2 + dm1 + dm0 = 1 ∨ y0 = x0)
    (h_stb_x : (stb_x + 128 * is_signed).val < 256)
    (h_stb_y : (stb_y + 128 * is_signed).val < 256)
    (h_diff : dm3 + dm2 + dm1 + dm0 = 1 → (diff - 1).val < 256)
  :
    (is_signed = 0 → (if U32.toNat #v[x0, x1, x2, x3] < U32.toNat #v[y0, y1, y2, y3] then (1 : FBB) else 0) = result) ∧
    (is_signed = 1 → (if U32.toInt #v[x0, x1, x2, x3] < U32.toInt #v[y0, y1, y2, y3] then (1 : FBB) else 0) = result)
  := by

    have ⟨ hdm0, hdm1, hdm2, hdm3 ⟩ :
      (dm0 = 1 → dm1 = 0 ∧ dm2 = 0 ∧ dm3 = 0) ∧
      (dm1 = 1 → dm0 = 0 ∧ dm2 = 0 ∧ dm3 = 0) ∧
      (dm2 = 1 → dm0 = 0 ∧ dm1 = 0 ∧ dm3 = 0) ∧
      (dm3 = 1 → dm0 = 0 ∧ dm1 = 0 ∧ dm2 = 0)
    := by
      clear *- b_dm0 b_dm1 b_dm2 b_dm3 b_sum
      grind (splits := 14)

    split_ands <;> intro h_signed <;>
    rcases b_sum with h_sum | h_sum <;>
    simp_all
    . have : dm3 = 0 ∧ dm2 = 0 ∧ dm1 = 0 ∧ dm0 = 0 := by grind
      have : x3 = stb_x ∧ y3 = stb_y := by grind
      simp_all [U32.toNat]
    . have : x3 = stb_x ∧ y3 = stb_y := by clear *- ub_x3 ub_y3 h_stb_diff_x h_stb_diff_y h_stb_x h_stb_y; grind
      simp [U32.toNat]
      rcases b_dm3 with h_dm3 | h_dm3
      . rcases b_dm2 with h_dm2 | h_dm2
        . rcases b_dm1 with h_dm1 | h_dm1
          . rcases b_dm0 with h_dm0 | h_dm0
            . simp_all
            . simp_all; rcases b_result <;> split_ifs <;> simp_all <;> grind
          . simp_all; rcases b_result <;> split_ifs <;> simp_all <;> grind
        . simp_all; rcases b_result <;> split_ifs <;> simp_all <;> grind
      . simp_all; rcases b_result <;> split_ifs <;> simp_all <;> grind
    . have : dm3 = 0 ∧ dm2 = 0 ∧ dm1 = 0 ∧ dm0 = 0 := by grind
      suffices : x3 = y3 <;> simp_all; grind
    . have eq_msb_b := @signed_top_byte x3 stb_x ub_x3 h_stb_x h_stb_diff_x
      have eq_msb_c := @signed_top_byte y3 stb_y ub_y3 h_stb_y h_stb_diff_y

      simp [U32.toInt, U32.toNat, ← U32.msb_3_negative, BitVec.msb_eq_decide]
      repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
      repeat rw [Int.emod_eq_of_lt (b := 256) (by omega) (by omega)]

      rcases b_dm3 with h_dm3 | h_dm3
      . rcases b_dm2 with h_dm2 | h_dm2
        . rcases b_dm1 with h_dm1 | h_dm1
          . rcases b_dm0 with h_dm0 | h_dm0
            . simp_all
            . simp_all; rcases b_result <;> split_ifs <;> simp_all <;> omega
          . simp_all; rcases b_result <;> split_ifs <;> simp_all <;> omega
        . simp_all; rcases b_result <;> split_ifs <;> simp_all <;> omega
      . simp_all; rcases b_result <;> split_ifs <;> simp_all <;> omega

lemma mul
{ a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 c0 c1 c2 c3 b_ext c_ext : FBB }
(ub_a0 : a0.val < 256)
(ub_a1 : a1.val < 256)
(ub_a2 : a2.val < 256)
(ub_a3 : a3.val < 256)
(ub_a4 : a4.val < 256)
(ub_a5 : a5.val < 256)
(ub_a6 : a6.val < 256)
(ub_a7 : a7.val < 256)
(ub_b0 : b0.val < 256)
(ub_b1 : b1.val < 256)
(ub_b2 : b2.val < 256)
(ub_b3 : b3.val < 256)
(ub_c0 : c0.val < 256)
(ub_c1 : c1.val < 256)
(ub_c2 : c2.val < 256)
(ub_c3 : c3.val < 256)
(h_msb_b : b_ext = if 128 ≤ b3.val then 255 else 0)
(h_msb_c : c_ext = if 128 ≤ c3.val then 255 else 0)
(ub_cry0 : (2005401601 * (b0 * c0 - a0)).val < 2048)
(ub_cry1 : (2005401601 * (2005401601 * (b0 * c0 - a0) + (b0 * c1 + b1 * c0) - a1)).val < 2048)
(ub_cry2 : (2005401601 * (2005401601 * (2005401601 * (b0 * c0 - a0) + (b0 * c1 + b1 * c0) - a1) + (b0 * c2 + b1 * c1 + b2 * c0) - a2)).val < 2048)
(ub_cry3 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (b0 * c0 - a0) + (b0 * c1 + b1 * c0) - a1) + (b0 * c2 + b1 * c1 + b2 * c0) - a2) + (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0) - a3)).val < 2048)
(ub_cry4 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (b0 * c0 - a0) + (b0 * c1 + b1 * c0) - a1) + (b0 * c2 + b1 * c1 + b2 * c0) - a2) + (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0) - a3) + (b1 * c3 + b2 * c2 + b3 * c1) + (b0 * c_ext + c0 * b_ext) - a4)).val < 2048)
(ub_cry5 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (b0 * c0 - a0) + (b0 * c1 + b1 * c0) - a1) + (b0 * c2 + b1 * c1 + b2 * c0) - a2) + (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0) - a3) + (b1 * c3 + b2 * c2 + b3 * c1) + (b0 * c_ext + c0 * b_ext) - a4) + (b2 * c3 + b3 * c2) + (b0 * c_ext + c0 * b_ext + b1 * c_ext + c1 * b_ext) - a5)).val < 2048)
(ub_cry6 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (b0 * c0 - a0) + (b0 * c1 + b1 * c0) - a1) + (b0 * c2 + b1 * c1 + b2 * c0) - a2) + (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0) - a3) + (b1 * c3 + b2 * c2 + b3 * c1) + (b0 * c_ext + c0 * b_ext) - a4) + (b2 * c3 + b3 * c2) + (b0 * c_ext + c0 * b_ext + b1 * c_ext + c1 * b_ext) - a5) + b3 * c3 + (b0 * c_ext + c0 * b_ext + b1 * c_ext + c1 * b_ext + b2 * c_ext + c2 * b_ext) - a6)).val < 2048)
(ub_cry7 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (b0 * c0 - a0) + (b0 * c1 + b1 * c0) - a1) + (b0 * c2 + b1 * c1 + b2 * c0) - a2) + (b0 * c3 + b1 * c2 + b2 * c1 + b3 * c0) - a3) + (b1 * c3 + b2 * c2 + b3 * c1) + (b0 * c_ext + c0 * b_ext) - a4) + (b2 * c3 + b3 * c2) + (b0 * c_ext + c0 * b_ext + b1 * c_ext + c1 * b_ext) - a5) + b3 * c3 + (b0 * c_ext + c0 * b_ext + b1 * c_ext + c1 * b_ext + b2 * c_ext + c2 * b_ext) - a6) + (b0 * c_ext + c0 * b_ext + b1 * c_ext + c1 * b_ext + b2 * c_ext + c2 * b_ext + b3 * c_ext + c3 * b_ext) - a7)).val < 2048)
:
  U64.toBV #v[BitVec.ofNat 8 a0, BitVec.ofNat 8 a1, BitVec.ofNat 8 a2, BitVec.ofNat 8 a3, BitVec.ofNat 8 a4, BitVec.ofNat 8 a5, BitVec.ofNat 8 a6, BitVec.ofNat 8 a7] =
  U64.toBV #v[BitVec.ofNat 8 b0, BitVec.ofNat 8 b1, BitVec.ofNat 8 b2, BitVec.ofNat 8 b3,
              BitVec.ofNat 8 b_ext, BitVec.ofNat 8 b_ext, BitVec.ofNat 8 b_ext, BitVec.ofNat 8 b_ext] *
  U64.toBV #v[BitVec.ofNat 8 c0, BitVec.ofNat 8 c1, BitVec.ofNat 8 c2, BitVec.ofNat 8 c3,
              BitVec.ofNat 8 c_ext, BitVec.ofNat 8 c_ext, BitVec.ofNat 8 c_ext, BitVec.ofNat 8 c_ext]
:= by
  have ub_b_ext : b_ext.val ≤ 255
    := by rw [h_msb_b]; clear *-; split_ifs <;> simp
  have ub_c_ext : c_ext.val ≤ 255
    := by rw [h_msb_c]; clear *-; split_ifs <;> simp

  replace ub_cry0 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry0; simp]
  replace ub_cry1 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry1; simp]
  replace ub_cry2 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry2; simp]
  replace ub_cry3 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry3; simp]
  replace ub_cry4 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry4; simp]
  replace ub_cry5 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry5; simp]
  replace ub_cry6 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry6; simp]
  replace ub_cry7 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry7; simp]

  have ub_p00 : b0.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a0, eq_cry0 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a0 ub_cry0
  simp [Fin.ext_iff, Fin.val_mul] at eq_a0
  rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a0
  rw [eq_cry0] at ub_cry1 ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry0 eq_cry0

  have ub_p01 : b0.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p10 : b1.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a1, eq_cry1 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a1 ub_cry1
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a1
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a1
  rw [eq_cry1] at ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry1 eq_cry1

  have ub_p02 : b0.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p11 : b1.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p20 : b2.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a2, eq_cry2 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a2 ub_cry2
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a2
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a2
  rw [eq_cry2] at ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry2 eq_cry2

  have ub_p03 : b0.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p12 : b1.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p21 : b2.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p30 : b3.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a3, eq_cry3 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a3 ub_cry3
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a3
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a3
  rw [eq_cry3] at ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry3 eq_cry3

  have ub_p13 : b1.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p22 : b2.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p31 : b3.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_be0 : b0.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_qe0 : c0.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a4, eq_cry4 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a4 ub_cry4
  rw [  add_assoc (b := (b1 * c3 + b2 * c2 + b3 * c1)),
      ← add_assoc (a := (b1 * c3 + b2 * c2 + b3 * c1))] at *
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a4
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a4
  rw [eq_cry4] at ub_cry5 ub_cry6 ub_cry7
  clear ub_cry4 eq_cry4

  have ub_p23 : b2.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p32 : b3.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_be1 : b1.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_qe1 : c1.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a5, eq_cry5 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a5 ub_cry5
  rw [add_assoc (b := (b2 * c3 + b3 * c2))] at *
  iterate 3 rw [← add_assoc (a := (b2 * c3 + b3 * c2))] at *
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a5
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a5
  rw [eq_cry5] at ub_cry6 ub_cry7
  clear ub_cry5 eq_cry5

  have ub_p33 : b3.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_be2 : b2.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_qe2 : c2.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a6, eq_cry6 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a6 ub_cry6
  rw [add_assoc (b := (b3 * c3))] at *
  iterate 5 rw [← add_assoc (a := (b3 * c3))] at *
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a6
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a6
  rw [eq_cry6] at ub_cry7
  clear ub_cry6 eq_cry6

  have ub_be3 : b3.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_qe3 : c3.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a7, eq_cry7 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a7 ub_cry7
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a7
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a7
  clear ub_cry7 eq_cry7

  rw [eq_a0, eq_a1, eq_a2, eq_a3, eq_a4, eq_a5, eq_a6, eq_a7]

  simp [← BitVec.toNat_inj, U64.toNat]
  rw [Nat.DivMod.div_8 (a := _ * _), Nat.DivMod.div_16, Nat.DivMod.div_24,
      Nat.DivMod.div_32, Nat.DivMod.div_40, Nat.DivMod.div_48]
  rw [Nat.DivMod.join_8, Nat.DivMod.join_16, Nat.DivMod.join_24,
      Nat.DivMod.join_32, Nat.DivMod.join_40, Nat.DivMod.join_48, Nat.DivMod.join_56]
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
  ring_nf
  omega

end Circuits

end BabyBear
