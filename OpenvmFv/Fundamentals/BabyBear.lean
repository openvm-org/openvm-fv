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

end auxiliaries

end BabyBear
