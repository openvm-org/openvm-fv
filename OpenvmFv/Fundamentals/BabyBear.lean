import OpenvmFv.Fundamentals.Core

notation "BB" => 2013265921
@[simp] lemma BB_eq : BB = 2013265921 := rfl

namespace BabyBear

lemma prime_BabyBearPrime : Nat.Prime BB := by native_decide

instance Fact_BBPrime : Fact (Nat.Prime BB) := ⟨prime_BabyBearPrime⟩
instance : NeZero BB := by constructor; decide

instance : Field (Fin BB) := ZMod.instField BB
instance : NoZeroDivisors (Fin BB) := Fin.noZeroDivisors_of_prime _ (hp := Fact_BBPrime)

section inverses

lemma inv_256 : (2005401601 : Fin BB) = 256⁻¹ := by native_decide

@[simp] lemma inv_256_eq_one_lr : (2005401601 : Fin BB) * 256 = 1 := by rfl
@[simp] lemma inv_256_eq_one_rl : 256 * (2005401601 : Fin BB) = 1 := by rfl

@[simp] lemma inv_256_eq_256_lr : (2005401601 : Fin BB) * x = 1 ↔ x = 256 := by rw [inv_256, inv_mul_eq_one₀ (by simp), eq_comm]
@[simp] lemma inv_256_eq_256_rl : x * (2005401601 : Fin BB) = 1 ↔ x = 256 := by rw [mul_comm, inv_256_eq_256_lr]

end inverses

end BabyBear
