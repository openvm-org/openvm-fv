import OpenvmFv.Fundamentals.Core

notation "BB_prime" => 2013265921
@[simp] lemma BB_eq : BB_prime = 2013265921 := rfl

namespace BabyBear

-- notation "F" => Fin BB_prime
abbrev F := Fin BB_prime

lemma prime_BabyBearPrime : Nat.Prime BB_prime := by native_decide

instance Fact_BBPrime : Fact (Nat.Prime BB_prime) := ⟨prime_BabyBearPrime⟩
instance : NeZero BB_prime := by constructor; decide

instance : Field F := ZMod.instField BB_prime
instance : NoZeroDivisors F := Fin.noZeroDivisors_of_prime _ (hp := Fact_BBPrime)

section inverses

lemma inv_256 : (2005401601 : F) = 256⁻¹ := by native_decide

@[simp] lemma inv_256_eq_one_lr : (2005401601 : F) * 256 = 1 := by rfl
@[simp] lemma inv_256_eq_one_rl : 256 * (2005401601 : F) = 1 := by rfl

@[simp] lemma inv_256_eq_256_lr : (2005401601 : F) * x = 1 ↔ x = 256 := by rw [inv_256, inv_mul_eq_one₀ (by simp), eq_comm]
@[simp] lemma inv_256_eq_256_rl : x * (2005401601 : F) = 1 ↔ x = 256 := by rw [mul_comm, inv_256_eq_256_lr]

end inverses

end BabyBear
