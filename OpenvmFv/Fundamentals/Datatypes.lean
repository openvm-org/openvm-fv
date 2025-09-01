import Mathlib

namespace BitVec

/-- Reformulation of `sshiftRight` -/
lemma sshiftright_eq {n : ℕ} {bv : BitVec n} {shift : ℕ} :
  bv.sshiftRight shift =
    BitVec.setWidth n
      (BitVec.extractLsb ((n - 1) + shift) shift (BitVec.signExtend (n + shift) bv))
    := by grind

/-- `BitVec` extension, signed and unsigned -/
def extend {m : ℕ} (bv : BitVec m) (n : ℕ) (sgn : Prop) [Decidable sgn] :=
  (if sgn then signExtend else setWidth) n bv

end BitVec

namespace Int

lemma abs_cases {a : ℤ} : abs a = if 0 ≤ a then a else -a := by
  unfold abs; rw [Int.max_def]; omega

lemma sign_cases (a : ℤ) : a.sign = if a < 0 then -1 else if a = 0 then 0 else 1 := by
  by_cases a = 0
  . simp_all
  . by_cases 0 < a
    . rw [Int.sign_eq_one_of_pos (by omega)]; omega
    . rw [Int.sign_eq_neg_one_of_neg (by omega)]; omega

lemma split_nzp (a : ℤ) (P : Prop) :
  (a < 0 → P) → (a = 0 → P) → (0 < a → P) → P := by
  intro an az ap
  by_cases a = 0
  . apply az (by assumption)
  . by_cases 0 < a
    . apply ap (by omega)
    . apply an (by omega)

end Int
