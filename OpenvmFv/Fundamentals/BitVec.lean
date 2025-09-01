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
