import LeanRV32D
import Mathlib

namespace LeanRV32D.Functions

/-- Revisiting `bool_bits_forwards` in more reasoning-friendly terms -/
@[simp]
lemma bool_bits_forwards_to_if {b : Bool} :
  bool_bits_forwards b = if b then 1#1 else 0#1 := by aesop

section misa

  opaque misa : BitVec 32

end misa

end LeanRV32D.Functions
