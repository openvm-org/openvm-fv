import LeanRV32D
import OpenvmFv.Fundamentals.U32

open PreSail
open LeanRV32D.Functions

attribute [simp]
  bool_to_bits
  shift_bits_right_arith
  shift_right_arith
  sign_extend
  zero_extend
  zopz0zI_s
  zopz0zI_u
  Sail.BitVec.extractLsb
  Sail.BitVec.signExtend
  Sail.BitVec.zeroExtend
  Sail.shift_bits_left
  Sail.shift_bits_right

attribute [local simp]
  BitVec.extractLsb
  BitVec.extractLsb'

namespace BitVec

lemma sshiftright_eq {n : ℕ} {bv : BitVec n} {shift : ℕ} :
  bv.sshiftRight shift =
    BitVec.setWidth n
      (BitVec.extractLsb ((n - 1) + shift) shift (BitVec.signExtend (n + shift) bv))
    := by grind

end BitVec

namespace LeanRV32D.Functions

@[simp]
lemma bool_bits_forwards_to_if {b : Bool} :
  bool_bits_forwards b = if b then 1#1 else 0#1 := by aesop

end LeanRV32D.Functions

section RTYPE

/-- Pure part of 32-bit `execute_RTYPE` -/
def execute_RTYPE_pure (op1 : BitVec 32) (op2 : BitVec 32) (op : rop) :=
  match op with
  | .ADD => op1 + op2
  | .SLT => zero_extend (m := 32) (bool_to_bits (zopz0zI_s op1 op2))
  | .SLTU => zero_extend (m := 32) (bool_to_bits (zopz0zI_u op1 op2))
  | .AND => op1 &&& op2
  | .OR => op1 ||| op2
  | .XOR => op1 ^^^ op2
  | .SLL => Sail.shift_bits_left op1 (Sail.BitVec.extractLsb op2 4 0)
  | .SRL => Sail.shift_bits_right op1 (Sail.BitVec.extractLsb op2 4 0)
  | .SUB => op1 - op2
  | .SRA => shift_bits_right_arith op1 (Sail.BitVec.extractLsb op2 4 0)

/-- Pure part of 32-bit , for `U32` arguments -/
@[simp] def execute_RTYPE_pure_U32 (op1 : U32) (op2 : U32) (op : rop) :=
match op with
  | .ADD => op1.toBV + op2.toBV
  | .SLT => if op1.toInt < op2.toInt then 1#64 else 0#64
  | .SLTU => if op1.toNat < op2.toNat then 1#64 else 0#64
  | .AND => op1.toBV &&& op2.toBV
  | .OR => op1.toBV ||| op2.toBV
  | .XOR => op1.toBV ^^^ op2.toBV
  | .SLL => op1.toBV <<< (BitVec.setWidth 5 op2.toBV)
  | .SRL => op1.toBV >>> (BitVec.setWidth 5 op2.toBV)
  | .SUB => op1.toBV - op2.toBV
  | .SRA => op1.toBV.sshiftRight (BitVec.setWidth 5 op2.toBV).toNat

set_option trace.Meta.Tactic.simp.rewrite true

/-- Equivalence of `execute_RTYPE` pure part computation -/
lemma exec_RTYPE_pure_equiv (op1 : U32) (op2 : U32) (op : rop) :
  execute_RTYPE_pure op1.toBV op2.toBV op = execute_RTYPE_pure_U32 op1 op2 op := by
  cases op <;> simp [execute_RTYPE_pure]
  . aesop
  . aesop
  . have toNat_31 : (31 + (op2.toNat : ℤ) % 32).toNat = 31 + op2.toNat % 32 := by omega
    have toNat_32 : (32 + (op2.toNat : ℤ) % 32).toNat = 32 + op2.toNat % 32 := by omega
    rw [U32.toBV_toNat, BitVec.toNat_ofNat]; simp
    rw [toNat_31, toNat_32]
    simp [BitVec.sshiftright_eq]
