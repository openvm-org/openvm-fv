import LeanRV32D
import OpenvmFv.Fundamentals.BitVec
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

namespace LeanRV32D.Functions

@[simp]
lemma bool_bits_forwards_to_if {b : Bool} :
  bool_bits_forwards b = if b then 1#1 else 0#1 := by aesop

end LeanRV32D.Functions

section auxiliaries

lemma toInt_toInt_as_toNat_64 {r1 r2 : BitVec 32} :
  (r1.toInt * r2.toInt % 18446744073709551616).toNat =
    (BitVec.signExtend 64 r1 * BitVec.signExtend 64 r2).toNat
    := by
  rw [← BitVec.toInt_signExtend_of_le (v := 64) (x := r1) (by simp)]
  rw [← BitVec.toInt_signExtend_of_le (v := 64) (x := r2) (by simp)]

  have h_max : forall (x : ℤ), max (x % 18446744073709551616) 0 = x % 18446744073709551616 := by omega
  have mr2 : max ((r2.toNat : ℤ) % 18446744073709551616) 0 = (r2.toNat : ℤ) % 18446744073709551616 := by omega
  have rr1 : (r1.toNat : ℤ) % 18446744073709551616 = r1.toNat := by omega
  have rr2 : (r2.toNat : ℤ) % 18446744073709551616 = r2.toNat := by omega

  simp [BitVec.toInt, BitVec.signExtend]; split_ifs

  all_goals
    simp_all
    try omega

  on_goal 1 => have : ((r1.toNat : ℤ) - 4294967296) % 18446744073709551616 = 18446744069414584320 + ↑r1.toNat := by omega
  on_goal 2 => have : ((r2.toNat : ℤ) - 4294967296) % 18446744073709551616 = 18446744069414584320 + ↑r2.toNat := by omega
  on_goal 3 => have : ((r1.toNat : ℤ) - 4294967296) % 18446744073709551616 = 18446744069414584320 + ↑r1.toNat := by omega

  all_goals
    zify; simp_all [Int.toNat_add]
    ring_nf
    omega

lemma toInt_toNat_as_toNat_64 {r1 r2 : BitVec 32} :
  (r1.toInt * r2.toNat % 18446744073709551616).toNat =
    (BitVec.signExtend 64 r1 * BitVec.setWidth 64 r2).toNat
    := by
  simp [← BitVec.toInt_signExtend_of_le (v := 64) (x := r1) (by simp)]

  have h_max : forall (x : ℤ), max (x % 18446744073709551616) 0 = x % 18446744073709551616 := by omega
  have mr2 : max ((r2.toNat : ℤ) % 18446744073709551616) 0 = (r2.toNat : ℤ) % 18446744073709551616 := by omega
  have rr1 : (r1.toNat : ℤ) % 18446744073709551616 = r1.toNat := by omega
  have rr2 : (r2.toNat : ℤ) % 18446744073709551616 = r2.toNat := by omega

  simp [BitVec.toInt, BitVec.signExtend]; split_ifs

  all_goals
    simp_all
    try omega

  . have : ((r1.toNat : ℤ) - 4294967296) % 18446744073709551616 = 18446744069414584320 + ↑r1.toNat := by omega
    zify; simp_all [Int.toNat_add]
    ring_nf
    omega

lemma toNat_toInt_as_toNat_64 {r1 r2 : BitVec 32} :
  ((r1.toNat : ℤ) * r2.toInt % 18446744073709551616).toNat =
    (BitVec.setWidth 64 r1 * BitVec.signExtend 64 r2).toNat
    := by
  simp [← BitVec.toInt_signExtend_of_le (v := 64) (x := r2) (by simp)]

  have h_max : forall (x : ℤ), max (x % 18446744073709551616) 0 = x % 18446744073709551616 := by omega
  have mr1 : max ((r1.toNat : ℤ) % 18446744073709551616) 0 = (r1.toNat : ℤ) % 18446744073709551616 := by omega
  have mr2 : max ((r2.toNat : ℤ) % 18446744073709551616) 0 = (r2.toNat : ℤ) % 18446744073709551616 := by omega
  have rr1 : (r1.toNat : ℤ) % 18446744073709551616 = r1.toNat := by omega
  have rr2 : (r2.toNat : ℤ) % 18446744073709551616 = r2.toNat := by omega

  simp [BitVec.toInt, BitVec.signExtend]; split_ifs

  all_goals
    simp_all
    try omega

  . have : ((r2.toNat : ℤ) - 4294967296) % 18446744073709551616 = 18446744069414584320 + ↑r2.toNat := by omega
    zify; simp_all [Int.toNat_add]
    ring_nf
    omega

end auxiliaries

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

/-- Pure part of 32-bit `execute_RTYPE`, for `U32` arguments -/
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

/-- Equivalence of `execute_RTYPE` pure part computation -/
lemma execute_RTYPE_pure_equiv (op1 : U32) (op2 : U32) (op : rop) :
  execute_RTYPE_pure op1.toBV op2.toBV op = execute_RTYPE_pure_U32 op1 op2 op := by
  cases op <;> simp [execute_RTYPE_pure] <;> [ aesop; aesop; skip ]
  . have toNat_31 : (31 + (op2.toNat : ℤ) % 32).toNat = 31 + op2.toNat % 32 := by omega
    have toNat_32 : (32 + (op2.toNat : ℤ) % 32).toNat = 32 + op2.toNat % 32 := by omega
    rw [U32.toBV_toNat, BitVec.toNat_ofNat]; simp
    rw [toNat_31, toNat_32]
    simp [BitVec.sshiftright_eq]

/-- `execute_RTYPE` with isolated pure part -/
def execute_RTYPE' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_RTYPE_pure rs1_bits rs2_bits op))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_RTYPE`s -/
@[simp]
lemma execute_RTYPE_eq_execute_RTYPE' :
  execute_RTYPE rs2 rs1 rd op = execute_RTYPE' rs2 rs1 rd op
  := by cases op <;> simp_all [execute_RTYPE', execute_RTYPE, execute_RTYPE_pure] <;> congr

end RTYPE

section ITYPE

@[simp]
def rop_of_iop (op : iop) : rop :=
  match op with
  | .ADDI => .ADD
  | .SLTI => .SLT
  | .SLTIU => .SLTU
  | .XORI => .XOR
  | .ORI => .OR
  | .ANDI => .AND

/-- Pure part of 32-bit `execute_ITYPE` -/
def execute_ITYPE_pure (op1 : BitVec 32) (op2 : BitVec 32) (op : iop) :=
  execute_RTYPE_pure op1 op2 (rop_of_iop op)

/-- Pure part of 32-bit `execute_RTYPE`, for `U32` arguments -/
def execute_ITYPE_pure_U32 (op1 : U32) (op2 : U32) (op : iop) :=
  execute_RTYPE_pure_U32 op1 op2 (rop_of_iop op)

/-- Equivalence of `execute_RTYPE` pure part computation -/
lemma execute_ITYPE_pure_equiv (op1 : U32) (op2 : U32) (op : iop) :
  execute_ITYPE_pure op1.toBV op2.toBV op = execute_ITYPE_pure_U32 op1 op2 op := by
  simp [execute_ITYPE_pure]
  cases op <;> simp <;> exact execute_RTYPE_pure_equiv _ _ _

/-- `execute_ITYPE` with isolated pure part -/
def execute_ITYPE' (imm : BitVec 12) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let immext := sign_extend (m := 32) imm
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_ITYPE_pure rs1_bits immext op))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_RTYPE`s -/
@[simp]
lemma execute_ITYPE_eq_execute_ITYPE' :
  execute_ITYPE imm rs1 rd op = execute_ITYPE' imm rs1 rd op
  := by cases op <;> simp_all [execute_ITYPE', execute_ITYPE, execute_ITYPE_pure, execute_RTYPE_pure]

end ITYPE

section SHIFTIOP

@[simp]
def rop_of_sop (op : sop) : rop :=
  match op with
  | .SLLI => .SLL
  | .SRLI => .SRL
  | .SRAI => .SRA

/-- Pure part of a 32-bit `execute_SHIFTIOP` -/
def execute_SHIFTIOP_pure (op1 : BitVec 32) (shamt : BitVec 6) (op : sop) :=
  let shamt32 : BitVec 32 := shamt
  execute_RTYPE_pure op1 shamt32 (rop_of_sop op)

/-- Pure part of a 32-bit `execute_SHIFTIOP`, for `U32` arguments -/
@[simp] def execute_SHIFTIOP_pure_U32 (op1 : U32) (shamt : BitVec 6) (op : sop) :=
  let shamtBV : BitVec 8 := ⟨shamt.toNat, by omega⟩
  execute_RTYPE_pure_U32 op1 #v[shamtBV, 0, 0, 0] (rop_of_sop op)

/-- Equivalence of `exec_SHIFTIOP` pure part computation -/
lemma execute_SHIFTIOP_pure_equiv (op1 : U32) (shamt : BitVec 6) (op : sop) :
  execute_SHIFTIOP_pure op1.toBV shamt op = execute_SHIFTIOP_pure_U32 op1 shamt op := by
  simp only [execute_SHIFTIOP_pure_U32, execute_SHIFTIOP_pure]
  rw [← execute_RTYPE_pure_equiv]
  suffices : (BitVec.setWidth 32 shamt) = U32.toBV #v[⟨shamt.toNat, by omega⟩, 0, 0, 0]
  . rw [this]
  . rw [← BitVec.toNat_inj]
    simp [U32.toNat]; omega

/-- `execute_SHIFTIOP` with isolated pure part -/
def execute_SHIFTIOP' (shamt : BitVec 6) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_SHIFTIOP_pure rs1_bits shamt op))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_SHIFTIOP`s -/
@[simp]
lemma execute_SHIFTIOP_eq_execute_SHIFTIOP' :
  execute_SHIFTIOP shamt rs1 rd op = execute_SHIFTIOP' shamt rs1 rd op
  := by
    have h_eq_shamt : BitVec.ofNat 5 (shamt.toNat % 4294967296) = shamt := by
      rw [Nat.mod_eq_of_lt (by omega)]; simp
    simp [execute_SHIFTIOP, execute_SHIFTIOP', execute_SHIFTIOP_pure, execute_RTYPE_pure]
    cases op <;> simp <;> aesop

end SHIFTIOP

section MUL

/-- Multiplication opcodes -/
inductive mop where | MUL | MULH | MULHU | MULHUS | MULHSU
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Conversion from RISC-V spec representation to `mop` -/
def mop_of_mul_op (m : mul_op) : mop :=
  match m with
  | { high := false, signed_rs1 := _, signed_rs2 := _ } => .MUL
  | { high := true, signed_rs1 := false, signed_rs2 := false } => .MULHU
  | { high := true, signed_rs1 := false, signed_rs2 := true } => .MULHUS
  | { high := true, signed_rs1 := true, signed_rs2 := false } => .MULHSU
  | { high := true, signed_rs1 := true, signed_rs2 := true } => .MULH

/-- Pure part of 32-bit `execute_MUL` -/
def execute_MUL_pure (op1 : BitVec 32) (op2 : BitVec 32) (op : mop) : BitVec 64 :=
  let rs1_ext : BitVec 64 := op1.extend 64 (op = .MULH ∨ op = .MULHSU)
  let rs2_ext : BitVec 64 := op2.extend 64 (op = .MULH ∨ op = .MULHUS)
  let result_wide := rs1_ext * rs2_ext
  (if (op = .MUL)
    then (Sail.BitVec.extractLsb result_wide 31 0)
    else (Sail.BitVec.extractLsb result_wide 63 32))

/-- Pure part of 32-bit `execute_MUL`, for `U32` arguments -/
def execute_MUL_pure_U32 (op1 : U32) (op2 : U32) (op : mop) : BitVec 32 :=
  let op1_ext := op1.toBV.extend 64 (op = .MULH ∨ op = .MULHSU)
  let op2_ext := op2.toBV.extend 64 (op = .MULH ∨ op = .MULHUS)
  let result_wide := op1_ext * op2_ext
  (if (op = .MUL)
    then (Sail.BitVec.extractLsb result_wide 31 0)
    else (Sail.BitVec.extractLsb result_wide 63 32))

/-- Equivalence of `execute_MUL` pure part computation -/
lemma execute_MUL_pure_equiv (op1 : U32) (op2 : U32) (op : mop) :
  execute_MUL_pure op1.toBV op2.toBV op = execute_MUL_pure_U32 op1 op2 op := by
  cases op <;> simp [execute_MUL_pure, execute_MUL_pure_U32]

def execute_MUL' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (m : mop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_MUL_pure rs1_bits rs2_bits m))
  (pure RETIRE_SUCCESS)

set_option maxHeartbeats 10000000 in
@[simp]
lemma execute_MUL_eq_execute_MUL' :
  execute_MUL rs2 rs1 rd op = execute_MUL' rs2 rs1 rd (mop_of_mul_op op)
    := by
  have bounds_toInt_32 : forall (bv : BitVec 32), -2^31 ≤ bv.toInt ∧ bv.toInt < 2^31 := by simp [BitVec.toInt]; intros; split_ifs <;> omega
  have bounds_toNat_32 : forall (bv : BitVec 32), 0 ≤ bv.toNat ∧ bv.toNat < 2^32 := by omega

  rcases op with ⟨ high, sgn1, sgn2 ⟩
  rcases sgn2 with sgn2 | sgn2 <;> rcases sgn1 with sgn1 | sgn1 <;> rcases high with high | high

  all_goals
    simp_all [execute_MUL', execute_MUL, execute_MUL_pure, BitVec.extend, mop_of_mul_op, LeanRV32D.Functions.xlen, to_bits_truncate, Sail.get_slice_int]
    refine bind_congr ?_; intro r1
    refine bind_congr ?_; intro r2
    ext s; simp_all; congr 3
    have mod_65_to_64 : forall (a : ℤ), (a % 36893488147419103232).toNat % 18446744073709551616 = (a % 18446744073709551616).toNat := by omega

  . rw [Int.toNat_emod (by nlinarith) (by simp)]
    rw [Int.toNat_mul (by simp) (by simp)]
    simp

  . rw [Int.toNat_emod (by nlinarith) (by simp)]
    rw [Int.toNat_mul (by simp) (by simp)]
    simp

  . unfold BitVec.toInt
    split_ifs <;> simp_all
    . rw [Int.toNat_emod (by nlinarith) (by simp)]
      simp; congr
    . simp [← BitVec.toNat_inj]
      trans (- (((4294967296 : ℤ) - r1.toNat) * r2.toNat) % 18446744073709551616).toNat % 4294967296
      . congr 3
        ring_nf
      . rw [Int.neg_emod_eq_sub_emod]
        have := bounds_toNat_32 r1
        have := bounds_toNat_32 r2
        rw [Int.toNat_emod (by nlinarith) (by simp)]
        rw [Int.toNat_sub'' (by simp) (by nlinarith)]
        simp only [Int.reduceToNat]
        rw [Int.toNat_mul (by omega) (by omega)]
        simp
        rw [Nat.mul_sub_right_distrib]
        rw [Nat.sub_sub_right _ (by nlinarith)]
        omega

  . congr 2
    rw [mod_65_to_64]
    apply toInt_toNat_as_toNat_64

  . unfold BitVec.toInt
    split_ifs <;> simp_all
    . rw [Int.toNat_emod (by nlinarith) (by simp)]
      simp; congr
    . simp [← BitVec.toNat_inj]
      trans (- ((r1.toNat : ℤ) * ((4294967296 : ℤ) - r2.toNat)) % 18446744073709551616).toNat % 4294967296
      . congr 3
        ring_nf
      . rw [Int.neg_emod_eq_sub_emod]
        have := bounds_toNat_32 r1
        have := bounds_toNat_32 r2
        rw [Int.toNat_emod (by nlinarith) (by simp)]
        rw [Int.toNat_sub'' (by simp) (by nlinarith)]
        simp only [Int.reduceToNat]
        rw [Int.toNat_mul (by omega) (by omega)]
        simp
        rw [Nat.mul_sub_left_distrib]
        rw [Nat.sub_sub_right _ (by nlinarith)]
        omega

  . congr 2
    rw [mod_65_to_64]
    apply toNat_toInt_as_toNat_64

  . unfold BitVec.toInt
    split_ifs <;> simp_all
    . rw [Int.toNat_emod (by nlinarith) (by simp)]
      simp; congr
    . simp [← BitVec.toNat_inj]
      trans (- ((r1.toNat : ℤ) * ((4294967296 : ℤ) - r2.toNat)) % 18446744073709551616).toNat % 4294967296
      . congr 3
        ring_nf
      . rw [Int.neg_emod_eq_sub_emod]
        have := bounds_toNat_32 r1
        have := bounds_toNat_32 r2
        rw [Int.toNat_emod (by nlinarith) (by simp)]
        rw [Int.toNat_sub'' (by simp) (by nlinarith)]
        simp only [Int.reduceToNat]
        rw [Int.toNat_mul (by omega) (by omega)]
        simp
        rw [Nat.mul_sub_left_distrib ]
        rw [Nat.sub_sub_right _ (by nlinarith)]
        omega
    . simp [← BitVec.toNat_inj]
      trans (- (((4294967296 : ℤ) - r1.toNat) * r2.toNat) % 18446744073709551616).toNat % 4294967296
      . congr 3
        ring_nf
      . rw [Int.neg_emod_eq_sub_emod]
        have := bounds_toNat_32 r1
        have := bounds_toNat_32 r2
        rw [Int.toNat_emod (by nlinarith) (by simp)]
        rw [Int.toNat_sub'' (by simp) (by nlinarith)]
        simp only [Int.reduceToNat]
        rw [Int.toNat_mul (by omega) (by omega)]
        simp
        rw [Nat.mul_sub_right_distrib]
        rw [Nat.sub_sub_right _ (by nlinarith)]
        omega
    . simp [← BitVec.toNat_inj]
      trans (((4294967296 : ℤ) - r1.toNat) * (4294967296 - r2.toNat) % 18446744073709551616).toNat % 4294967296
      . congr 3
        ring_nf
      . have := bounds_toNat_32 r1
        have := bounds_toNat_32 r2
        rw [Int.toNat_emod (by nlinarith) (by simp)]
        simp only [Int.reduceToNat]
        rw [Int.toNat_mul (by omega) (by omega)]
        simp [Nat.mul_sub_right_distrib]
        repeat rw [Nat.mul_sub_left_distrib]
        rw [Nat.sub_sub_right _ (by nlinarith)]
        ring_nf
        suffices : (r1.toNat * 4294967296) % 4294967296 = 0
        . have : forall x y, y * 4294967296 ≤ x → (x - y * 4294967296) % 4294967296 = x % 4294967296 := by intro; omega
          rw [this]
          . omega
          . suffices : r1.toNat * 4294967296 + r2.toNat * 4294967296 ≤ r2.toNat * r1.toNat + 18446744073709551616
            . rw [← Nat.add_sub_assoc (by omega)]
              rw [Nat.le_sub_iff_add_le (by nlinarith)]
              assumption
            . nlinarith
        . omega

  . congr 2
    rw [mod_65_to_64]
    . rw [← BitVec.toNat_mul]
      apply toInt_toInt_as_toNat_64

end MUL
