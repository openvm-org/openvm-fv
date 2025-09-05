import LeanRV32D
import OpenvmFv.Fundamentals.Core
import OpenvmFv.Fundamentals.RV32D
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
def execute_ITYPE_pure (imm : BitVec 12) (op1 : BitVec 32) (op : iop) :=
  let immext := sign_extend (m := 32) imm
  execute_RTYPE_pure op1 immext (rop_of_iop op)

/-- `execute_ITYPE` with isolated pure part -/
def execute_ITYPE' (imm : BitVec 12) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_ITYPE_pure imm rs1_bits op))
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

section DIV_REM

/-- Multiplication opcodes -/
inductive drop where | DRS | DRU
  deriving BEq, DecidableEq, Inhabited, Repr

def execute_DIV_REM_pure_int (op1 : BitVec 32) (op2 : BitVec 32) (op : drop) : ℤ × ℤ :=
  match op with
  | .DRS =>
      let nop1 := BitVec.toInt op1
      let nop2 := BitVec.toInt op2
      let q := if nop2 = 0 then -1 else
                 if nop1 = -2^31 && nop2 = -1 then -2^31 else
                   Int.tdiv nop1 nop2
      let r := Int.tmod nop1 nop2
      ⟨ q, r ⟩
  | .DRU =>
      let nop1 : ℤ := BitVec.toNat op1
      let nop2 : ℤ := BitVec.toNat op2
      let q := if nop2 = 0 then 2^32 - 1 else Int.tdiv nop1 nop2
      let r := Int.tmod nop1 nop2
      ⟨ q, r ⟩

def execute_DIV_REM_pure (op1 : BitVec 32) (op2 : BitVec 32) (op : drop) : BitVec 64 × BitVec 64 :=
  let ⟨ q, r ⟩ := execute_DIV_REM_pure_int op1 op2 op
  match op with
  | .DRS => ⟨ BitVec.ofInt 32 q, BitVec.ofInt 32 r ⟩
  | .DRU => ⟨ BitVec.ofNat 32 q, BitVec.ofNat 32 r ⟩

def execute_DIV' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let ⟨ result, _ ⟩ := execute_DIV_REM_pure rs1_bits rs2_bits (if is_unsigned then .DRU else .DRS)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

def execute_REM' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let ⟨ _, result ⟩ := execute_DIV_REM_pure rs1_bits rs2_bits (if is_unsigned then .DRU else .DRS)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

set_option maxHeartbeats 100000000 in
@[simp]
lemma execute_DIV'_eq_execute_DIV :
  execute_DIV rs2 rs1 rd usgn = execute_DIV' rs2 rs1 rd usgn := by
  simp_all [execute_DIV, execute_DIV']
  refine bind_congr ?_; intro r1
  refine bind_congr ?_; intro r2
  ext s; simp; congr
  have range_int_r1 : -2147483648 ≤ r1.toInt ∧ r1.toInt < 2147483648 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_int_r2 : -2147483648 ≤ r2.toInt ∧ r2.toInt < 2147483648 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_nat_r1 : 0 ≤ r1.toNat ∧ r1.toNat < 4294967296 := by omega
  have range_nat_r2 : 0 ≤ r2.toNat ∧ r2.toNat < 4294967296 := by omega
  by_cases usgn <;> simp_all [execute_DIV_REM_pure, execute_DIV_REM_pure_int, LeanRV32D.Functions.not, LeanRV32D.Functions.xlen, instHPowInt_leanRV32D] <;>
  by_cases r2z : r2 = 0 <;> simp_all
  . simp [to_bits_truncate, Sail.get_slice_int]
  . repeat rw [ if_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
    rw [← BitVec.toNat_inj]
    simp [to_bits_truncate, Sail.get_slice_int]
    congr; rw [Int.emod_eq_of_lt]
    . apply Int.zero_le_ofNat
    . have := @Int.ediv_le_self r1.toNat r2.toNat (by omega)
      omega
  . simp [to_bits_truncate, Sail.get_slice_int]
  . by_cases of : 2147483648 ≤ r1.toInt.tdiv r2.toInt <;>
    have of' := div_overflow range_int_r1 range_int_r2 <;>
    simp_all [to_bits_truncate, Sail.get_slice_int]
    simp [BitVec.ofNat, BitVec.ofInt]
    congr; simp [Fin.ext_iff]
    omega

@[simp]
lemma execute_REM'_eq_execute_REM :
  execute_REM rs2 rs1 rd usgn = execute_REM' rs2 rs1 rd usgn := by
  simp_all [execute_REM, execute_REM']
  refine bind_congr ?_; intro r1
  refine bind_congr ?_; intro r2
  ext s; simp_all; congr
  have range_int_r1 : -2147483648 ≤ r1.toInt ∧ r1.toInt < 2147483648 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_int_r2 : -2147483648 ≤ r2.toInt ∧ r2.toInt < 2147483648 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_nat_r1 : 0 ≤ r1.toNat ∧ r1.toNat < 4294967296 := by omega
  have range_nat_r2 : 0 ≤ r2.toNat ∧ r2.toNat < 4294967296 := by omega
  by_cases usgn <;> simp_all [execute_DIV_REM_pure, execute_DIV_REM_pure_int] <;>
  by_cases r2z : r2 = 0 <;> simp_all
  . simp [to_bits_truncate, Sail.get_slice_int]
    rw [Nat.mod_eq_of_lt (by omega)]; simp
  . repeat rw [ if_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
    rw [← BitVec.toNat_inj]
    simp [to_bits_truncate, Sail.get_slice_int]
    congr; rw [Int.emod_eq_of_lt]
    . apply Int.zero_le_ofNat
    . rw [Int.tmod_eq_emod_of_nonneg (by omega)]
      trans (r2.toNat : ℤ)
      . simp [← BitVec.toNat_inj] at r2z
        apply Int.emod_lt_of_pos r1.toNat (by omega)
      . omega
  . simp [to_bits_truncate, Sail.get_slice_int]
    simp [← BitVec.toNat_inj]
    have mod_33_to_32 : forall (a : ℤ), (a % 8589934592).toNat % 4294967296 = (a % 4294967296).toNat := by omega
    simp [mod_33_to_32, BitVec.toInt]
    split_ifs with hneg <;> [ skip; simp ] <;> rw [Int.emod_eq_of_lt (by omega)] <;> simp <;> omega
  . repeat rw [ if_neg (by rw [← BitVec.toInt_inj] at r2z; simp_all) ]
    simp_all [to_bits_truncate, Sail.get_slice_int]
    simp [BitVec.ofNat, BitVec.ofInt]
    congr; simp [Fin.ext_iff]
    omega

end DIV_REM
