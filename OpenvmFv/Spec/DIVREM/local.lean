import OpenvmFv.Spec.run_hart_active

namespace Local
  def execute_DIV (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
    let rs1_bits ← do (LeanRV32D.Functions.rX_bits rs1)
    let rs2_bits ← do (LeanRV32D.Functions.rX_bits rs2)
    let rs1_int : Int :=
      if (is_unsigned : Bool)
      then (BitVec.toNat rs1_bits)
      else (BitVec.toInt rs1_bits)
    let rs2_int : Int :=
      if (is_unsigned : Bool)
      then (BitVec.toNat rs2_bits)
      else (BitVec.toInt rs2_bits)
    let quotient : Int :=
      if ((rs2_int == 0) : Bool)
      then (-1)
      else (Int.tdiv rs1_int rs2_int)
    let quotient : Int :=
      if (((not is_unsigned) && (quotient ≥b (2 ^i (xlen -i 1)))) : Bool)
      then (Neg.neg (2 ^i (xlen -i 1)))
      else quotient
    (LeanRV32D.Functions.wX_bits rd (LeanRV32D.Functions.to_bits_truncate (l := 32) quotient))
    (pure LeanRV32D.Functions.RETIRE_SUCCESS)

  def execute_REM (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
    let rs1_bits ← do (LeanRV32D.Functions.rX_bits rs1)
    let rs2_bits ← do (LeanRV32D.Functions.rX_bits rs2)
    let rs1_int : Int :=
      if (is_unsigned : Bool)
      then (BitVec.toNat rs1_bits)
      else (BitVec.toInt rs1_bits)
    let rs2_int : Int :=
      if (is_unsigned : Bool)
      then (BitVec.toNat rs2_bits)
      else (BitVec.toInt rs2_bits)
    let remainder : Int :=
      if ((rs2_int == 0) : Bool)
      then rs1_int
      else (Int.tmod rs1_int rs2_int)
    (LeanRV32D.Functions.wX_bits rd (LeanRV32D.Functions.to_bits_truncate (l := 32) remainder))
    (pure LeanRV32D.Functions.RETIRE_SUCCESS)

  lemma execute_DIV_equiv :
    execute_DIV = LeanRV32D.Functions.execute_DIV
  := rfl

  lemma execute_REM_equiv :
    execute_REM = LeanRV32D.Functions.execute_REM
  := rfl

end Local
