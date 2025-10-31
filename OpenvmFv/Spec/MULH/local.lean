import OpenvmFv.Spec.run_hart_active

namespace Local

  def execute_MUL (rs2 : regidx) (rs1 : regidx) (rd : regidx) (mul_op : mul_op) : SailM ExecutionResult := do
    let rs1_bits ← do (LeanRV32D.Functions.rX_bits rs1)
    let rs2_bits ← do (LeanRV32D.Functions.rX_bits rs2)
    let rs1_int :=
      if (mul_op.signed_rs1 : Bool)
      then (BitVec.toInt rs1_bits)
      else (BitVec.toNat rs1_bits)
    let rs2_int :=
      if (mul_op.signed_rs2 : Bool)
      then (BitVec.toInt rs2_bits)
      else (BitVec.toNat rs2_bits)
    let result_wide := (LeanRV32D.Functions.to_bits_truncate (l := (2 *i xlen)) (rs1_int *i rs2_int))
    (LeanRV32D.Functions.wX_bits rd
      (if (mul_op.high : Bool)
      then (Sail.BitVec.extractLsb result_wide ((2 *i xlen) -i 1) xlen)
      else (Sail.BitVec.extractLsb result_wide (xlen -i 1) 0)))
    (pure LeanRV32D.Functions.RETIRE_SUCCESS)

  lemma execute_MUL_equiv :
    execute_MUL = LeanRV32D.Functions.execute_MUL
  := rfl

end Local
