import OpenvmFv.Spec.run_hart_active

namespace Local

  def execute_SHIFTIOP (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
    let shamt := (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)
    (LeanRV32D.Functions.wX_bits rd
      (← do
        match op with
        | .SLLI => (pure (Sail.shift_bits_left (← (LeanRV32D.Functions.rX_bits rs1)) shamt))
        | .SRLI => (pure (Sail.shift_bits_right (← (LeanRV32D.Functions.rX_bits rs1)) shamt))
        | .SRAI => (pure (LeanRV32D.Functions.shift_bits_right_arith (← (LeanRV32D.Functions.rX_bits rs1)) shamt))))
    (pure LeanRV32D.Functions.RETIRE_SUCCESS)

  lemma execute_SHIFTIOP_equiv :
    execute_SHIFTIOP = LeanRV32D.Functions.execute_SHIFTIOP
  := rfl
end Local
