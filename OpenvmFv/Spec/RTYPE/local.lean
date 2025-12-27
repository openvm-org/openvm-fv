import OpenvmFv.Spec.run_hart_active

namespace Local
  def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
    (LeanRV32D.Functions.wX_bits rd
      (← do
        match op with
        | .ADD => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) + (← (LeanRV32D.Functions.rX_bits rs2))))
        | .SLT =>
          (pure (zero_extend (m := 32)
              (LeanRV32D.Functions.bool_to_bits (LeanRV32D.Functions.zopz0zI_s (← (LeanRV32D.Functions.rX_bits rs1)) (← (LeanRV32D.Functions.rX_bits rs2))))))
        | .SLTU =>
          (pure (zero_extend (m := 32)
              (LeanRV32D.Functions.bool_to_bits (LeanRV32D.Functions.zopz0zI_u (← (LeanRV32D.Functions.rX_bits rs1)) (← (LeanRV32D.Functions.rX_bits rs2))))))
        | .AND => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) &&& (← (LeanRV32D.Functions.rX_bits rs2))))
        | .OR => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) ||| (← (LeanRV32D.Functions.rX_bits rs2))))
        | .XOR => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) ^^^ (← (LeanRV32D.Functions.rX_bits rs2))))
        | .SLL =>
          (pure (Sail.shift_bits_left (← (LeanRV32D.Functions.rX_bits rs1))
              (Sail.BitVec.extractLsb (← (LeanRV32D.Functions.rX_bits rs2)) (log2_xlen -i 1) 0)))
        | .SRL =>
          (pure (Sail.shift_bits_right (← (LeanRV32D.Functions.rX_bits rs1))
              (Sail.BitVec.extractLsb (← (LeanRV32D.Functions.rX_bits rs2)) (log2_xlen -i 1) 0)))
        | .SUB => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) - (← (LeanRV32D.Functions.rX_bits rs2))))
        | .SRA =>
          (pure (LeanRV32D.Functions.shift_bits_right_arith (← (LeanRV32D.Functions.rX_bits rs1))
              (Sail.BitVec.extractLsb (← (LeanRV32D.Functions.rX_bits rs2)) (log2_xlen -i 1) 0)))))
    (pure LeanRV32D.Functions.RETIRE_SUCCESS)

  lemma execute_RTYPE_equiv :
    execute_RTYPE = LeanRV32D.Functions.execute_RTYPE
  := rfl

end Local
