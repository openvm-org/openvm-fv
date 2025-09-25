import OpenvmFv.Spec.run_hart_active

namespace Local
  def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
    (LeanRV32D.Functions.wX_bits rd
      (← do
        match op with
        | .ADD => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) + (← (LeanRV32D.Functions.rX_bits rs2))))
        | .SLT =>
          (pure (LeanRV32D.Functions.zero_extend (m := 32)
              (LeanRV32D.Functions.bool_to_bits (LeanRV32D.Functions.zopz0zI_s (← (LeanRV32D.Functions.rX_bits rs1)) (← (LeanRV32D.Functions.rX_bits rs2))))))
        | .SLTU =>
          (pure (LeanRV32D.Functions.zero_extend (m := 32)
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

  def execute_ITYPE (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
    let immext : xlenbits := (LeanRV32D.Functions.sign_extend (m := 32) imm)
    (LeanRV32D.Functions.wX_bits rd
      (← do
        match op with
        | .ADDI => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) + immext))
        | .SLTI => (pure (LeanRV32D.Functions.zero_extend (m := 32) (LeanRV32D.Functions.bool_to_bits (LeanRV32D.Functions.zopz0zI_s (← (LeanRV32D.Functions.rX_bits rs1)) immext))))
        | .SLTIU =>
          (pure (LeanRV32D.Functions.zero_extend (m := 32) (LeanRV32D.Functions.bool_to_bits (LeanRV32D.Functions.zopz0zI_u (← (LeanRV32D.Functions.rX_bits rs1)) immext))))
        | .ANDI => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) &&& immext))
        | .ORI => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) ||| immext))
        | .XORI => (pure ((← (LeanRV32D.Functions.rX_bits rs1)) ^^^ immext))))
    (pure LeanRV32D.Functions.RETIRE_SUCCESS)

  lemma execute_ITYPE_equiv :
    execute_ITYPE = LeanRV32D.Functions.execute_ITYPE
  := rfl
end Local
