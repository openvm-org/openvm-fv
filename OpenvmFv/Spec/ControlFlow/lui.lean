import OpenvmFv.Spec.run_hart_active

structure LuiInput where
  -- operands
  imm : BitVec 20
  rd: Fin 32
  -- registers
  PC : BitVec 32

structure LuiOutput where
  -- registers
  nextPC : BitVec 32
  rd : Option (Finset.Icc 1 31 × BitVec 32)

def execute_LUI_pure (input : LuiInput) : LuiOutput :=
  {
    nextPC := input.PC + 4#32
    rd := if h: input.rd = 0
      then .none
      else .some (⟨input.rd, by {
        apply Finset.mem_Icc.mpr
        omega
      }⟩, input.imm ++ 0#12)
  }

lemma rv32d_execute_lui :
  LeanRV32D.Functions.execute (instruction.UTYPE (imm, rd, op)) state =
  LeanRV32D.Functions.execute_UTYPE imm rd op state
:= by
  simp [LeanRV32D.Functions.execute]

lemma execute_LUI_pure_equiv
  (lui_input : LuiInput)
  (imm: BitVec 20)
  (rd: regidx)
  (h_input_imm: lui_input.imm = imm)
  (h_input_rd: lui_input.rd = regidx_to_fin rd)
  (h_input_pc: state.regs.get? Register.PC = .some lui_input.PC)
:
  (
    do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV32D.Functions.execute (instruction.UTYPE (imm, rd, uop.LUI))
  ) state =
  let lui_output := execute_LUI_pure lui_input
  (do
    Sail.writeReg Register.nextPC lui_output.nextPC
    match lui_output.rd with
      | .some (reg, rd_val) => write_xreg reg rd_val
      | .none => pure ()
    (pure (ExecutionResult.Retire_Success ()))) state
:= by
  simp [
    readReg_state h_input_pc,
    writeReg_state_success,
    rv32d_execute_lui,
    LeanRV32D.Functions.execute_UTYPE,
  ]

  obtain ⟨⟨rd: Fin 32⟩⟩ := rd
  fin_cases rd <;> simp [
    LeanRV32D.Functions.wX_bits,
    LeanRV32D.Functions.wX,
    LeanRV32D.Functions.regval_into_reg,
    LeanRV32D.Functions.sign_extend,
    Sail.BitVec.signExtend,
    writeReg_state_success,
    LeanRV32D.Functions.xreg_write_callback,
    LeanRV32D.Functions.reg_name_forwards,
    LeanRV32D.Functions.encdec_reg_forwards_matches,
    LeanRV32D.Functions.get_config_use_abi_names,
    LeanRV32D.Functions.not,
    Sail.BitVec.addInt,
    execute_LUI_pure,
    h_input_rd,
    regidx_to_fin,
    write_xreg,
    h_input_imm
  ]
