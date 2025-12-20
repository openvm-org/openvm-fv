import OpenvmFv.Spec.run_hart_active

structure JalInput where
  -- operands
  imm : BitVec 21
  rd: Fin 32
  -- registers
  PC : BitVec 32
  misa : BitVec 32

structure JalOutput where
  -- registers
  nextPC : Option (BitVec 32)
  rd : Option (Finset.Icc 1 31 × BitVec 32)
  -- result
  success : Bool
  throws : Bool

def execute_JAL_pure (input : JalInput) : JalOutput :=
  let bit0_valid := (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0]! == 0#1)
  let bit1_valid := (BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1]! == 0#1)
  {
    nextPC :=
      if !bit0_valid || (!bit1_valid && !input.misa[2])
      then (.some (input.PC + 4))
      else (.some (input.PC + BitVec.signExtend 32 input.imm))
    rd := if h: !bit0_valid || (!bit1_valid && !input.misa[2]) || input.rd = 0
    then .none
    else (
      .some (⟨input.rd, by {
        simp at h
        apply Finset.mem_Icc.mpr
        omega
      }⟩, input.PC + 4))
    success := bit0_valid && (bit1_valid || input.misa[2])
    throws := !bit0_valid
  }

lemma rv32d_execute_jal :
  LeanRV32D.Functions.execute (instruction.JAL (imm, rd)) state =
  LeanRV32D.Functions.execute_JAL imm rd state
:= by
  simp [LeanRV32D.Functions.execute]

set_option maxHeartbeats 0 in
lemma execute_JAL_pure_equiv
  (jal_input : JalInput)
  (imm: BitVec 21)
  (rd: regidx)
  (h_input_imm: jal_input.imm = imm)
  (h_input_rd: jal_input.rd = regidx_to_fin rd)
  (h_input_pc: state.regs.get? Register.PC = .some jal_input.PC)
  (h_input_misa: state.regs.get? Register.misa = .some jal_input.misa)
:
  (
    do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV32D.Functions.execute (instruction.JAL (imm, rd))
  ) state =
  let jal_output := execute_JAL_pure jal_input
  (do
    match jal_output.nextPC with
      | .some nextPC => Sail.writeReg Register.nextPC nextPC
      | .none => pure ()
    match jal_output.rd with
      | .some (reg, rd_val) => write_xreg reg rd_val
      | .none => pure ()
    if jal_output.throws then
      throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
    else if !jal_output.success then
      pure (
        ExecutionResult.Memory_Exception (
          (virtaddr.Virtaddr (jal_input.PC + BitVec.signExtend 32 jal_input.imm)),
          (ExceptionType.E_Fetch_Addr_Align ())
        )
      )
    else
      (pure (ExecutionResult.Retire_Success ()))) state
:= by
  simp [
    readReg_state h_input_pc,
    writeReg_state_success,
    rv32d_execute_jal,
    LeanRV32D.Functions.execute_JAL,
    LeanRV32D.Functions.get_next_pc,
    readReg_state (writeReg_read_same _),
    readReg_state (writeReg_read_diff h_input_pc (show Register.PC ≠ Register.nextPC by grind)),
    LeanRV32D.Functions.jump_to
  ]
  unfold liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ExceptT.instMonadLift ExceptT.lift ExceptT.mk Functor.map EStateM.instMonad
  simp
  unfold EStateM.map
  simp [
    Sail.SailME.run,
    ExceptT.run,
    Sail.BitVec.addInt
  ]
  unfold bind ExceptT.instMonad ExceptT.bind ExceptT.mk bind
  simp
  unfold ExceptT.bindCont EStateM.bind
  simp [
    LeanRV32D.Functions.sign_extend,
    Sail.BitVec.signExtend
  ]

  by_cases h_bit0 : BitVec.ofBool (jal_input.PC + BitVec.signExtend 32 imm)[0] = 0#1
  . simp [
      h_bit0,
      readReg_state (writeReg_read_diff h_input_misa (show Register.misa ≠ Register.nextPC by grind)),
      LeanRV32D.Functions.not,
      ExceptT.pure, ExceptT.mk
    ]
    by_cases h_bit1 : BitVec.ofBool (jal_input.PC + BitVec.signExtend 32 imm)[1] = 1#1
    . simp [h_bit1]
      simp [
        execute_JAL_pure,
        h_input_imm,
        h_bit0,
        h_bit1
      ]
      by_cases h_misa : jal_input.misa[2]
      . simp [
          h_misa,
          ExceptT.map,
          ExceptT.mk,
          writeReg_state_success,
          writeReg_write_same
        ]
        obtain ⟨⟨rd: Fin 32⟩⟩ := rd
        fin_cases rd <;> simp [
          h_input_rd,
          regidx_to_fin,
          LeanRV32D.Functions.wX_bits,
          LeanRV32D.Functions.wX,
          LeanRV32D.Functions.regval_into_reg,
          writeReg_state_success,
          LeanRV32D.Functions.xreg_write_callback,
          LeanRV32D.Functions.reg_name_forwards,
          LeanRV32D.Functions.encdec_reg_forwards_matches,
          LeanRV32D.Functions.get_config_use_abi_names,
          LeanRV32D.Functions.not,
          write_xreg
        ]
      . simp [
          h_misa
        ]
    . simp [
        h_bit1,
        ExceptT.map,
        ExceptT.mk,
        writeReg_state_success,
        writeReg_write_same,
        execute_JAL_pure,
        h_input_imm,
        h_bit0
      ]
      by_cases h_misa : jal_input.misa[2]
      . simp [
          h_misa,
          h_input_rd,
        ]
        obtain ⟨⟨rd: Fin 32⟩⟩ := rd
        fin_cases rd <;> simp [
          regidx_to_fin,
          LeanRV32D.Functions.wX_bits,
          LeanRV32D.Functions.wX,
          LeanRV32D.Functions.regval_into_reg,
          writeReg_state_success,
          LeanRV32D.Functions.xreg_write_callback,
          LeanRV32D.Functions.reg_name_forwards,
          LeanRV32D.Functions.encdec_reg_forwards_matches,
          LeanRV32D.Functions.get_config_use_abi_names,
          LeanRV32D.Functions.not,
          write_xreg
        ]
      . replace h_bit1 := bit_eq_zero_of_not_eq_one _ h_bit1
        simp [
          h_misa,
          h_bit1
        ]
        obtain ⟨⟨rd: Fin 32⟩⟩ := rd
        fin_cases rd <;> simp [
          h_input_rd,
          regidx_to_fin,
          LeanRV32D.Functions.wX_bits,
          LeanRV32D.Functions.wX,
          LeanRV32D.Functions.regval_into_reg,
          writeReg_state_success,
          LeanRV32D.Functions.xreg_write_callback,
          LeanRV32D.Functions.reg_name_forwards,
          LeanRV32D.Functions.encdec_reg_forwards_matches,
          LeanRV32D.Functions.get_config_use_abi_names,
          LeanRV32D.Functions.not,
          write_xreg
        ]
  . replace h_bit0 := bit_eq_one_of_not_eq_zero _ h_bit0
    simp [
      h_bit0,
      execute_JAL_pure,
      h_input_imm
    ]
