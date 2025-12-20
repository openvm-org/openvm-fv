import OpenvmFv.Spec.run_hart_active

structure JalrInput where
  -- operands
  imm : BitVec 12
  rs1_val: BitVec 32
  rd: Fin 32
  -- registers
  PC : BitVec 32
  misa : BitVec 32

structure JalrOutput where
  -- registers
  nextPC : Option (BitVec 32)
  rd : Option (Finset.Icc 1 31 × BitVec 32)
  -- result
  success : Bool

def execute_JALR_pure (input : JalrInput) : JalrOutput :=
  let bit1_valid := (BitVec.ofBool (input.rs1_val + BitVec.signExtend 32 input.imm)[1]! == 0#1)
  let mask := 0xFFFFFFFE
  {
    nextPC :=
      if (!bit1_valid && !input.misa[2])
      then (.some (input.PC + 4))
      else (.some (mask &&& (input.rs1_val + BitVec.signExtend 32 input.imm)))
    rd := if h: (!bit1_valid && !input.misa[2]) || input.rd = 0
    then .none
    else (
      .some (⟨input.rd, by {
        simp at h
        apply Finset.mem_Icc.mpr
        omega
      }⟩, input.PC + 4))
    success := (bit1_valid || input.misa[2])
  }

lemma rv32d_execute_jalr :
  LeanRV32D.Functions.execute (instruction.JALR (imm, rs1, rd)) state =
  LeanRV32D.Functions.execute_JALR imm rs1 rd state
:= by
  simp [LeanRV32D.Functions.execute]

set_option maxHeartbeats 0 in
lemma execute_JALR_pure_equiv
  (jalr_input : JalrInput)
  (imm: BitVec 12)
  (rs1 rd: regidx)
  (h_input_imm: jalr_input.imm = imm)
  (h_input_rd: jalr_input.rd = regidx_to_fin rd)
  (h_input_rs1: read_xreg (regidx_to_fin rs1) state = EStateM.Result.ok (jalr_input.rs1_val) state)
  (h_input_pc: state.regs.get? Register.PC = .some jalr_input.PC)
  (h_input_misa: state.regs.get? Register.misa = .some jalr_input.misa)
:
  (
    do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV32D.Functions.execute (instruction.JALR (imm, rs1, rd))
  ) state =
  let jalr_output := execute_JALR_pure jalr_input
  (do
    match jalr_output.nextPC with
      | .some nextPC => Sail.writeReg Register.nextPC nextPC
      | .none => pure ()
    match jalr_output.rd with
      | .some (reg, rd_val) => write_xreg reg rd_val
      | .none => pure ()
    if !jalr_output.success then
      pure (
        ExecutionResult.Memory_Exception (
          (virtaddr.Virtaddr (0xFFFFFFFE &&& (jalr_input.rs1_val + BitVec.signExtend 32 jalr_input.imm))),
          (ExceptionType.E_Fetch_Addr_Align ())
        )
      )
    else
      (pure (ExecutionResult.Retire_Success ()))) state
:= by
  simp [
    readReg_state h_input_pc,
    writeReg_state_success,
    rv32d_execute_jalr,
    LeanRV32D.Functions.execute_JALR,
    LeanRV32D.Functions.get_next_pc,
    readReg_state (writeReg_read_same _)
  ]

  obtain ⟨⟨rs1: Fin 32⟩⟩ := rs1

  rewrite [
    rX_read_xreg_equiv _ ⟨⟨rs1⟩⟩ rs1 (by simp)
  ]

  simp [
    regidx_to_fin
  ] at h_input_rs1

  simp [
    h_input_rs1,
    read_xreg_write_reg_state_nextPC,
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
    Sail.BitVec.signExtend,
    Sail.BitVec.update,
    Sail.BitVec.updateSubrange',
    readReg_state (writeReg_read_diff h_input_misa (show Register.misa ≠ Register.nextPC by grind)),
    LeanRV32D.Functions.not,
  ]

  by_cases h_bit1 : BitVec.ofBool (jalr_input.rs1_val + BitVec.signExtend 32 imm)[1] = 0#1
  . simp [
      h_bit1,
      ExceptT.mk,
      ExceptT.map,
      writeReg_state_success,
      writeReg_write_same
    ]

    obtain ⟨⟨rd: Fin 32⟩⟩ := rd
    fin_cases rd <;> simp [
      LeanRV32D.Functions.wX_bits,
      LeanRV32D.Functions.wX,
      writeReg_state_success,
      LeanRV32D.Functions.xreg_write_callback,
      LeanRV32D.Functions.reg_name_forwards,
      LeanRV32D.Functions.encdec_reg_forwards_matches,
      LeanRV32D.Functions.get_config_use_abi_names,
      LeanRV32D.Functions.not,
      LeanRV32D.Functions.regval_into_reg,
      execute_JALR_pure,
      h_input_imm,
      h_bit1,
      h_input_rd,
      regidx_to_fin,
      write_xreg,
    ]
    done
  . replace h_bit1 := bit_eq_one_of_not_eq_zero _ h_bit1
    simp [
      h_bit1,
      execute_JALR_pure,
      h_input_imm
    ]
    by_cases h_misa: jalr_input.misa[2]
    . simp [
        h_misa,
        ExceptT.map,
        ExceptT.mk,
        writeReg_state_success,
        writeReg_write_same
      ]
      obtain ⟨⟨rd: Fin 32⟩⟩ := rd
      fin_cases rd <;> simp [
        LeanRV32D.Functions.wX_bits,
        LeanRV32D.Functions.wX,
        writeReg_state_success,
        LeanRV32D.Functions.xreg_write_callback,
        LeanRV32D.Functions.reg_name_forwards,
        LeanRV32D.Functions.encdec_reg_forwards_matches,
        LeanRV32D.Functions.get_config_use_abi_names,
        LeanRV32D.Functions.not,
        LeanRV32D.Functions.regval_into_reg,
        h_input_rd,
        regidx_to_fin,
        write_xreg,
      ]
      done
    . simp [
        h_misa,
        ExceptT.pure,
        ExceptT.mk
      ]
