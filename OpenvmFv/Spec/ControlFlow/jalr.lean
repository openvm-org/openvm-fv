import OpenvmFv.Spec.run_hart_active

namespace PureSpec

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

  lemma cur_privilege_of_write_state
    {cur_privilege : Privilege}
    (pc : BitVec 32)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state = EStateM.Result.ok cur_privilege state)
  :
    Sail.readReg Register.cur_privilege (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok cur_privilege (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_cur_privilege
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_cur_privilege
    dsimp at ⊢ h_cur_privilege
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.cur_privilege =
      state.regs.get? Register.cur_privilege
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.cur_privilege
    . simp [h] at h_cur_privilege
    . simp [h] at ⊢ h_cur_privilege
      exact h_cur_privilege

  lemma mseccfg_of_write_state
    (pc : BitVec 32)
    (h_mseccfg : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state)
  :
    Sail.readReg Register.mseccfg (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4)) =
    EStateM.Result.ok mseccfg (write_reg_state state Register.nextPC (Sail.BitVec.addInt pc 4))
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_mseccfg
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get EStateM.instMonadStateOf EStateM.get at ⊢ h_mseccfg
    dsimp at ⊢ h_mseccfg
    have :
      (state.regs.insert Register.nextPC (Sail.BitVec.addInt pc 4)).get? Register.mseccfg =
      state.regs.get? Register.mseccfg
    := by grind
    simp [this]
    rcases h: state.regs.get? Register.mseccfg
    . simp [h] at h_mseccfg
    . simp [h] at ⊢ h_mseccfg
      exact h_mseccfg

  set_option maxHeartbeats 0 in
  lemma execute_JALR_pure_equiv
    (input : JalrInput)
    (imm: BitVec 12)
    (rs1 rd: regidx)
    (h_input_imm: input.imm = imm)
    (h_input_rd: input.rd = regidx_to_fin rd)
    (h_input_rs1: read_xreg (regidx_to_fin rs1) state = EStateM.Result.ok (input.rs1_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some input.misa)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.JALR (imm, rs1, rd))
    ) state =
    let output := execute_JALR_pure input
    (do
      match output.nextPC with
        | .some nextPC => Sail.writeReg Register.nextPC nextPC
        | .none => pure ()
      match output.rd with
        | .some (reg, rd_val) => write_xreg reg rd_val
        | .none => pure ()
      if !output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (0xFFFFFFFE &&& (input.rs1_val + BitVec.signExtend 32 input.imm))),
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
      LeanRV32D.Functions.execute_JALR
    ]
    replace h_cur_privilege := cur_privilege_of_write_state input.PC h_cur_privilege
    simp [
      LeanRV32D.Functions.update_elp_state,
      LeanRV32D.Functions.currentlyEnabled,
      h_cur_privilege,
      LeanRV32D.Functions.get_xLPE
    ]
    replace h_mseccfg := mseccfg_of_write_state input.PC h_mseccfg
    simp [
      h_mseccfg,
      LeanRV32D.Functions.hartSupports,
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
      PreSail.PreSailME.run,
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

    by_cases h_bit1 : BitVec.ofBool (input.rs1_val + BitVec.signExtend 32 imm)[1] = 0#1
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
    . replace h_bit1 := bit_eq_one_of_not_eq_zero _ h_bit1
      simp [
        h_bit1,
        execute_JALR_pure,
        h_input_imm
      ]
      by_cases h_misa: input.misa[2]
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
      . simp [
          h_misa,
          ExceptT.pure,
          ExceptT.mk
        ]

end PureSpec
