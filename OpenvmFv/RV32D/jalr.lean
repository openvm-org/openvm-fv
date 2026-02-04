import OpenvmFv.RV32D.Auxiliaries

namespace PureSpec

  structure JalrInput where
    -- operands
    imm : BitVec 12
    rs1_val: BitVec 32
    rd: Fin 32
    -- registers
    PC : BitVec 32

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
        if (!bit1_valid)
        then (.some (input.PC + 4))
        else (.some (mask &&& (input.rs1_val + BitVec.signExtend 32 input.imm)))
      rd := if h: (!bit1_valid) || input.rd = 0
      then .none
      else (
        .some (⟨input.rd, by {
          simp at h
          apply Finset.mem_Icc.mpr
          omega
        }⟩, input.PC + 4))
      success := (bit1_valid)
    }

  set_option maxHeartbeats 0 in
  lemma execute_JALR_pure_equiv
    (input : JalrInput)
    (imm: BitVec 12)
    (rs1 rd: regidx)
    (h_input_imm: input.imm = imm)
    (h_input_rd: input.rd = regidx_to_fin rd)
    (h_input_rs1: read_xreg (regidx_to_fin rs1) state = EStateM.Result.ok (input.rs1_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa)
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
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      LeanRV32D.Functions.execute_JALR
    ]
    replace h_cur_privilege := readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := input.PC + 4#32) h_cur_privilege (by trivial)
    simp [
      LeanRV32D.Functions.update_elp_state,
      LeanRV32D.Functions.currentlyEnabled,
      h_cur_privilege,
      LeanRV32D.Functions.get_xLPE
    ]
    replace h_mseccfg := readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := input.PC + 4#32) h_mseccfg (by trivial)
    simp [
      h_mseccfg,
      readReg_succ (writeReg_read_same _)
    ]
    obtain ⟨⟨rs1: Fin 32⟩⟩ := rs1
    rewrite [rX_read_xreg_equiv _ ⟨⟨rs1⟩⟩ rs1 (by simp)]
    simp [regidx_to_fin] at h_input_rs1
    simp [
      read_xreg_write_other_reg_state (register := Register.nextPC) (write_val := input.PC + 4#32) rs1 h_input_rs1 reg_of_fin_neq_nextPC,
      Sail.BitVec.update,
      writeReg_read_diff h_input_misa (show Register.misa ≠ Register.nextPC by grind),
      execute_JALR_pure
    ]
    by_cases h_bit1 : BitVec.ofBool (input.rs1_val + BitVec.signExtend 32 imm)[1] = 1#1 <;> simp [h_bit1]
    . split <;> simp_all
    . have h_bit1' : BitVec.ofBool (input.rs1_val + BitVec.signExtend 32 imm)[1] = 0#1 := by grind
      by_cases h_rd_0 : regidx_to_fin rd = 0 <;> simp_all
      . replace h_rd_0 : rd.1.toNat = 0
        := by
          simp [regidx_to_fin] at h_rd_0
          rcases rd with ⟨ rd, h_rd ⟩
          simp_all
        simp [
          LeanRV32D.Functions.wX_bits,
          LeanRV32D.Functions.wX,
          h_rd_0
        ]
      . rcases rd with ⟨ rd, h_rd ⟩
        simp [regidx_to_fin, Fin.ext_iff] at h_rd_0
        simp at h_rd
        simp [
          write_xreg,
          Sail.writeReg,
          PreSail.writeReg,
          LeanRV32D.Functions.wX_bits,
          LeanRV32D.Functions.wX,
          reg_of_fin
        ]
        interval_cases rd <;> simp
        . omega
        all_goals
          congr

end PureSpec
