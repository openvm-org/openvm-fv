import OpenvmFv.RV32D.Auxiliaries

namespace PureSpec

  structure JalInput where
    -- operands
    imm : BitVec 21
    rd: Fin 32
    -- registers
    PC : BitVec 32

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
        if !bit0_valid || !bit1_valid
        then (.some (input.PC + 4))
        else (.some (input.PC + BitVec.signExtend 32 input.imm))
      rd := if h: !bit0_valid || !bit1_valid || input.rd = 0
      then .none
      else (
        .some (⟨input.rd, by {
          simp at h
          apply Finset.mem_Icc.mpr
          omega
        }⟩, input.PC + 4))
      success := bit0_valid && bit1_valid
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
    (h_input_misa: state.regs.get? Register.misa = .some misa)
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
      readReg_succ h_input_pc,
      writeReg_state_success,
      rv32d_execute_jal,
      LeanRV32D.Functions.execute_JAL,
      LeanRV32D.Functions.get_next_pc,
      readReg_succ (writeReg_read_same _),
      readReg_succ (writeReg_read_diff h_input_pc (show Register.PC ≠ Register.nextPC by grind)),
      LeanRV32D.Functions.jump_to
    ]

    by_cases h_bit0 : BitVec.ofBool (jal_input.PC + BitVec.signExtend 32 imm)[0] = 0#1
    . simp [
        h_bit0,
        readReg_succ (writeReg_read_diff h_input_misa (show Register.misa ≠ Register.nextPC by grind)),
      ]
      by_cases h_bit1 : BitVec.ofBool (jal_input.PC + BitVec.signExtend 32 imm)[1] = 1#1
      . simp [h_bit1]
        simp [
          execute_JAL_pure,
          h_input_imm,
          h_bit0,
          h_bit1
        ]
      . have h_bit1' : BitVec.ofBool (jal_input.PC + BitVec.signExtend 32 imm)[1] = 0#1 := by grind
        rw [if_neg (by grind)]
        simp [
          writeReg_write_same,
          execute_JAL_pure
        ]
        rw [if_neg (by grind)]
        simp
        rw [if_pos (by grind)]
        rw [if_neg (by grind)]
        simp [
          h_input_imm,
          h_bit0,
          h_bit1'
        ]
        by_cases h_rd_0 : jal_input.rd = 0 <;> simp [h_rd_0]
        . replace h_rd_0 : rd.1.toNat = 0
          := by
            simp [regidx_to_fin, h_rd_0] at h_input_rd
            rcases rd with ⟨ rd, h_rd ⟩
            simp_all
          simp [
            LeanRV32D.Functions.wX_bits,
            LeanRV32D.Functions.wX,
            h_rd_0
          ]
        . rcases rd with ⟨ rd, h_rd ⟩
          simp [regidx_to_fin] at h_input_rd
          simp [h_input_rd, Fin.ext_iff] at h_rd_0
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
            congr <;> simp_all
    . simp_all [execute_JAL_pure]

end PureSpec
