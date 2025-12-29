import OpenvmFv.RV32D.Auxiliaries
import OpenvmFv.Fundamentals.Execution

namespace PureSpec

  structure SltiInput where
    -- operands
    r1_val : BitVec 32
    imm : BitVec 12
    rd : Fin 32
    -- registers
    PC : BitVec 32

  structure SltiOutput where
    -- registers
    nextPC : BitVec 32
    rd : Option (Finset.Icc 1 31 × BitVec 32)

  def execute_ITYPE_slti_pure (input : SltiInput) : SltiOutput := {
    nextPC := input.PC + 4#32
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        if input.r1_val.slt (BitVec.signExtend 32 input.imm)
        then 1#32
        else 0#32
      )
    : SltiOutput
  }

  lemma execute_ITYPE_slti_pure_equiv
    (slti_input : SltiInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (slti_input.r1_val) state)
    (h_input_imm: slti_input.imm = imm)
    (h_input_rd: slti_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some slti_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.SLTI))
    ) state =
    let slti_output := execute_ITYPE_slti_pure slti_input
    (do
      Sail.writeReg Register.nextPC slti_output.nextPC
      match slti_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      execute_ITYPE'
    ]

    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp [
      execute_ITYPE_pure,
      execute_RTYPE_pure,
      execute_ITYPE_slti_pure
    ]

    obtain ⟨rd⟩ := rd
    by_cases h_zero: rd = 0
    . rewrite [h_zero, wX_write_xreg_zero_equiv]
      simp
      rewrite [dite_cond_eq_true]
      . simp
      . simp [h_input_rd, h_zero, regidx_to_fin]
    . have h_inc := regidx_non_zero h_zero
      apply Finset.mem_Icc.mp at h_inc
      obtain ⟨h_low, h_high⟩ := h_inc
      rewrite [
        wX_write_xreg_non_zero_equiv _ _
          (regidx.Regidx rd)
          ⟨(regidx_to_fin (regidx.Regidx rd)).val, Finset.mem_Icc.mpr ⟨h_low, h_high⟩⟩
          (by simp [regidx_to_fin])
      ]
      simp [regidx_to_fin]
      rewrite [dite_cond_eq_false]
      . simp [h_input_rd, regidx_to_fin]
        by_cases h_lt: slti_input.r1_val.toInt < (BitVec.signExtend 32 slti_input.imm).toInt
        . simp_all [BitVec.slt]
        . simp [h_lt, BitVec.slt]
          have : (slti_input.r1_val.toInt < (BitVec.signExtend 32 imm).toInt) = false := by simp_all
          simp [this]
      . simp [regidx_to_fin] at *
        omega

end PureSpec
