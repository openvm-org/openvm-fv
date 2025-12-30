import OpenvmFv.RV32D.Auxiliaries
import OpenvmFv.Fundamentals.Execution

namespace PureSpec

  structure OriInput where
    -- operands
    r1_val : BitVec 32
    imm : BitVec 12
    rd : Fin 32
    -- registers
    PC : BitVec 32

  structure OriOutput where
    -- registers
    nextPC : BitVec 32
    rd : Option (Finset.Icc 1 31 × BitVec 32)

  def execute_ITYPE_ori_pure (input : OriInput) : OriOutput := {
    nextPC := input.PC + 4#32
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        input.r1_val ||| BitVec.signExtend 32 input.imm
      )
    : OriOutput
  }

  lemma execute_ITYPE_ori_pure_equiv
    (ori_input : OriInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (ori_input.r1_val) state)
    (h_input_imm: ori_input.imm = imm)
    (h_input_rd: ori_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some ori_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.ORI))
    ) state =
    let ori_output := execute_ITYPE_ori_pure ori_input
    (do
      Sail.writeReg Register.nextPC ori_output.nextPC
      match ori_output.rd with
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
      execute_ITYPE_ori_pure
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
      . simp_all [regidx_to_fin]
      . simp [regidx_to_fin] at *
        omega

end PureSpec
