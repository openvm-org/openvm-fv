import OpenvmFv.Spec.RTYPE.local
import OpenvmFv.Spec.rX_bits

structure SltInput where
  -- operands
  r1_val : BitVec 32
  r2_val : BitVec 32
  rd : Fin 32
  -- registers
  PC : BitVec 32

structure SltOutput where
  -- registers
  nextPC : BitVec 32
  rd : Option (Finset.Icc 1 31 × BitVec 32)

def execute_RTYPE_slt_pure (input : SltInput) : SltOutput := {
  nextPC := input.PC + 4#32
  rd := if h: input.rd = 0
    then .none
    else .some (
      ⟨
        input.rd.val,
        by apply Finset.mem_Icc.mpr; omega
      ⟩,
      if input.r2_val.slt input.r1_val
      then 1#32
      else 0#32
    )
  : SltOutput
}

lemma execute_RTYPE_slt_pure_equiv
  (slt_input : SltInput)
  (r1 r2 rd: regidx)
  (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (slt_input.r1_val) state)
  (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (slt_input.r2_val) state)
  (h_input_rd: slt_input.rd = regidx_to_fin rd)
  (h_input_pc: state.regs.get? Register.PC = .some slt_input.PC)
:
  (
    do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV32D.Functions.execute (instruction.RTYPE (r1, r2, rd, rop.SLT))
  ) state =
  let slt_output := execute_RTYPE_slt_pure slt_input
  (do
    Sail.writeReg Register.nextPC slt_output.nextPC
    match slt_output.rd with
      | .some (rd, rd_val) => write_xreg rd rd_val
      | .none => pure ()
    pure (ExecutionResult.Retire_Success ())
  ) state
:= by
  unfold bind Monad.toBind EStateM.instMonad
  dsimp
  unfold EStateM.bind
  dsimp

  simp [
    readReg_state h_input_pc,
    writeReg_state_success,
    ←Local.execute_equiv,
    Local.execute.eq_def
  ]

  have (x : BitVec 32) : Sail.BitVec.addInt x 4 = x + 4 := rfl
  simp [this]

  simp [
    ←Local.execute_RTYPE_equiv,
    Local.execute_RTYPE.eq_def,
    bind, EStateM.instMonad, EStateM.bind
  ]

  rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
  rewrite [read_xreg_write_reg_state_nextPC _ h_input_r2]
  simp
  rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
  rewrite [read_xreg_write_reg_state_nextPC _ h_input_r1]
  simp [EStateM.pure]

  simp [execute_RTYPE_slt_pure]

  obtain ⟨rd⟩ := rd
  by_cases h_zero: rd = 0
  . rewrite [h_zero, wX_write_xreg_0_equiv]
    simp
    rewrite [dite_cond_eq_true]
    . simp
    . simp [h_input_rd, h_zero, regidx_to_fin]
  . have h_inc := regidx_non_zero h_zero
    apply Finset.mem_Icc.mp at h_inc
    obtain ⟨h_low, h_high⟩ := h_inc
    rewrite [
      wX_write_xreg_equiv _ _
        (regidx.Regidx rd)
        ⟨(regidx_to_fin (regidx.Regidx rd)).val, Finset.mem_Icc.mpr ⟨h_low, h_high⟩⟩
        (by simp [regidx_to_fin])
    ]
    simp [regidx_to_fin]
    rewrite [dite_cond_eq_false]
    . simp [h_input_rd, regidx_to_fin]
      simp [
        LeanRV32D.Functions.zopz0zI_s,
        LeanRV32D.Functions.bool_to_bits, LeanRV32D.Functions.bool_bits_forwards
      ]
      by_cases h_lt: slt_input.r2_val.slt slt_input.r1_val
      . simp [h_lt]
        have : slt_input.r2_val.toInt<bslt_input.r1_val.toInt := h_lt
        simp [this, LeanRV32D.Functions.zero_extend, Sail.BitVec.zeroExtend]
      . simp [h_lt]
        have : ¬(slt_input.r2_val.toInt<bslt_input.r1_val.toInt) := h_lt
        simp [this, LeanRV32D.Functions.zero_extend, Sail.BitVec.zeroExtend]
    . simp [regidx_to_fin] at *
      omega
