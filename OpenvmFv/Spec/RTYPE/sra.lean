import OpenvmFv.Spec.RTYPE.local
import OpenvmFv.Spec.rX_bits

namespace PureSpec

  structure SraInput where
    -- operands
    r1_val : BitVec 32
    r2_val : BitVec 32
    rd : Fin 32
    -- registers
    PC : BitVec 32

  structure SraOutput where
    -- registers
    nextPC : BitVec 32
    rd : Option (Finset.Icc 1 31 × BitVec 32)

  def execute_RTYPE_sra_pure (input : SraInput) : SraOutput := {
    nextPC := input.PC + 4#32
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        input.r1_val.sshiftRight (input.r2_val.toNat % 32)
      )
    : SraOutput
  }

  lemma execute_RTYPE_sra_pure_equiv
    (sra_input : SraInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (sra_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (sra_input.r2_val) state)
    (h_input_rd: sra_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some sra_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.RTYPE (r2, r1, rd, rop.SRA))
    ) state =
    let sra_output := execute_RTYPE_sra_pure sra_input
    (do
      Sail.writeReg Register.nextPC sra_output.nextPC
      match sra_output.rd with
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
      Local.execute.eq_def,
      -write_xreg_eq_write_xreg'
    ]

    have (x : BitVec 32) : Sail.BitVec.addInt x 4 = x + 4 := rfl
    simp [this, -write_xreg_eq_write_xreg']

    simp [
      ←Local.execute_RTYPE_equiv,
      Local.execute_RTYPE.eq_def,
      bind, EStateM.instMonad, EStateM.bind,
      -write_xreg_eq_write_xreg'
    ]

    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_reg_state_nextPC _ h_input_r1]
    simp [-write_xreg_eq_write_xreg']
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_reg_state_nextPC _ h_input_r2]
    simp [EStateM.pure, -write_xreg_eq_write_xreg']

    simp [execute_RTYPE_sra_pure, -write_xreg_eq_write_xreg']

    obtain ⟨rd⟩ := rd
    by_cases h_zero: rd = 0
    . rewrite [h_zero, wX_write_xreg_0_equiv]
      simp [-write_xreg_eq_write_xreg']
      rewrite [dite_cond_eq_true]
      . simp [-write_xreg_eq_write_xreg']
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
      simp [regidx_to_fin, -write_xreg_eq_write_xreg']
      rewrite [dite_cond_eq_false]
      . simp [h_input_rd, regidx_to_fin, -write_xreg_eq_write_xreg']
        simp [
          LeanRV32D.Functions.shift_bits_right_arith, Sail.BitVec.extractLsb, log2_xlen,
          LeanRV32D.Functions.shift_right_arith, LeanRV32D.Functions.sign_extend, Sail.BitVec.signExtend,
          -write_xreg_eq_write_xreg'
        ]
        congr
        grind
      . simp [regidx_to_fin] at *
        omega

end PureSpec
