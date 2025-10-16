import OpenvmFv.Spec.run_hart_active
import OpenvmFv.Spec.ControlFlow.local

namespace PureSpec

  structure AuipcInput where
    -- operands
    imm : BitVec 20
    rd: Fin 32
    -- registers
    PC : BitVec 32

  structure AuipcOutput where
    -- registers
    nextPC : BitVec 32
    rd : Option (Finset.Icc 1 31 × BitVec 32)

  def execute_AUIPC_pure (input : AuipcInput) : AuipcOutput :=
    {
      nextPC := (input.PC + 4)
      rd := if h: input.rd = 0
        then .none
        else (.some (⟨input.rd, by {
          apply Finset.mem_Icc.mpr
          omega
        }⟩, input.PC + (input.imm ++ 0#12)))
      : AuipcOutput
    }

  lemma execute_AUIPC_pure_equiv
    (auipc_input : AuipcInput)
    (imm: BitVec 21)
    (rd: regidx)
    (h_input_imm: auipc_input.imm = imm)
    (h_input_rd: auipc_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some auipc_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.UTYPE (imm, rd, .AUIPC))
    ) state =
    let auipc_output := execute_AUIPC_pure auipc_input
    (do
      Sail.writeReg Register.nextPC auipc_output.nextPC
      match auipc_output.rd with
        | .some (reg, rd_val) => write_xreg reg rd_val
        | .none => pure ()
      (pure (ExecutionResult.Retire_Success ()))) state
  := by
    -- unfold to functional structure
    unfold bind Monad.toBind EStateM.instMonad
    dsimp
    unfold EStateM.bind EStateM.pure
    dsimp


    simp [←h_input_imm]; clear h_input_imm

    simp [
      readReg_state h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      ←Local.execute_UTYPE_equiv
    ]

    have (x : BitVec 32) : Sail.BitVec.addInt x 4 = x + 4 := rfl
    simp [this]

    unfold Local.execute_UTYPE

    unfold bind Monad.toBind EStateM.instMonad
    dsimp
    unfold EStateM.bind EStateM.pure
    dsimp

    simp [LeanRV32D.Functions.get_arch_pc]

    rewrite [readReg_state (writeReg_read_diff h_input_pc (by trivial))]
    dsimp
    rewrite [
      Local.sign_extend_equiv,
    ]

    obtain ⟨rd⟩ := rd
    by_cases h_zero: rd = 0
    . rewrite [h_zero, wX_write_xreg_0_equiv]
      simp [execute_AUIPC_pure, h_input_rd, h_zero, regidx_to_fin]
    . have h_inc := regidx_non_zero h_zero
      apply Finset.mem_Icc.mp at h_inc
      obtain ⟨h_low, h_high⟩ := h_inc
      rewrite [
        wX_write_xreg_equiv _ _
          (regidx.Regidx rd)
          ⟨(regidx_to_fin (regidx.Regidx rd)).val, Finset.mem_Icc.mpr ⟨h_low, h_high⟩⟩
          (by simp [regidx_to_fin])
      ]
      simp [
        regidx_to_fin,
        execute_AUIPC_pure,
      ]
      rewrite [dite_cond_eq_false]
      . simp [h_input_rd, regidx_to_fin]
      . simp [regidx_to_fin] at *
        omega

end PureSpec
