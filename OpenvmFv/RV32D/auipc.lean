import OpenvmFv.RV32D.Auxiliaries

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

  set_option maxHeartbeats 0 in
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
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      execute_AUIPC_pure,
      LeanRV32D.Functions.execute_UTYPE,
      LeanRV32D.Functions.get_arch_pc
    ]
    rewrite [readReg_succ (writeReg_read_diff h_input_pc (by trivial))]
    simp
    by_cases h_rd_0 : auipc_input.rd = 0 <;> simp [h_rd_0]
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

end PureSpec
