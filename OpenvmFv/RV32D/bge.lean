import OpenvmFv.RV32D.Auxiliaries

namespace PureSpec

  structure BgeInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 32
    r2_val: BitVec 32
    -- registers
    PC : BitVec 32

  structure BgeOutput where
    -- registers
    nextPC : BitVec 32
    -- result
    success : Bool
    throws : Bool

  def execute_BGE_pure (input : BgeInput) : BgeOutput :=
    let skip := !(input.r1_val.toInt ≥b input.r2_val.toInt)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 32 input.imm)
      success := !fails
      throws := throws
      : BgeOutput
    }

  lemma execute_BGE_pure_succ_throws
    (input : BgeInput)
  :
    let output := execute_BGE_pure input
    output.success = true → output.throws = false
  := by
    simp [execute_BGE_pure]
    grind

  @[simp]
  lemma sign_extend_equiv :
    @LeanRV32D.Functions.sign_extend width1 width2 =
    @BitVec.signExtend width1 width2
  := rfl

  lemma execute_BGE_pure_equiv
    (bge_input : BgeInput)
    (imm: BitVec 13)
    (h_input_imm: bge_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bge_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bge_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some bge_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BGE ))
    ) state =
    let bge_output := execute_BGE_pure bge_input
    (do
      Sail.writeReg Register.nextPC bge_output.nextPC
      if bge_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !bge_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bge_input.PC + BitVec.signExtend 32 bge_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := by
    simp [
      readReg_succ h_input_pc,
      LeanRV32D.Functions.execute,
      writeReg_state_success,
      LeanRV32D.Functions.execute_BTYPE
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by { simp [regidx_to_fin] })]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by { simp [regidx_to_fin] })]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp

    by_cases h_eq: bge_input.r2_val.toInt ≤ bge_input.r1_val.toInt <;>
    simp [h_eq, execute_BGE_pure]
    rewrite [(readReg_succ (writeReg_read_diff h_input_pc (by trivial)))]
    simp
    rewrite [writeReg_read_diff h_input_misa (by trivial)]
    simp

    by_cases h_throws : (execute_BGE_pure bge_input).throws <;>
    simp_all [execute_BGE_pure]
    . by_cases h_success : (execute_BGE_pure bge_input).success
      . simp [execute_BGE_pure, h_eq, h_throws, h_input_imm] at h_success
        repeat rw [if_neg (by omega)]
        simp
      . simp [execute_BGE_pure, h_eq, h_throws, h_input_imm] at h_success
        repeat rw [if_pos (by omega)]
        simp

end PureSpec
