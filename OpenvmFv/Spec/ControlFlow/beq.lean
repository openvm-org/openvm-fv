import OpenvmFv.Spec.run_hart_active
import OpenvmFv.Spec.ControlFlow.local
import OpenvmFv.Spec.ControlFlow.jump_to

namespace PureSpec

  structure BeqInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 32
    r2_val: BitVec 32
    -- registers
    PC : BitVec 32
    misa : BitVec 32

  structure BeqOutput where
    -- registers
    nextPC : BitVec 32
    -- result
    success : Bool
    throws : Bool

  def execute_BEQ_pure (input : BeqInput) : BeqOutput :=
    let skip := !(input.r1_val == input.r2_val)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1] == 1#1 && !input.misa[2])
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 32 input.imm)
      success := !fails
      throws := throws
      : BeqOutput
    }

  lemma execute_BEQ_pure_succ_throws
    (input : BeqInput)
  :
    let output := execute_BEQ_pure input
    output.success = true → output.throws = false
  := by
    simp [execute_BEQ_pure]
    grind

  @[simp]
  lemma sign_extend_equiv :
    @LeanRV32D.Functions.sign_extend width1 width2 =
    @BitVec.signExtend width1 width2
  := rfl

  lemma execute_BEQ_pure_equiv
    (beq_input : BeqInput)
    (imm: BitVec 13)
    (h_input_imm: beq_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (beq_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (beq_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some beq_input.misa)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BEQ ))
    ) state =
    let beq_output := execute_BEQ_pure beq_input
    (do
      Sail.writeReg Register.nextPC beq_output.nextPC
      if beq_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !beq_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (beq_input.PC + BitVec.signExtend 32 beq_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := by
    have (x : BitVec 32) : Sail.BitVec.addInt x 4 = x + 4 := rfl
    simp [
      this,
      readReg_state h_input_pc,
      writeReg_state_success,
      ←Local.execute_equiv,
      ←Local.execute_BTYPE_equiv
    ]

    simp [Local.execute_BTYPE]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by {
      simp [regidx_to_fin]
    })]
    rewrite [read_xreg_write_reg_state_nextPC _ h_input_r1]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by {
      simp [regidx_to_fin]
    })]
    rewrite [read_xreg_write_reg_state_nextPC _ h_input_r2]
    simp
    by_cases h_eq: beq_input.r1_val = beq_input.r2_val
    . simp [h_eq]
      rewrite [readReg_state (writeReg_read_diff h_input_pc (by trivial))]
      simp [←Local.jump_to_equiv, jump_to_simplified_equiv, jump_to_simplified]
      rewrite [writeReg_read_diff h_input_misa (by trivial)]
      simp

      by_cases h_throws : (execute_BEQ_pure beq_input).throws
      . simp [execute_BEQ_pure, h_eq, h_input_imm] at h_throws
        simp [h_throws, execute_BEQ_pure, h_eq, h_input_imm]
      . simp [execute_BEQ_pure, h_eq, h_input_imm] at h_throws
        simp [h_throws, execute_BEQ_pure, h_eq, h_input_imm]
        by_cases h_success : (execute_BEQ_pure beq_input).success
        . simp [execute_BEQ_pure, h_eq, h_throws, h_input_imm] at h_success
          rw [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false]
          . simp [writeReg_write_same]
          all_goals cases h_success <;> simp [*]
        . simp [execute_BEQ_pure, h_eq, h_throws, h_input_imm] at h_success
          rw [ite_cond_eq_true, ite_cond_eq_true, ite_cond_eq_true]
          all_goals simp [h_success]
    . simp [
        h_eq,
        execute_BEQ_pure
      ]

end PureSpec
