import OpenvmFv.Spec.run_hart_active
import OpenvmFv.Spec.ControlFlow.local
import OpenvmFv.Spec.ControlFlow.jump_to

structure BneInput where
  -- operands
  imm : BitVec 13
  r1_val: BitVec 32
  r2_val: BitVec 32
  -- registers
  PC : BitVec 32
  misa : BitVec 32

structure BneOutput where
  -- registers
  nextPC : BitVec 32
  -- result
  success : Bool
  throws : Bool

def target_bit_0_invalid (input : BneInput) : Bool :=
  BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0]! == 1#1

def target_bit_1_invalid (input: BneInput): Bool :=
  BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1]! == 1#1 && !input.misa[2]

def execute_BNE_pure (input : BneInput) : BneOutput :=
  let skip := input.r2_val == input.r1_val
  let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[0] == 1#1
  let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 32 input.imm)[1] == 1#1 && !input.misa[2])
  {
    nextPC := if skip || fails
      then (input.PC + 4)
      else (input.PC + BitVec.signExtend 32 input.imm)
    success := !fails
    throws := throws
    : BneOutput
  }

@[simp]
lemma sign_extend_equiv :
  @LeanRV32D.Functions.sign_extend width1 width2 =
  @BitVec.signExtend width1 width2
:= rfl

lemma execute_BNE_pure_equiv
  (bne_input : BneInput)
  (imm: BitVec 13)
  (h_input_imm: bne_input.imm = imm)
  (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bne_input.r1_val) state)
  (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bne_input.r2_val) state)
  (h_input_pc: state.regs.get? Register.PC = .some bne_input.PC)
  (h_input_misa: state.regs.get? Register.misa = .some bne_input.misa)
:
  (
    do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV32D.Functions.execute (instruction.BTYPE (imm, r1, r2, bop.BNE ))
  ) state =
  let bne_output := execute_BNE_pure bne_input
  (do
    Sail.writeReg Register.nextPC bne_output.nextPC
    if bne_output.throws then
      throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
    else if !bne_output.success then
      pure (
        ExecutionResult.Memory_Exception (
          (virtaddr.Virtaddr (bne_input.PC + BitVec.signExtend 32 bne_input.imm)),
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
  rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by { simp [regidx_to_fin] })]
  simp [read_xreg_write_reg_state_nextPC _ h_input_r2]
  rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by { simp [regidx_to_fin] })]
  simp [read_xreg_write_reg_state_nextPC _ h_input_r1]
  by_cases h_eq: bne_input.r2_val = bne_input.r1_val
  . simp [h_eq, execute_BNE_pure]
  . simp [h_eq]
    rewrite [readReg_state (writeReg_read_diff h_input_pc (by trivial))]
    simp [←Local.jump_to_equiv, jump_to_simplified_equiv, jump_to_simplified]
    rewrite [writeReg_read_diff h_input_misa (by trivial)]
    simp

    by_cases h_throws : (execute_BNE_pure bne_input).throws <;>
    simp [execute_BNE_pure, h_eq, h_input_imm] at h_throws <;>
    simp [h_throws, execute_BNE_pure, h_eq, h_input_imm]
    . by_cases h_success : (execute_BNE_pure bne_input).success
      . simp [execute_BNE_pure, h_eq, h_throws, h_input_imm] at h_success
        iterate 3 rw [ite_cond_eq_false (h := by grind)]
        grind [writeReg_write_same]
      . simp [execute_BNE_pure, h_eq, h_throws, h_input_imm] at h_success
        iterate 3 rw [ite_cond_eq_true (h := by grind)]
