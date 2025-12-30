import OpenvmFv.RV32D.Auxiliaries

namespace PureSpec

  structure SwInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    r2 : BitVec 5
    -- registers
    r1_val : BitVec 32
    r2_val : BitVec 32
    PC : BitVec 32

  structure SwOutput where
    -- registers
    nextPC : BitVec 32
    -- memory
    data0 : ℕ × BitVec 8
    data1 : ℕ × BitVec 8
    data2 : ℕ × BitVec 8
    data3 : ℕ × BitVec 8

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_STOREW_pure (input : SwInput) : SwOutput := {
    nextPC := input.PC + 4#32
    data0 := (
      (input.r1_val + BitVec.signExtend 32 input.imm).toNat,
      BitVec.extractLsb 7 0 input.r2_val
    )
    data1 := (
      (input.r1_val + BitVec.signExtend 32 input.imm).toNat + 1,
      BitVec.extractLsb 15 8 input.r2_val
    )
    data2 := (
      (input.r1_val + BitVec.signExtend 32 input.imm).toNat + 2,
      BitVec.extractLsb 23 16 input.r2_val
    )
    data3 := (
      (input.r1_val + BitVec.signExtend 32 input.imm).toNat + 3,
      BitVec.extractLsb 31 24 input.r2_val
    )
    : SwOutput
  }

  def modify_memory_4
    (s: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (output: SwOutput)
  := {
    regs := s.regs,
    choiceState := s.choiceState,
    tags := s.tags,
    cycleCount := s.cycleCount,
    sailOutput := s.sailOutput
    mem :=
      ((((s.mem.insert output.data0.1 output.data0.2
      ).insert output.data1.1 output.data1.2)
      ).insert output.data2.1 output.data2.2
      ).insert output.data3.1 output.data3.2
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  }

  def sw_state_assumptions
    (i : SwInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    -- Connecting the registers
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    -- Assumption : Memory address is not outside address space
    -- Note : This is an assumption for this proof, but is not an assumption in general because there is
    --        a static guarantee that all addresses on the memory bus must be less than 2 ^ 29
    i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat < OpenVM_address_space_size ∧
    -- Assumption A1 : Memory address alignment
    (4 : ℤ) ∣ i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat

  set_option maxHeartbeats 0 in
  lemma execute_STOREW_pure_equiv
    (input : SwInput)
    (h_assumptions : general_memory_assumptions state mstatus pmaRegion)
    (h_sw_assumptions : sw_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.STORE (
          input.imm,
          regidx.Regidx input.r2,
          regidx.Regidx input.r1,
          4
        ))
    ) state =
    let output := execute_STOREW_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_4 (← get) output)
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := gma_invariant_under_pc_increment h_assumptions (val := input.PC + 4#32)
    obtain ⟨
      h_pc,
      h_r1_val,
      h_r2_val,
      h_does_fit,
      h_aligned
    ⟩ := h_sw_assumptions

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      *
    ]

    replace h_r1_val := rX_bits_write_other_reg_state (r := input.r1) (val := input.PC + 4#32) h_r1_val reg_of_fin_neq_nextPC
    replace h_r2_val := rX_bits_write_other_reg_state (r := input.r2) (val := input.PC + 4#32) h_r2_val reg_of_fin_neq_nextPC

    have h_execute_store := execute_STOREW
      (write_reg_state state Register.nextPC (input.PC + 4#32))
      h_r1_val
      h_r2_val
      next_gma
      h_aligned
      h_does_fit

    simp [
      h_execute_store,
      execute_STOREW_pure,
      EStateM.set,
      modify_memory_4
    ]

end PureSpec
