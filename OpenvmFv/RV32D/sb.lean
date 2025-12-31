import OpenvmFv.RV32D.Auxiliaries

namespace PureSpec

  structure SbInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    r2 : BitVec 5
    -- registers
    r1_val : BitVec 32
    r2_val : BitVec 32
    PC : BitVec 32

  structure SbOutput where
    -- registers
    nextPC : BitVec 32
    -- memory
    data0 : ℕ × BitVec 8

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_STOREB_pure (input : SbInput) : SbOutput := {
    nextPC := input.PC + 4#32
    data0 := (
      (input.r1_val + BitVec.signExtend 32 input.imm).toNat,
      BitVec.extractLsb 7 0 input.r2_val
    )
    : SbOutput
  }

  def modify_memory_1
    (s: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_output: SbOutput)
  := {
    regs := s.regs,
    choiceState := s.choiceState,
    tags := s.tags,
    cycleCount := s.cycleCount,
    sailOutput := s.sailOutput
    mem :=
      s.mem.insert sb_output.data0.1 sb_output.data0.2
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  }

  def sb_state_assumptions
    (i : SbInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    -- Connecting the registers
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    -- Assumption : Memory address is not outside address space
    -- Note : This is an assumption for this proof, but is not an assumption in general because there is
    --        a static guarantee that all addresses on the memory bus must be less than 2 ^ 29
    i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat < OpenVM_address_space_size

  set_option maxHeartbeats 0 in
  lemma execute_STOREB_pure_equiv
    (input : SbInput)
    (h_general_assumptions : general_memory_assumptions state mstatus pmaRegion)
    (h_opcode_assumptions : sb_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.STORE (
          input.imm,
          regidx.Regidx input.r2,
          regidx.Regidx input.r1,
          1
        ))
    ) state =
    let output := execute_STOREB_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_1 (← get) output)
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := gma_invariant_under_pc_increment h_general_assumptions (val := input.PC + 4#32)
    unfold sb_state_assumptions at h_opcode_assumptions

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      *
    ]

    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#32) h_opcode_assumptions.2.1 reg_of_fin_neq_nextPC
    have h_r2_val := rX_bits_write_other_reg_state (val := input.PC + 4#32) h_opcode_assumptions.2.2.1 reg_of_fin_neq_nextPC

    obtain ⟨ h_htif, h_priv, h_mprv , h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned ⟩ := next_gma
    have := arithmetic_helper (a := input.r1_val.toNat) (b := (BitVec.signExtend 32 input.imm).toNat) (by grind)

    simp [LeanRV32D.Functions.execute_STORE, LeanRV32D.Functions.vmem_write, EStateM.map, *]
    simp [LeanRV32D.Functions.vmem_write_addr, ExceptT.run, *]
    rw [if_pos (by omega)]; simp [*]
    rw [if_neg (by omega)]

    simp [execute_STOREB_pure, EStateM.set, modify_memory_1, *]
    congr 1; simp [← BitVec.toNat_inj]

end PureSpec
