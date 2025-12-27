import OpenvmFv.Spec.LoadStore.local_extended
import OpenvmFv.Spec.rX_bits

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

  open Local.RegisterInvariants

  def sb_state_assumptions
    (i : SbInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    -- Connecting the registers
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    -- Assumptions
    i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat < OpenVM_memory_address_space_size ∧
    LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (i.r1_val + (BitVec.signExtend 32 i.imm))) 1 = true

  set_option maxHeartbeats 0 in
  lemma execute_STOREB_pure_equiv
    (input : SbInput)
    (h_assumptions : Local.Assumptions.general_memory_assumptions state)
    (h_sb_assumptions : sb_state_assumptions input state)
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
    obtain ⟨
      h_htif_tohost_base,
      h_cur_privilege,
      ⟨ mstatus, ⟨ h_mstatus, h_plat_mstatus_val⟩ ⟩,
      pmaRegion,
      h_pma_regions,
      h_pma_region_base_val,
      h_pma_region_size_ub,
      h_pma_region_size_readable,
      h_pma_region_size_writable,
      h_pma_region_size_misaligned
    ⟩ := h_assumptions
    obtain ⟨
      h_pc,
      h_r1_val,
      h_r2_val,
      h_does_fit,
      h_aligned
    ⟩ := h_sb_assumptions

    simp [
      readReg_state h_pc,
      writeReg_state_success,
    ]

    replace h_r1_val := r1_of_write_state input.PC h_r1_val
    replace h_r2_val := r1_of_write_state input.PC h_r2_val
    replace h_mstatus := mstatus_of_write_state input.PC h_mstatus
    replace h_cur_privilege := cur_privilege_of_write_state input.PC h_cur_privilege
    replace h_pma_regions := pma_regions_of_write_state input.PC h_pma_regions
    replace h_htif_tohost_base := htif_tohost_base_of_write_state input.PC h_htif_tohost_base

    have h_execute_store := Local.execute_STOREB_simplified
      (write_reg_state state Register.nextPC (Sail.BitVec.addInt input.PC 4))
      h_r1_val
      h_r2_val
      h_mstatus
      h_cur_privilege
      h_htif_tohost_base
      h_does_fit
      h_aligned
      (by simp)
      h_plat_mstatus_val
      h_pma_regions
      h_pma_region_base_val
      h_pma_region_size_ub
      (by grind)

    rewrite [
      Local.execute_store_instruction
    ]
    simp only [Int.toNat]
    rewrite [
      h_execute_store
    ]

    unfold write_reg_state
    unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get
    simp [EStateM.instMonadStateOf, EStateM.get, EStateM.set, modify_memory_1, execute_STOREB_pure, Sail.BitVec.addInt]

end PureSpec
