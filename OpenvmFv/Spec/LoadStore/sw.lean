import OpenvmFv.Spec.LoadStore.local_extended
import OpenvmFv.Spec.rX_bits

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

  def execute_STORE_pure (input : SwInput) : SwOutput := {
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

  open Local.RegisterInvariants

  def sw_state_assumptions
    (i : SwInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    -- Connecting the registers
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    -- Assumptions
    i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat < OpenVM_memory_address_space_size ∧
    LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (i.r1_val + (BitVec.signExtend 32 i.imm))) 4 = true

  set_option maxHeartbeats 0 in
  lemma execute_STORE_pure_equiv
    (input : SwInput)
    (h_assumptions : Local.Assumptions.general_memory_assumptions state)
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
    let output := execute_STORE_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_4 (← get) output)
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
    ⟩ := h_sw_assumptions

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

    have h_execute_store := Local.execute_STORE_simplified
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
    simp [EStateM.instMonadStateOf, EStateM.get, EStateM.set, modify_memory_4, execute_STORE_pure, Sail.BitVec.addInt]

end PureSpec
