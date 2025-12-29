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
    -- Assumptions
    LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (i.r1_val + (BitVec.signExtend 32 i.imm))) 1 = true

  set_option maxHeartbeats 0 in
  lemma execute_STOREB_pure_equiv
    (input : SbInput)
    (h_assumptions : general_memory_assumptions state (input.r1_val.toNat + (BitVec.signExtend 32 input.imm).toNat) 1)
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
      h_aligned
    ⟩ := h_sb_assumptions

    simp [
      Sail.readReg,
      PreSail.readReg,
      h_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute
    ]

    replace h_r1_val := rX_bits_write_other_reg_state (r := input.r1) (val := input.PC + 4#32) h_r1_val reg_of_fin_neq_nextPC
    replace h_r2_val := rX_bits_write_other_reg_state (r := input.r2) (val := input.PC + 4#32) h_r2_val reg_of_fin_neq_nextPC
    replace h_mstatus := readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := input.PC + 4#32) h_mstatus (by trivial)
    replace h_cur_privilege := readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := input.PC + 4#32) h_cur_privilege (by trivial)
    replace h_pma_regions := readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := input.PC + 4#32) h_pma_regions (by trivial)
    replace h_htif_tohost_base := readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := input.PC + 4#32) h_htif_tohost_base (by trivial)

    have h_execute_store := execute_STOREB
      (write_reg_state state Register.nextPC (input.PC + 4#32))
      h_r1_val
      h_r2_val
      h_mstatus
      h_cur_privilege
      h_htif_tohost_base
      h_aligned
      (by simp)
      h_plat_mstatus_val
      h_pma_regions
      h_pma_region_base_val
      h_pma_region_size_ub
      (by grind)
      (by grind)

    simp [
      h_execute_store,
      execute_STOREB_pure,
      EStateM.set,
      modify_memory_1
    ]

end PureSpec
