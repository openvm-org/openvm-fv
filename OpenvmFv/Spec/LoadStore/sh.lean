import OpenvmFv.Spec.LoadStore.local_extended
import OpenvmFv.Spec.rX_bits

namespace PureSpec

  structure ShInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    r2 : BitVec 5
    -- registers
    r1_val : BitVec 32
    r2_val : BitVec 32
    PC : BitVec 32

  structure ShOutput where
    -- registers
    nextPC : BitVec 32
    -- memory
    data0 : ℕ × BitVec 8
    data1 : ℕ × BitVec 8

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_STOREH_pure (input : ShInput) : ShOutput := {
    nextPC := input.PC + 4#32
    data0 := (
      (input.r1_val + BitVec.signExtend 32 input.imm).toNat,
      BitVec.extractLsb 7 0 input.r2_val
    )
    data1 := (
      (input.r1_val + BitVec.signExtend 32 input.imm).toNat + 1,
      BitVec.extractLsb 15 8 input.r2_val
    )
    : ShOutput
  }

  -- just used to allow the same tactics to handle the case for each non-zero register
  private def bitvec_to_reg (bv: BitVec 5) : Register :=
    match bv with
      | 0#5 => Register.x1 -- purely used for totality, does not come up
      | 1#5 => Register.x1
      | 2#5 => Register.x2
      | 3#5 => Register.x3
      | 4#5 => Register.x4
      | 5#5 => Register.x5
      | 6#5 => Register.x6
      | 7#5 => Register.x7
      | 8#5 => Register.x8
      | 9#5 => Register.x9
      | 10#5 => Register.x10
      | 11#5 => Register.x11
      | 12#5 => Register.x12
      | 13#5 => Register.x13
      | 14#5 => Register.x14
      | 15#5 => Register.x15
      | 16#5 => Register.x16
      | 17#5 => Register.x17
      | 18#5 => Register.x18
      | 19#5 => Register.x19
      | 20#5 => Register.x20
      | 21#5 => Register.x21
      | 22#5 => Register.x22
      | 23#5 => Register.x23
      | 24#5 => Register.x24
      | 25#5 => Register.x25
      | 26#5 => Register.x26
      | 27#5 => Register.x27
      | 28#5 => Register.x28
      | 29#5 => Register.x29
      | 30#5 => Register.x30
      | 31#5 => Register.x31
      | _ => Register.x1

  def modify_memory_2
    (s: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (output: ShOutput)
  := {
    regs := s.regs,
    choiceState := s.choiceState,
    tags := s.tags,
    cycleCount := s.cycleCount,
    sailOutput := s.sailOutput
    mem :=
      ((s.mem.insert output.data0.1 output.data0.2
      ).insert output.data1.1 output.data1.2)
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  }

  open Local.RegisterInvariants

  def sh_state_assumptions
    (i : ShInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    -- Connecting the registers
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    -- Assumptions
    i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat < OpenVM_memory_address_space_size ∧
    LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (i.r1_val + (BitVec.signExtend 32 i.imm))) 2 = true


  set_option maxHeartbeats 0 in
  lemma execute_STOREH_pure_equiv
    (input : ShInput)
    (h_assumptions : Local.Assumptions.general_memory_assumptions state)
    (h_sh_assumptions : sh_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.STORE (
          input.imm,
          regidx.Regidx input.r2,
          regidx.Regidx input.r1,
          2
        ))
    ) state =
    let output := execute_STOREH_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_2 (← get) output)
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
    ⟩ := h_sh_assumptions

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

    have h_execute_store := Local.execute_STOREH_simplified
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
    simp [EStateM.instMonadStateOf, EStateM.get, EStateM.set, modify_memory_2, execute_STOREH_pure, Sail.BitVec.addInt]

end PureSpec
