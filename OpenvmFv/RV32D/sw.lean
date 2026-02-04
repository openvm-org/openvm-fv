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
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    (i.r1_val + BitVec.signExtend 32 i.imm).toNat < OpenVM_address_space_size ∧
    (4 : ℤ) ∣ (i.r1_val.toNat + (BitVec.signExtend 32 i.imm)).toNat

  set_option maxHeartbeats 0 in
  lemma execute_STOREW_pure_equiv
    (input : SwInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : sw_state_assumptions input state)
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
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#32)
    unfold sw_state_assumptions at h_opcode_assumptions

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      *
    ]

    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#32) h_opcode_assumptions.2.1 reg_of_fin_neq_nextPC
    have h_r2_val := rX_bits_write_other_reg_state (val := input.PC + 4#32) h_opcode_assumptions.2.2.1 reg_of_fin_neq_nextPC

    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := next_gma

    simp at h_opcode_assumptions
    simp [LeanRV32D.Functions.execute_STORE, LeanRV32D.Functions.vmem_write, EStateM.map, *]
    simp [LeanRV32D.Functions.vmem_write_addr, ExceptT.run, *]
    rw [if_pos (by omega)]; simp [*]
    rw [if_pos
         (by
          rw [Int.emod_eq_of_lt (b := 18446744073709551616) (by omega) (by omega)];
          omega)]; simp [*]
    rw [if_pos (by omega)]; simp [*]
    rw [if_neg
          (by
           rw [Int.emod_eq_of_lt (b := 17179869184) (by omega) (by omega)]
           omega)]

    simp [execute_STOREW_pure, EStateM.set, modify_memory_4,
          BitVec.extractLsb, BitVec.extractLsb', *]
    repeat rw [Nat.mod_eq_of_lt (b := 17179869184) (by omega)]

end PureSpec
