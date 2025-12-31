import OpenvmFv.RV32D.Auxiliaries

namespace PureSpec

  structure LwInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    rd : BitVec 5
    -- registers
    r1_val : BitVec 32
    PC : BitVec 32
    -- memory
    data0 : BitVec 8
    data1 : BitVec 8
    data2 : BitVec 8
    data3 : BitVec 8

  structure LwOutput where
    -- registers
    nextPC : BitVec 32
    rd : Option (Finset.Icc 1 31 × BitVec 32)

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_LOADW_pure (input : LwInput) : LwOutput := {
    nextPC := input.PC + 4#32
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          range input.rd h
        ⟩,
        input.data3 ++ input.data2 ++ input.data1 ++ input.data0
      )
    : LwOutput
  }

  def lw_state_assumptions
    (i : LwInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    -- Connecting the registers
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat]? = .some i.data0 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat + 1]? = .some i.data1 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat + 2]? = .some i.data2 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat + 3]? = .some i.data3 ∧
    -- Assumption : Memory address is not outside address space
    -- Note : This is an assumption for this proof, but is not an assumption in general because there is
    --        a static guarantee that all addresses on the memory bus must be less than 2 ^ 29
    i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat < OpenVM_address_space_size ∧
    -- Assumption A1 : Memory address alignment
    (4 : ℤ) ∣ i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat

  set_option maxHeartbeats 0 in
  lemma execute_LOADW_pure_equiv
    (input : LwInput)
    (h_general_assumptions : general_memory_assumptions state mstatus pmaRegion)
    (h_opcode_assumptions : lw_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          true,
          4
        ))
    ) state =
    let output := execute_LOADW_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := gma_invariant_under_pc_increment h_general_assumptions (val := input.PC + 4#32)
    unfold lw_state_assumptions at h_opcode_assumptions

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      *
    ]

    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#32) h_opcode_assumptions.2.1 reg_of_fin_neq_nextPC

    obtain ⟨ h_htif, h_priv, h_mprv , h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned ⟩ := next_gma
    have := arithmetic_helper (a := input.r1_val.toNat) (b := (BitVec.signExtend 32 input.imm).toNat) (by grind)

    simp [LeanRV32D.Functions.execute_LOAD, LeanRV32D.Functions.vmem_read, EStateM.map, *]
    simp [LeanRV32D.Functions.vmem_read_addr, ExceptT.run, *]
    rw [if_pos (by omega)]; simp [*]
    rw [if_neg (by omega)]

    simp [write_reg_state, execute_LOADW_pure, *]

    split_ifs with h_rd
    . simp [LeanRV32D.Functions.wX_bits, LeanRV32D.Functions.wX, *]
    . let r  : Finset.Icc 1 31 := ⟨input.rd.toNat, range input.rd h_rd⟩
      rewrite [ wX_write_xreg_non_zero_equiv _ _ _ r (by simp [r])]
      grind

end PureSpec
