import OpenvmFv.RV32D.Auxiliaries

namespace PureSpec

  structure LhuInput where
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

  structure LhuOutput where
    -- registers
    nextPC : BitVec 32
    rd : Option (Finset.Icc 1 31 × BitVec 32)

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_LOADHU_pure (input : LhuInput) : LhuOutput := {
    nextPC := input.PC + 4#32
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          range input.rd h
        ⟩,
        (BitVec.setWidth 32 (input.data1 ++ input.data0))
      )
    : LhuOutput
  }

  def lhu_state_assumptions
    (i : LhuInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    -- Connecting the registers
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat]? = .some i.data0 ∧
    state.mem[(i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat) + 1]? = .some i.data1 ∧
    -- Assumptions
    i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat < OpenVM_address_space_size ∧
    LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (i.r1_val + (BitVec.signExtend 32 i.imm))) 2 = true

  set_option maxHeartbeats 0 in
  lemma execute_LOADHU_pure_equiv
    (input : LhuInput)
    (h_assumptions : general_memory_assumptions state)
    (h_lhu_assumptions : lhu_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          true,
          2
        ))
    ) state =
    let output := execute_LOADHU_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
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
      h_mem_0,
      h_mem_1,
      h_does_fit,
      h_aligned
    ⟩ := h_lhu_assumptions

    simp [
      Sail.readReg,
      PreSail.readReg,
      h_pc,
      writeReg_state_success,
      LeanRV32D.Functions.execute
    ]

    replace h_r1_val := rX_bits_write_other_reg_state (r := input.r1) (val := input.PC + 4#32) h_r1_val reg_of_fin_neq_nextPC
    replace h_mstatus := readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := input.PC + 4#32) h_mstatus (by trivial)
    replace h_cur_privilege := readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := input.PC + 4#32) h_cur_privilege (by trivial)
    replace h_pma_regions := readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := input.PC + 4#32) h_pma_regions (by trivial)
    replace h_htif_tohost_base := readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := input.PC + 4#32) h_htif_tohost_base (by trivial)

    have h_execute_load := execute_LOADHU
      (write_reg_state state Register.nextPC (input.PC + 4#32))
      (regidx.Regidx input.rd)
      input.data0
      input.data1
      h_r1_val
      h_mstatus
      h_cur_privilege
      h_htif_tohost_base
      h_mem_0
      h_mem_1
      h_aligned
      (by simp)
      h_plat_mstatus_val
      h_pma_regions
      h_pma_region_base_val
      h_pma_region_size_ub
      (by grind)
      (by grind)

    simp [
      h_execute_load,
      execute_LOADHU_pure
    ]
    split_ifs with h_rd
    . simp [
        LeanRV32D.Functions.wX_bits,
        LeanRV32D.Functions.wX,
        h_rd,
      ]
    . simp
      rewrite [
        wX_write_xreg_non_zero_equiv _ _
          (regidx.Regidx input.rd)
          ⟨input.rd.toNat, range input.rd h_rd⟩
      ]
      . obtain s | s := write_xreg
          ⟨input.rd.toNat, _⟩
          (BitVec.setWidth 32 (input.data1 ++ input.data0))
          (write_reg_state state Register.nextPC (input.PC + 4#32))
        . simp
        . simp
      . simp

end PureSpec
