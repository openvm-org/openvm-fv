import OpenvmFv.Spec.LoadStore.local_extended
import OpenvmFv.Spec.rX_bits

namespace PureSpec

  structure LbuInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    rd : BitVec 5
    -- registers
    r1_val : BitVec 32
    PC : BitVec 32
    -- memory
    data0 : BitVec 8

  structure LbuOutput where
    -- registers
    nextPC : BitVec 32
    rd : Option (Finset.Icc 1 31 × BitVec 32)

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_LOADBU_pure (input : LbuInput) : LbuOutput := {
    nextPC := input.PC + 4#32
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          range input.rd h
        ⟩,
        (BitVec.extend (input.data0) 32 false)
      )
    : LbuOutput
  }

  open Local.RegisterInvariants

  def lbu_state_assumptions
    (i : LbuInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    -- Connecting the registers
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV32D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat]? = .some i.data0 ∧
    -- Assumptions
    i.r1_val.toNat + (BitVec.signExtend 32 i.imm).toNat < OpenVM_memory_address_space_size ∧
    LeanRV32D.Functions.is_aligned_vaddr (virtaddr.Virtaddr (i.r1_val + (BitVec.signExtend 32 i.imm))) 1 = true

  set_option maxHeartbeats 0 in
  lemma execute_LOADBU_pure_equiv
    (input : LbuInput)
    (h_assumptions : Local.Assumptions.general_memory_assumptions state)
    (h_lbu_assumptions : lbu_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV32D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          true,
          1
        ))
    ) state =
    let output := execute_LOADBU_pure input
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
      h_does_fit,
      h_aligned
    ⟩ := h_lbu_assumptions

    simp [
      readReg_state h_pc,
      writeReg_state_success,
    ]

    rewrite [
      Local.execute_load_instruction,
      ←Local.execute_LOAD_equiv
    ]
    simp

    replace h_r1_val := r1_of_write_state input.PC h_r1_val
    replace h_mstatus := mstatus_of_write_state input.PC h_mstatus
    replace h_cur_privilege := cur_privilege_of_write_state input.PC h_cur_privilege
    replace h_pma_regions := pma_regions_of_write_state input.PC h_pma_regions
    replace h_htif_tohost_base := htif_tohost_base_of_write_state input.PC h_htif_tohost_base

    have h_execute_load := Local.execute_LOADBU_simplified
      (write_reg_state state Register.nextPC (Sail.BitVec.addInt input.PC 4))
      (regidx.Regidx input.rd)
      input.data0
      h_r1_val
      h_mstatus
      h_cur_privilege
      h_htif_tohost_base
      h_mem_0
      h_does_fit
      h_aligned
      (by simp)
      h_plat_mstatus_val
      h_pma_regions
      h_pma_region_base_val
      h_pma_region_size_ub
      (by grind)

    simp [
      h_execute_load,
      execute_LOADBU_pure
    ]
    split_ifs with h_rd
    . simp [
        LeanRV32D.Functions.wX_bits,
        LeanRV32D.Functions.wX,
        h_rd,
        Sail.BitVec.addInt
      ]
    . simp [Sail.BitVec.addInt]
      rewrite [
        wX_write_xreg_equiv _ _
          (regidx.Regidx input.rd)
          ⟨input.rd.toNat, range input.rd h_rd⟩
      ]
      . obtain s | s := write_xreg
          ⟨input.rd.toNat, _⟩
          ((input.data0).extend 32 false)
          (write_reg_state state Register.nextPC (input.PC + 4#32))
        . simp
        . simp
      . simp

end PureSpec
