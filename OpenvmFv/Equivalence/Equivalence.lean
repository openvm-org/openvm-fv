import OpenvmFv.Equivalence.Auipc
import OpenvmFv.Equivalence.BaseALU
import OpenvmFv.Equivalence.BranchEqual
import OpenvmFv.Equivalence.BranchLessThan
import OpenvmFv.Equivalence.DivRem
import OpenvmFv.Equivalence.JalLui
import OpenvmFv.Equivalence.JalR
import OpenvmFv.Equivalence.LoadSignExtend
import OpenvmFv.Equivalence.Lt
import OpenvmFv.Equivalence.Mul
import OpenvmFv.Equivalence.Mulh
import OpenvmFv.Equivalence.Shift

set_option maxHeartbeats 2_000_000
set_option maxRecDepth 20_000

namespace RV32IM.Equivalence

  section Auipc

    open VmAirWrapper_auipc.constraints
    open Equivalence.Auipc

    attribute [local simp]
      _executionBus_row
      executionBus_row
      _programBus_row
      programBus_row
      LeanRV32D.Functions.execute
      LeanRV32D.Functions.execute_UTYPE
      LeanRV32D.Functions.get_arch_pc

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : axiomsPerRow air row)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    include h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_bus

    theorem equiv_AUIPC
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let imm := (_programBus_row air row)[0]!.xc
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let imm := BitVec.ofNat 20 (imm.toNat >>> 4)
      let instr : instruction := instruction.UTYPE (imm, rd, uop.AUIPC)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by
      have h_spec := Auipc.ValidRows.spec_auipc ExtF air row h_row h_constraints h_is_valid h_bus_axioms h_bus_wellformedness

      have h_nzd := rd_neq_0 air row h_row h_constraints h_is_valid h_bus_wellformedness

      -- Apply the bus equivalence
      rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
      -- Get the hypotheses
      have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
      rw [this] at h_bus; clear this
      obtain ⟨ h_pc, h_rd ⟩ := h_bus
      extract_lets rd_ptr imm rd imm instr val reg_idx
      subst rd_ptr imm rd imm instr val reg_idx
      simp [h_pc, writeReg_state_success, -Fin.toNat_eq_val]; rw [Fin.toNat_eq_val]
      rw [readReg_of_write_other_reg_state h_pc (by simp)]
      simp
      rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx, get_instruction_fields_row] at h_nzd ⊢; omega ⟩) (h_rd := by simp)]
      simp [write_xreg, Sail.writeReg, PreSail.writeReg, write_reg_state, cast]
      rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; grind)]
      congr; rw [← h_spec]
      simp [← BitVec.toNat_inj, U32.toNat]

  end Auipc

  section BaseALU

    open VmAirWrapper_alu.constraints
    open Equivalence.BaseALU

    attribute [local simp]
      _programBus_row
      programBus_row
      execute_RTYPE'
      execute_ITYPE'
      execute_RTYPE_pure
      execute_ITYPE_pure
      ALU.ValidRows.rop_of_ALU_opcode
      ALU.ValidRows.iop_of_ALU_opcode

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_alu FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : axiomsPerRow air row)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    section ProofMacros

      set_option hygiene false

      macro "proof_start" : tactic => `(tactic| (
        simp [h_opcode] at h_spec
        -- Apply the bus equivalence
        rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
        -- Get the hypotheses
        have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
        rw [this] at h_bus; clear this
        obtain ⟨ h_pc, h_rs1, h_rs2, h_rd ⟩ := h_bus
        simp [h_imm] at h_rs2; clear h_rd
        -- Get the fact that rd is non-zero
        have h_nzd := rd_neq_0 air row h_row h_constraints h_is_valid h_bus_wellformedness
        simp [get_instruction_fields_row] at h_nzd

        extract_lets rs1_ptr rs2_ptr rd_ptr r2 r1 rd val reg_idx
        subst rs1_ptr rs2_ptr rd_ptr r2 r1 rd val reg_idx
        simp [
          h_pc,
          writeReg_state_success,
          LeanRV32D.Functions.execute
        ]
        rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
        rotate_left
        rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0)) (h_rd := by simp)]
        assumption
        simp
      ))

      macro "proof_non_imm_specific" : tactic => `(tactic| (
        rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
        rotate_left
        rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs2 row 0)) (h_rd := by simp)]
        assumption
        simp
      ))

      macro "proof_end" : tactic => `(tactic| (
        rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0)).val, by simp; omega ⟩) (h_rd := by simp)]
        simp [write_xreg, Sail.writeReg, PreSail.writeReg, write_reg_state, cast]
        rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; grind)]
        congr 3; symm
        assumption
      ))

      macro "alu_non_imm_proof" : tactic => `(tactic| (
        -- Get the spec
        have h_spec := ALU.ValidRows.spec_base_ALU_non_imm ExtF air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_imm
        proof_start; proof_non_imm_specific; proof_end
      ))

      macro "alu_imm_proof" : tactic => `(tactic| (
        -- Get the spec
        have h_spec := ALU.ValidRows.spec_base_ALU_imm ExtF air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_imm
        proof_start; proof_end
      ))

    end ProofMacros

    include h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_bus

    theorem equiv_ADD
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 512)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.RTYPE (r2, r1, rd, rop.ADD)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_non_imm_proof

    theorem equiv_ADDI
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 512)
      (h_imm : air.adapter.rs2_as row 0 = 0)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.ITYPE (imm, r1, rd, iop.ADDI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_imm_proof

    theorem equiv_SUB
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 513)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.RTYPE (r2, r1, rd, rop.SUB)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_non_imm_proof

    theorem equiv_XOR
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 514)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.RTYPE (r2, r1, rd, rop.XOR)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_non_imm_proof

    theorem equiv_XORI
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 514)
      (h_imm : air.adapter.rs2_as row 0 = 0)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.ITYPE (imm, r1, rd, iop.XORI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_imm_proof

    theorem equiv_OR
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 515)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.RTYPE (r2, r1, rd, rop.OR)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_non_imm_proof

    theorem equiv_ORI
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 515)
      (h_imm : air.adapter.rs2_as row 0 = 0)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.ITYPE (imm, r1, rd, iop.ORI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_imm_proof

    theorem equiv_AND
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 516)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.RTYPE (r2, r1, rd, rop.AND)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_non_imm_proof

    theorem equiv_ANDI
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 516)
      (h_imm : air.adapter.rs2_as row 0 = 0)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.ITYPE (imm, r1, rd, iop.ANDI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_imm_proof

  end BaseALU

  section BranchEqual

    open VmAirWrapper_branch_eq.constraints
    open Equivalence.BranchEqual

    attribute [local simp]
      _programBus_row
      programBus_row
      LeanRV32D.Functions.execute
      LeanRV32D.Functions.execute_BTYPE

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : axiomsPerRow air row)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    section ProofMacros

      set_option hygiene false

      macro "proof_common" : tactic => `(tactic| (
        have h_spec := BranchEqual.ValidRows.spec_BEQ_BNE_pc ExtF air row h_row h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
        simp [h_opcode] at h_spec
        -- Apply the bus equivalence
        rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
        -- Get the hypotheses
        have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
        rw [this] at h_bus; clear this
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus
        extract_lets rs1_ptr rs2_ptr imm r2 r1 imm instr
        subst rs1_ptr rs2_ptr imm r2 r1 imm instr
        -- Get the axioms
        simp [h_is_valid, VmAirWrapper_branch_eq_constraint_and_interaction_simplification, and_assoc] at h_bus_axioms
        obtain ⟨ ub_pc, al_pc, ub_tpc, al_tpc, rest ⟩ := h_bus_axioms; clear rest
        replace al_tpc : (BitVec.ofNat 32 (air.to_pc row 0)).toNat % 4 = 0
          := by simp; grind
        simp [
          h_pc,
          writeReg_state_success,
        ]
        rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
        rotate_left
        rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0)) (h_rd := by simp)]
        assumption
        simp
        rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
        rotate_left
        rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs2_ptr row 0)) (h_rd := by simp)]
        assumption
        simp
      ))

    end ProofMacros

    include h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_bus

    theorem equiv_BEQ
      (ex_reg_misa : state.regs.get? Register.misa = .some misa)
      (h_opcode : air.core.expected_opcode row 0 = 544)
    :
      let rs1_ptr := (_programBus_row air row)[0]!.xa
      let rs2_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let imm : BitVec 13 := BitVec.ofInt 13 (BabyBear.toInt imm)
      let instr : instruction := instruction.BTYPE (imm, r2, r1, bop.BEQ)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by
      proof_common
      split_ifs at h_spec
      . rw [if_pos (by assumption), h_spec]
        rw [readReg_of_write_other_reg_state h_pc (by simp)]
        simp
        rw [if_neg,
            writeReg_read_diff ex_reg_misa (by simp)]
        . simp
          rw [if_neg]
          . simp [write_reg_state]
          . rw [← h_spec]; clear *- ub_tpc al_tpc
            simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
            rw [Nat.mod_eq_of_lt (by omega)]
            grind
        . rw [← h_spec]; clear *- ub_tpc al_tpc
          simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
          grind
      . rw [if_neg (by assumption), h_spec]
        simp [write_reg_state]

    theorem equiv_BNE
      (ex_reg_misa : state.regs.get? Register.misa = .some misa)
      (h_opcode : air.core.expected_opcode row 0 = 545)
    :
      let rs1_ptr := (_programBus_row air row)[0]!.xa
      let rs2_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let imm : BitVec 13 := BitVec.ofInt 13 (BabyBear.toInt imm)
      let instr : instruction := instruction.BTYPE (imm, r2, r1, bop.BNE)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by
      proof_common
      split_ifs at h_spec
      . rw [if_pos (by assumption), h_spec]
        simp [write_reg_state]
      . rw [if_neg (by assumption), h_spec]
        rw [readReg_of_write_other_reg_state h_pc (by simp)]
        simp
        rw [if_neg,
            writeReg_read_diff ex_reg_misa (by simp)]
        . simp
          rw [if_neg]
          . simp [write_reg_state]
          . rw [← h_spec]; clear *- ub_tpc al_tpc
            simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
            rw [Nat.mod_eq_of_lt (by omega)]
            grind
        . rw [← h_spec]; clear *- ub_tpc al_tpc
          simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
          grind

  end BranchEqual

  section BranchLessThan

    open VmAirWrapper_branch_lt.constraints
    open Equivalence.BranchLessThan

    attribute [local simp]
      _programBus_row
      programBus_row
      LeanRV32D.Functions.execute
      LeanRV32D.Functions.execute_BTYPE

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : axiomsPerRow air row)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    section ProofMacros

      set_option hygiene false

      macro "proof_common" : tactic => `(tactic| (
        have h_spec := BranchLessThan.ValidRows.spec_BLT_BLTU_BGE_BGEU_pc ExtF air row h_row h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
        simp [h_opcode] at h_spec
        -- Apply the bus equivalence
        rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
        -- Get the hypotheses
        have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
        rw [this] at h_bus; clear this
        obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus
        extract_lets rs1_ptr rs2_ptr imm r1 r2 imm instr
        subst rs1_ptr rs2_ptr imm r1 r2 imm instr
        -- Get the axioms
        simp [h_is_valid, VmAirWrapper_branch_lt_constraint_and_interaction_simplification, and_assoc] at h_bus_axioms
        obtain ⟨ ub_pc, al_pc, ub_tpc, al_tpc, rest ⟩ := h_bus_axioms; clear rest
        replace al_tpc : (BitVec.ofNat 32 (air.to_pc row 0)).toNat % 4 = 0
          := by simp; clear *- al_tpc; grind
        simp [
          h_pc,
          writeReg_state_success,
        ]
        rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
        rotate_left
        rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0)) (h_rd := by simp)]
        assumption
        simp
        rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
        rotate_left
        rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs2_ptr row 0)) (h_rd := by simp)]
        assumption
        simp
        split_ifs at h_spec
        . rw [if_pos (by assumption), h_spec]
          rw [readReg_of_write_other_reg_state h_pc (by simp)]
          simp
          rw [if_neg,
              writeReg_read_diff ex_reg_misa (by simp)]
          . simp
            rw [if_neg]
            . simp [write_reg_state]
            . rw [← h_spec]; clear *- ub_tpc al_tpc
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rw [Nat.mod_eq_of_lt (by omega)]
              grind
          . rw [← h_spec]; clear *- ub_tpc al_tpc
            simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
            grind
        . rw [if_neg (by assumption), h_spec]
          simp [write_reg_state]
      ))

    end ProofMacros

    include h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_bus

    theorem equiv_BLT
      (ex_reg_misa : state.regs.get? Register.misa = .some misa)
      (h_opcode : air.core.expected_opcode row 0 = 549)
    :
      let rs1_ptr := (_programBus_row air row)[0]!.xa
      let rs2_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let imm : BitVec 13 := BitVec.ofInt 13 (BabyBear.toInt imm)
      let instr : instruction := instruction.BTYPE (imm, r2, r1, bop.BLT)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by proof_common

    theorem equiv_BLTU
      (ex_reg_misa : state.regs.get? Register.misa = .some misa)
      (h_opcode : air.core.expected_opcode row 0 = 550)
    :
      let rs1_ptr := (_programBus_row air row)[0]!.xa
      let rs2_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let imm : BitVec 13 := BitVec.ofInt 13 (BabyBear.toInt imm)
      let instr : instruction := instruction.BTYPE (imm, r2, r1, bop.BLTU)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by proof_common

    theorem equiv_BGE
      (ex_reg_misa : state.regs.get? Register.misa = .some misa)
      (h_opcode : air.core.expected_opcode row 0 = 551)
    :
      let rs1_ptr := (_programBus_row air row)[0]!.xa
      let rs2_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let imm : BitVec 13 := BitVec.ofInt 13 (BabyBear.toInt imm)
      let instr : instruction := instruction.BTYPE (imm, r2, r1, bop.BGE)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by proof_common

    theorem equiv_BGEU
      (ex_reg_misa : state.regs.get? Register.misa = .some misa)
      (h_opcode : air.core.expected_opcode row 0 = 552)
    :
      let rs1_ptr := (_programBus_row air row)[0]!.xa
      let rs2_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let imm : BitVec 13 := BitVec.ofInt 13 (BabyBear.toInt imm)
      let instr : instruction := instruction.BTYPE (imm, r2, r1, bop.BGEU)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by proof_common

  end BranchLessThan

  @[simp]
  lemma bv_ofFin_ofNat
    (x : Fin 256)
  : @BitVec.ofFin 8 x = BitVec.ofNat 8 x.val
    := by simp

  @[simp]
  lemma bv_ofNat_clearMod
    (x : ℕ)
  : BitVec.ofNat 8 (x % 256) = BitVec.ofNat 8 x
    := by simp [← BitVec.toNat_inj]

  @[simp]
  lemma bv_natCast_bv8
    (x : FBB)
  :
    @Nat.cast (BitVec 8) BitVec.instNatCast x = BitVec.ofNat 8 x.val
  := by simp

  section DivRem

    open VmAirWrapper_divrem.constraints
    open Equivalence.DivRem

    attribute [local simp]
      _executionBus_row
      executionBus_row
      _programBus_row
      programBus_row
      execute_DIV'
      execute_REM'
      execute_DIV_REM_pure
      execute_DIV_REM_pure_int

    attribute [-simp]
      Int.tmod_eq_emod

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : axiomsPerRow air row)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    section ProofMacros

      set_option hygiene false

      macro "proof_common" : tactic => `(tactic| (
        have h_ess := DivRem.ValidRows.essentials ExtF air row h_row h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
        have h_spec := h_ess.2.2.2.2.2.2.2.2.2.2.2.2.2
        obtain ⟨ ua0, ua1, ua2, ua3, ub0, ub1, ub2, ub3, uc0, uc1, uc2, uc3 ⟩ :
          (air.core.a row 0 0).val % 256 = (air.core.a row 0 0).val ∧ (air.core.a row 0 1).val % 256 = (air.core.a row 0 1).val ∧ (air.core.a row 0 2).val % 256 = (air.core.a row 0 2).val ∧ (air.core.a row 0 3).val % 256 = (air.core.a row 0 3).val ∧
          (air.core.b_0 row 0).val % 256 = (air.core.b_0 row 0).val ∧ (air.core.b_1 row 0).val % 256 = (air.core.b_1 row 0).val ∧ (air.core.b_2 row 0).val % 256 = (air.core.b_2 row 0).val ∧ (air.core.b_3 row 0).val % 256 = (air.core.b_3 row 0).val ∧
          (air.core.c_0 row 0).val % 256 = (air.core.c_0 row 0).val ∧ (air.core.c_1 row 0).val % 256 = (air.core.c_1 row 0).val ∧ (air.core.c_2 row 0).val % 256 = (air.core.c_2 row 0).val ∧ (air.core.c_3 row 0).val % 256 = (air.core.c_3 row 0).val
        := by omega
        simp [h_opcode] at h_spec
        obtain ⟨ ha0, ha1, ha2, ha3 ⟩ := h_ess
        -- Apply the bus equivalence
        rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
        -- Get the hypotheses
        have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
        rw [this] at h_bus; clear this
        obtain ⟨ h_pc, h_rs1, h_rs2, h_rd ⟩ := h_bus; clear h_rd
        -- Get the fact that rd is non-zero
        have h_nzd := rd_neq_0 air row h_row h_constraints h_is_valid h_bus_wellformedness
        simp [get_instruction_fields_row] at h_nzd

        extract_lets rd_ptr rs1_ptr rs2_ptr rs1 rs2 rd instr val reg_idx
        simp [ ub0, ub1, ub2, ub3, uc0, uc1, uc2, uc3 ] at h_rs1 h_rs2
        subst rd_ptr rs1_ptr rs2_ptr rs1 rs2 rd instr val reg_idx
        simp [
          h_pc,
          writeReg_state_success,
          LeanRV32D.Functions.execute,
          ua0, ua1, ua2, ua3
        ]
        rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
        rotate_left
        rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0)) (h_rd := by simp)]
        assumption
        simp
        rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
        rotate_left
        rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs2_ptr row 0)) (h_rd := by simp)]
        assumption
        simp [h_spec]

        replace h_spec := DivRem.ValidRows.spec_DIVREM ExtF air row h_row h_constraints h_is_valid h_bus_wellformedness
        have h_spec' := DivRem.ValidRows.spec_DIVUREMU ExtF air row h_row h_constraints h_is_valid h_bus_wellformedness
        simp [h_opcode] at h_spec h_spec'

        (try simp [← h_spec]); (try simp [← h_spec'])

        rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_nzd ⊢; omega ⟩) (h_rd := by simp)]
        simp [write_xreg, Sail.writeReg, PreSail.writeReg, write_reg_state, cast]
        rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; clear *- this; grind)]
      ))

    end ProofMacros

    include h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_bus

    theorem equiv_DIV
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 596)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let rs1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let rs2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := .DIV (rs2, rs1, rd, false)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by proof_common

    theorem equiv_DIVU
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 597)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let rs1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let rs2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := .DIV (rs2, rs1, rd, true)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by proof_common

    theorem equiv_REM
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 598)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let rs1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let rs2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := .REM (rs2, rs1, rd, false)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by proof_common

    theorem equiv_REMU
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 599)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let rs1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let rs2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := .REM (rs2, rs1, rd, true)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by proof_common

  end DivRem

  section JalR

    open VmAirWrapper_jalr.constraints
    open Equivalence.JalR

    attribute [local simp]
      _executionBus_row
      executionBus_row
      _programBus_row
      programBus_row
      LeanRV32D.Functions.execute
      LeanRV32D.Functions.execute_JALR
      LeanRV32D.Functions.update_elp_state
      LeanRV32D.Functions.get_xLPE

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_jalr FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : axiomsPerRow air row)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    include h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_bus

    theorem equiv_JALR
      (ex_reg_mseccfg : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state)
      (ex_reg_misa : state.regs.get? Register.misa = .some misa)
      (assumption_privilege : Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let rs1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm
      let instr : instruction := .JALR (imm, rs1, rd)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by
      have h_nzd := rd_neq_0 air row h_row h_constraints h_is_valid h_bus_wellformedness
      simp [get_instruction_fields_row] at h_nzd

      obtain ⟨ h_spec_rd, h_spec_npc ⟩ := JalR.ValidRows.spec_jalr ExtF air row h_row h_constraints h_bus_axioms h_bus_wellformedness (by simp [h_is_valid])
      -- Apply the bus equivalence
      rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
      -- Get the hypotheses
      have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
      rw [this] at h_bus; clear this
      obtain ⟨ h_pc, h_rs1, h_rd ⟩ := h_bus
      extract_lets rd_ptr rs1_ptr imm rd rs1 imm instr
      subst rd_ptr rs1_ptr imm rd rs1 imm instr
      simp at h_rs1 h_rd h_spec_rd h_spec_npc
      -- Get the axioms
      simp [h_is_valid, VmAirWrapper_branch_eq_constraint_and_interaction_simplification, and_assoc] at h_bus_axioms
      obtain ⟨ ub_pc, al_pc, ub_tpc, al_tpc, rest ⟩ := h_bus_axioms; clear rest
      replace al_tpc : (BitVec.ofNat 32 (air.core.to_pc row 0)).toNat % 4 = 0
        := by simp; grind
      simp [
        h_pc,
        writeReg_state_success,
      ]
      rw [readReg_of_write_other_reg_state assumption_privilege (h_neq := by simp)]
      simp
      rw [readReg_of_write_other_reg_state ex_reg_mseccfg (h_neq := by simp)]
      simp
      rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
      rotate_left
      rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0)) (h_rd := by simp)]
      assumption
      simp [Sail.BitVec.update]
      rw [if_neg]
      . rw [writeReg_read_diff ex_reg_misa (h_neq := by simp)]
        simp
        rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_nzd ⊢; omega ⟩) (h_rd := by simp)]
        simp [write_xreg, Sail.writeReg, PreSail.writeReg, write_reg_state, cast]
        rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; grind)]
        congr
        . simp [h_spec_rd]
        . simp [h_spec_npc]
      . simp [h_spec_npc] at al_tpc
        obtain ⟨ x, eq_x ⟩ : ∃ x, x = U32.toNat #v[BitVec.ofNat 8 (air.core.rs1_data_0 row 0).val, BitVec.ofNat 8 (air.core.rs1_data_1 row 0).val, BitVec.ofNat 8 (air.core.rs1_data_2 row 0).val, BitVec.ofNat 8 (air.core.rs1_data_3 row 0).val] +
                                      (BitVec.signExtend 32 (BitVec.ofNat 12 (air.core.imm row 0).val)).toNat := by simp
        simp [← BitVec.toNat_inj] at h_spec_npc
        rw [Nat.mod_eq_of_lt (b := 4294967296) (by omega)] at h_spec_npc
        simp [Fin.lt_def, h_spec_npc] at ub_tpc
        rw [← eq_x] at al_tpc ub_tpc
        simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat, ← eq_x]
        have : (x % 4294967296).testBit 1 = x.testBit 1
          := by simp [Nat.testBit_eq_decide_div_mod_eq]; omega
        rw [this]; clear this
        simp [Nat.testBit_eq_decide_div_mod_eq]
        clear *- al_tpc
        simp [Bool.cond_eq_ite]
        suffices : (x % 4294967296) / 2 % 2 = 0
        . omega
        . obtain ⟨ x, eq_x, ub_x ⟩ : ∃ y, y = x % 4294967296 ∧ y < 4294967296
          := by use x % 4294967296; simp; omega
          rw [← eq_x] at al_tpc ⊢; clear eq_x
          suffices : (x % 4) / 2 % 2 = 0
          . omega
          . have := @Nat.and_mod_two_pow 4294967294 x 2
            simp [this] at al_tpc; clear this ub_x
            rw [Nat.and_comm] at al_tpc
            have := @Nat.and_two_pow (i := 1) (x % 4)
            simp [al_tpc] at this
            simp [Nat.testBit_eq_decide_div_mod_eq] at this
            assumption

  end JalR

  section JalLui

    open VmAirWrapper_jallui.constraints
    open Equivalence.JalLui

    attribute [local simp]
      _executionBus_row
      executionBus_row
      _programBus_row
      programBus_row
      LeanRV32D.Functions.execute
      LeanRV32D.Functions.execute_JAL
      LeanRV32D.Functions.execute_UTYPE

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_jallui FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : axiomsPerRow air row)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    include h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_bus

    theorem equiv_JAL
      (ex_reg_misa : state.regs.get? Register.misa = .some misa)
      (h_opcode : air.core.expected_opcode row 0 = 560)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let imm := (_programBus_row air row)[0]!.xc
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let imm : BitVec 21 := BitVec.ofInt 21 (BabyBear.toInt imm)
      let instr : instruction := .JAL (imm, rd)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by
      have h_nzd := rd_neq_0 air row h_row h_constraints h_is_valid h_bus_wellformedness
      simp [get_instruction_fields_row] at h_nzd

      have h_spec := JalLui.ValidRows.spec_jal ExtF air row h_row h_constraints h_bus_axioms h_bus_wellformedness (by simp [h_is_valid])
      simp [h_opcode] at h_spec
      obtain ⟨ h_spec_rd, h_spec_pc ⟩ := h_spec

      -- Apply the bus equivalence
      rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
      -- Get the hypotheses
      have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
      rw [this] at h_bus; clear this
      obtain ⟨ h_pc, h_rd ⟩ := h_bus
      extract_lets rd_ptr imm rd imm instr
      subst rd_ptr imm rd imm instr
      simp at h_rd h_spec_rd h_spec_pc
      -- Get the axioms
      simp [h_is_valid, VmAirWrapper_branch_eq_constraint_and_interaction_simplification, and_assoc] at h_bus_axioms
      obtain ⟨ ub_pc, al_pc, ub_tpc, al_tpc, rest ⟩ := h_bus_axioms; clear rest
      replace al_tpc : (BitVec.ofNat 32 (air.to_pc row 0)).toNat % 4 = 0
        := by simp; grind
      simp [
        h_pc,
        writeReg_state_success,
      ]
      rw [readReg_of_write_other_reg_state h_pc (h_neq := by simp)]
      simp
      rw [if_neg]
      . rw [writeReg_read_diff ex_reg_misa (h_neq := by simp)]
        simp
        rw [if_neg]
        . simp
          rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.inner.rd_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_nzd ⊢; omega ⟩) (h_rd := by simp)]
          simp [write_xreg, Sail.writeReg, PreSail.writeReg, write_reg_state, cast]
          rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; grind)]
          congr 3
          . rw [h_spec_rd]
          . rw [h_spec_pc]
        . rw [← h_spec_pc]
          simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
          rw [Nat.mod_eq_of_lt (by omega)]
          grind
      . rw [← h_spec_pc]
        simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
        grind

    theorem equiv_LUI
      (ex_reg_misa : state.regs.get? Register.misa = .some misa)
      (h_opcode : air.core.expected_opcode row 0 = 561)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let imm := (_programBus_row air row)[0]!.xc
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let imm : BitVec 21 := BitVec.ofNat 21 imm
      let instr : instruction := .UTYPE (imm, rd, .LUI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by
      have h_nzd := rd_neq_0 air row h_row h_constraints h_is_valid h_bus_wellformedness
      simp [get_instruction_fields_row] at h_nzd

      have spec := JalLui.ValidRows.spec_lui ExtF air row h_row h_constraints h_bus_axioms h_bus_wellformedness (by simp [h_is_valid])
      simp [h_opcode] at spec
      obtain ⟨ h_spec_rd, h_spec_pc ⟩ := spec

      -- Apply the bus equivalence
      rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
      -- Get the hypotheses
      have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
      rw [this] at h_bus; clear this
      obtain ⟨ h_pc, h_rd ⟩ := h_bus
      extract_lets rd_ptr imm rd imm instr
      subst rd_ptr imm rd imm instr
      simp at h_rd h_spec_rd h_spec_pc
      -- Get the axioms
      simp [h_is_valid, VmAirWrapper_branch_eq_constraint_and_interaction_simplification, and_assoc] at h_bus_axioms
      obtain ⟨ ub_pc, al_pc, ub_tpc, al_tpc, rest ⟩ := h_bus_axioms; clear rest
      replace al_tpc : (BitVec.ofNat 32 (air.to_pc row 0)).toNat % 4 = 0
        := by simp; grind
      simp [
        h_pc,
        writeReg_state_success,
      ]
      rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.inner.rd_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_nzd ⊢; omega ⟩) (h_rd := by simp)]
      simp [write_xreg, Sail.writeReg, PreSail.writeReg, write_reg_state, cast]
      rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; grind)]
      rw [h_spec_rd, h_spec_pc]

  end JalLui

  section Lt

    open VmAirWrapper_lt.constraints
    open Equivalence.Lt

    attribute [local simp]
      _programBus_row
      programBus_row
      execute_RTYPE'
      execute_ITYPE'
      execute_RTYPE_pure
      execute_ITYPE_pure
      ALU.ValidRows.rop_of_ALU_opcode
      ALU.ValidRows.iop_of_ALU_opcode

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_lt FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : axiomsPerRow air row)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    section ProofMacros

      set_option hygiene false

      macro "lt_non_imm_proof" : tactic => `(tactic| (
        -- Get the spec
        have h_spec := Lt.ValidRows.spec_base_Lt_non_imm ExtF air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_imm
        proof_start; proof_non_imm_specific; proof_end
      ))

      macro "lt_imm_proof" : tactic => `(tactic| (
        -- Get the spec
        have h_spec := Lt.ValidRows.spec_base_Lt_imm ExtF air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_imm
        proof_start; proof_end
      ))

    end ProofMacros

    include h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_bus

    theorem equiv_SLT
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 520)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.RTYPE (r2, r1, rd, rop.SLT)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by lt_non_imm_proof

    theorem equiv_SLTI
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 520)
      (h_imm : air.adapter.rs2_as row 0 = 0)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.ITYPE (imm, r1, rd, iop.SLTI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by lt_imm_proof

    theorem equiv_SLTU
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 521)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.RTYPE (r2, r1, rd, rop.SLTU)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by lt_non_imm_proof

    theorem equiv_SLTIU
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 521)
      (h_imm : air.adapter.rs2_as row 0 = 0)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.ITYPE (imm, r1, rd, iop.SLTIU)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by lt_imm_proof

  end Lt

  section Mul

    open VmAirWrapper_mul.constraints
    open Equivalence.Mul

    attribute [local simp]
      _executionBus_row
      executionBus_row
      _programBus_row
      programBus_row
      execute_MUL'
      execute_MUL_pure
      Mul.ValidRows.rop_of_Mul_opcode
      mop_of_mul_op

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_mul FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    include h_constraints h_is_valid h_bus_wellformedness h_bus

    theorem equiv_MUL
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 592)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let rs1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let rs2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := .MUL (rs2, rs1, rd, { result_part := .Low, signed_rs1 := srs1, signed_rs2 := srs2 : mul_op})
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by
      have h_spec := Mul.ValidRows.spec_MUL ExtF air row h_is_valid h_bus_wellformedness
      simp [h_opcode, execute_MUL_pure] at h_spec
      -- Apply the bus equivalence
      rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
      -- Get the hypotheses
      have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
      rw [this] at h_bus; clear this
      obtain ⟨ h_pc, h_rs1, h_rs2, h_rd ⟩ := h_bus; clear h_rd
      -- Get the fact that rd is non-zero
      have h_nzd := rd_neq_0 air row h_row h_constraints h_is_valid h_bus_wellformedness
      simp [get_instruction_fields_row] at h_nzd

      extract_lets rd_ptr rs1_ptr rs2_ptr rs1 rs2 rd instr val reg_idx
      subst rd_ptr rs1_ptr rs2_ptr rs1 rs2 rd instr val reg_idx
      simp [
        h_pc,
        writeReg_state_success,
        LeanRV32D.Functions.execute,
      ]
      rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
      rotate_left
      rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0)) (h_rd := by simp)]
      assumption
      simp
      rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
      rotate_left
      rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs2_ptr row 0)) (h_rd := by simp)]
      assumption
      simp [h_spec]
      rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_nzd ⊢; omega ⟩) (h_rd := by simp)]
      simp [write_xreg, Sail.writeReg, PreSail.writeReg, write_reg_state, cast]
      rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; clear *- this; grind)]


  end Mul

  section Mulh

    open VmAirWrapper_mulh.constraints
    open Equivalence.Mulh

    attribute [local simp]
      _executionBus_row
      executionBus_row
      _programBus_row
      programBus_row
      execute_MUL'
      execute_MUL_pure
      Mulh.ValidRows.rop_of_Mulh_opcode
      mop_of_mul_op

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_mulh FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    section ProofMacros

      set_option hygiene false

      macro "proof_common" : tactic => `(tactic| (
        have h_spec := Mulh.ValidRows.spec_mulh ExtF air row h_row h_constraints h_is_valid h_bus_wellformedness
        simp [h_opcode, execute_MUL_pure] at h_spec
        -- Apply the bus equivalence
        rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
        -- Get the hypotheses
        have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
        rw [this] at h_bus; clear this
        obtain ⟨ h_pc, h_rs1, h_rs2, h_rd ⟩ := h_bus; clear h_rd
        -- Get the fact that rd is non-zero
        have h_nzd := rd_neq_0 air row h_row h_constraints h_is_valid h_bus_wellformedness
        simp [get_instruction_fields_row] at h_nzd

        extract_lets rd_ptr rs1_ptr rs2_ptr rs1 rs2 rd instr val reg_idx
        subst rd_ptr rs1_ptr rs2_ptr rs1 rs2 rd instr val reg_idx
        simp [
          h_pc,
          writeReg_state_success,
          LeanRV32D.Functions.execute,
        ]
        rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
        rotate_left
        rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0)) (h_rd := by simp)]
        assumption
        simp
        rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
        rotate_left
        rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs2_ptr row 0)) (h_rd := by simp)]
        assumption
        simp [h_spec]
        rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_nzd ⊢; omega ⟩) (h_rd := by simp)]
        simp [write_xreg, Sail.writeReg, PreSail.writeReg, write_reg_state, cast]
        rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; clear *- this; grind)]
      ))

    end ProofMacros

    include h_constraints h_is_valid h_bus_wellformedness h_bus

    theorem equiv_MULH
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 593)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let rs1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let rs2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed : mul_op})
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by
      have h_spec := Mulh.ValidRows.spec_mulh ExtF air row h_row h_constraints h_is_valid h_bus_wellformedness
      simp [h_opcode, execute_MUL_pure] at h_spec
      -- Apply the bus equivalence
      rw [chip_bus_effect air row h_row h_constraints h_is_valid h_bus_wellformedness h_bus]
      -- Get the hypotheses
      have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
      rw [this] at h_bus; clear this
      obtain ⟨ h_pc, h_rs1, h_rs2, h_rd ⟩ := h_bus; clear h_rd
      -- Get the fact that rd is non-zero
      have h_nzd := rd_neq_0 air row h_row h_constraints h_is_valid h_bus_wellformedness
      simp [get_instruction_fields_row] at h_nzd

      extract_lets rd_ptr rs1_ptr rs2_ptr rs1 rs2 rd instr val reg_idx
      subst rd_ptr rs1_ptr rs2_ptr rs1 rs2 rd instr val reg_idx
      simp [
        h_pc,
        writeReg_state_success,
        LeanRV32D.Functions.execute,
      ]
      rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
      rotate_left
      rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0)) (h_rd := by simp)]
      assumption
      simp
      rw [rX_bits_write_other_reg_state (h_neq := by apply reg_of_fin_neq_nextPC)]
      rotate_left
      rw [rX_read_xreg_equiv (rd := Transpiler.wrap_to_regidx (air.adapter.rs2_ptr row 0)) (h_rd := by simp)]
      assumption
      simp [h_spec]
      rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_nzd ⊢; omega ⟩) (h_rd := by simp)]
      simp [write_xreg, Sail.writeReg, PreSail.writeReg, write_reg_state, cast]
      rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; clear *- this; grind)]

    theorem equiv_MULHSU
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 594)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let rs1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let rs2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned : mul_op})
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by proof_common

    theorem equiv_MULHU
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 595)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let rs1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let rs2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := .MUL (rs2, rs1, rd, { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned : mul_op})
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by proof_common

  end Mulh

  section Shift

    open VmAirWrapper_shift.constraints
    open Equivalence.Shift

    attribute [local simp]
      _programBus_row
      programBus_row
      execute_RTYPE'
      execute_ITYPE'
      execute_SHIFTIOP'
      execute_RTYPE_pure
      execute_ITYPE_pure
      ALU.ValidRows.rop_of_ALU_opcode
      ALU.ValidRows.iop_of_ALU_opcode

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_shift FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : axiomsPerRow air row)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    section ProofMacros

      set_option hygiene false

      macro "shift_non_imm_proof" : tactic => `(tactic| (
        -- Get the spec
        have h_spec := Shift.ValidRows.spec_base_Shift_non_imm ExtF air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_imm
        proof_start; proof_non_imm_specific; proof_end
      ))

      macro "shift_imm_proof" : tactic => `(tactic| (
        -- Get the spec
        have h_spec := Shift.ValidRows.spec_base_Shift_imm ExtF air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_imm
        proof_start; proof_end
      ))

    end ProofMacros

    include h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_bus

    theorem equiv_SLL
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 517)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.RTYPE (r2, r1, rd, rop.SLL)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by shift_non_imm_proof

    theorem equiv_SLLI
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 517)
      (h_imm : air.adapter.rs2_as row 0 = 0)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.SHIFTIOP (imm, r1, rd, .SLLI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by shift_imm_proof

    theorem equiv_SRL
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 518)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.RTYPE (r2, r1, rd, rop.SRL)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by shift_non_imm_proof

    theorem equiv_SRLI
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 518)
      (h_imm : air.adapter.rs2_as row 0 = 0)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.SHIFTIOP (imm, r1, rd, .SRLI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by shift_imm_proof

    theorem equiv_SRA
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 519)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let rs2_ptr := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let r2 : regidx := ⟨ (Transpiler.wrap_to_regidx rs2_ptr).val, by simp ⟩
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.RTYPE (r2, r1, rd, rop.SRA)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by shift_non_imm_proof

    theorem equiv_SRAI
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 519)
      (h_imm : air.adapter.rs2_as row 0 = 0)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.SHIFTIOP (imm, r1, rd, .SRAI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by shift_imm_proof

  end Shift

  section LoadSignExtend

    open VmAirWrapper_load_sign_extend.constraints

    attribute [local simp]
      _executionBus_row
      executionBus_row
      _programBus_row
      programBus_row

    variable
      [Field ExtF]
      (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : axiomsPerRow air row)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)

    include h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_bus

    theorem equiv_LOADB
      (h_opcode : air.core.expected_opcode row 0 = 534)

      (h_general_assumptions : general_memory_assumptions state mstatus pmaRegion)
      (assumption_alignment : (air.read_ptr row 0).val % 4 = 0)
    :
      let rd_ptr := (_programBus_row air row)[0]!.xa
      let rs1_ptr := (_programBus_row air row)[0]!.xb
      let imm := (_programBus_row air row)[0]!.xc
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let rs1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm
      let instr : instruction := .LOAD (imm, rs1, rd, false, 1)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
  := by
    extract_lets rd_ptr rs1_ptr imm rd rs1 imm instruction
    subst instruction

    have effect_z := LoadB.chip_bus_effect_rdz air row h_row h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_opcode h_bus
    have effect_nz := LoadB.chip_bus_effect_rdnz air row h_row h_constraints h_is_valid h_bus_axioms h_bus_wellformedness h_opcode h_bus

    have h_ub_read_ptr := h_bus_wellformedness
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      show ((2013265920 : FBB) = -1) by decide,
    ] at h_ub_read_ptr
    replace h_ub_read_ptr := h_ub_read_ptr.1.2.1.2.1

    have := LoadB.chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness h_opcode
    rw [this] at h_bus; clear this
    obtain ⟨ h_pc, h_rs1, hm0, hm1, hm2, hm3, h_rd ⟩ := h_bus; clear h_rd

    replace h_pc : state.regs.get? Register.PC = .some (BitVec.ofNat 32 ↑(air.adapter.from_state.pc row 0))
      := by
        clear *- h_pc
        simp [Sail.readReg, PreSail.readReg] at h_pc
        cases h : (state.regs.get? Register.PC) <;> simp_all
    rw [← rX_read_xreg_equiv
          (rd := Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0))
          (rd_idx := regidx.Regidx (BitVec.ofNat 5 (Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0))))
          (h_rd := rfl)] at h_rs1

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV32D.Functions.execute,
      *
    ]

    have h_r1_val := rX_bits_write_other_reg_state (val := (BitVec.ofNat 32 ↑(air.adapter.from_state.pc row 0)) + 4#32) h_rs1 reg_of_fin_neq_nextPC
    simp at h_rs1 h_r1_val

    have h_mem_ptr := LoadB.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    rw [add_comm] at h_mem_ptr; simp at h_mem_ptr

    have next_gma := gma_invariant_under_pc_increment h_general_assumptions (val := (BitVec.ofNat 32 ↑(air.adapter.from_state.pc row 0)) + 4#32)
    obtain ⟨ h_htif, h_priv, h_mprv , h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned ⟩ := next_gma
    subst rd_ptr rs1_ptr imm rd rs1 imm

    have ⟨ rd_div_4, rd_ub_128 ⟩ := LoadB.rd_rs2_ptr_div_4_under_128 air row h_is_valid h_bus_wellformedness h_opcode

    simp [LeanRV32D.Functions.execute_LOAD, LeanRV32D.Functions.vmem_read, EStateM.map, *]
    simp [LeanRV32D.Functions.vmem_read_addr, ExceptT.run, *, -BitVec.toNat_add]
    rw [if_pos]
    . simp [*, -BitVec.toNat_add]
      rw [if_neg (by omega)]
      rw [Nat.mod_eq_of_lt (by omega)]
      simp [*]
      simp [← BitVec.toNat_inj] at h_mem_ptr
      rw [Nat.mod_eq_of_lt (by omega)] at h_mem_ptr
      rw [← LoadB.imm_extend_12_to_16 air row h_bus_wellformedness h_is_valid h_opcode] at h_mem_ptr
      by_cases h_rd_z : air.adapter.rd_rs2_ptr row 0 = 0
      . specialize effect_z h_rd_z
        simp [h_is_valid] at effect_z
        simp [← h_mem_ptr, effect_z]
        have eq_mem_ptr : air.adapter.mem_ptr row 0 = air.read_ptr row 0 + air.shift_amount row 0
          := by simp [LoadB.read_ptr_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness]
        simp [eq_mem_ptr]; clear eq_mem_ptr
        obtain ⟨ sh, lsh, rsh ⟩ := LoadB.shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
        rw [sh]; clear sh lsh rsh
        split_ifs
        . simp [write_reg_state, LeanRV32D.Functions.wX_bits, LeanRV32D.Functions.wX, *]
        . rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
          simp [write_reg_state, LeanRV32D.Functions.wX_bits, LeanRV32D.Functions.wX, *]
        . rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
          simp [write_reg_state, LeanRV32D.Functions.wX_bits, LeanRV32D.Functions.wX, *]
        . rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
          simp [write_reg_state, LeanRV32D.Functions.wX_bits, LeanRV32D.Functions.wX, *]
      . specialize effect_nz h_rd_z
        simp [h_is_valid] at effect_nz
        simp [← h_mem_ptr, effect_nz]
        have eq_mem_ptr : air.adapter.mem_ptr row 0 = air.read_ptr row 0 + air.shift_amount row 0
          := by simp [LoadB.read_ptr_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness]
        simp [eq_mem_ptr]; clear eq_mem_ptr
        obtain ⟨ sh, lsh, rsh ⟩ := LoadB.shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
        rw [sh]; clear sh lsh rsh
        split_ifs
        . simp [write_reg_state, *]
          rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_rs2_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_rd_z ⊢; omega⟩) (h_rd := by simp)]
          simp [write_xreg, Sail.writeReg, PreSail.writeReg, cast]
          rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; clear *- this; grind)]
          congr; clear *- hm0; grind
        . rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
          simp [write_reg_state, *]
          rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_rs2_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_rd_z ⊢; omega⟩) (h_rd := by simp)]
          simp [write_xreg, Sail.writeReg, PreSail.writeReg, cast]
          rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; clear *- this; grind)]
          congr; clear *- hm1; grind
        . rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
          simp [write_reg_state, *]
          rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_rs2_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_rd_z ⊢; omega⟩) (h_rd := by simp)]
          simp [write_xreg, Sail.writeReg, PreSail.writeReg, cast]
          rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; clear *- this; grind)]
          congr; clear *- hm2; grind
        . rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
          simp [write_reg_state, *]
          rw [wX_write_xreg_non_zero_equiv (rd := ⟨ (Transpiler.wrap_to_regidx (air.adapter.rd_rs2_ptr row 0)).val, by simp [Transpiler.wrap_to_regidx] at h_rd_z ⊢; omega⟩) (h_rd := by simp)]
          simp [write_xreg, Sail.writeReg, PreSail.writeReg, cast]
          rw [ExtDHashMap.insert_comm (h_neq := by have := @reg_of_fin_neq_nextPC; clear *- this; grind)]
          congr; clear *- hm3; grind
    . rw [LoadB.imm_extend_12_to_16 air row h_bus_wellformedness h_is_valid h_opcode]
      simp [← h_mem_ptr, -BitVec.toNat_add]; rw [BitVec.toNat_add]; simp
      simp [LoadB.read_ptr_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness] at h_ub_read_ptr assumption_alignment
      obtain ⟨ sh, lsh, rsh ⟩ := LoadB.shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
      rw [sh] at h_ub_read_ptr assumption_alignment; clear sh lsh rsh
      clear *- h_ub_read_ptr assumption_alignment h_pma_size
      split_ifs at h_ub_read_ptr <;> simp_all
      . omega
      . repeat rw [Int.emod_eq_of_lt (by grind) (by grind)]
        rw [Nat.mod_eq_of_lt (by grind)]
        rw [Fin.sub_val_of_le] at assumption_alignment
        . rw [Fin.sub_val_of_le (by omega)] at h_ub_read_ptr
          omega
        . simp [Fin.sub_def] at h_ub_read_ptr
          omega
      . repeat rw [Int.emod_eq_of_lt (by grind) (by grind)]
        rw [Nat.mod_eq_of_lt (by grind)]
        rw [Fin.sub_val_of_le] at assumption_alignment
        . rw [Fin.sub_val_of_le (by omega)] at h_ub_read_ptr
          omega
        . simp [Fin.sub_def] at h_ub_read_ptr
          omega
      . repeat rw [Int.emod_eq_of_lt (by grind) (by grind)]
        rw [Nat.mod_eq_of_lt (by grind)]
        rw [Fin.sub_val_of_le] at assumption_alignment
        . rw [Fin.sub_val_of_le (by omega)] at h_ub_read_ptr
          omega
        . simp [Fin.sub_def] at h_ub_read_ptr
          omega

  end LoadSignExtend

end RV32IM.Equivalence
