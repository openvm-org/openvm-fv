import OpenvmFv.RV32D.add
import OpenvmFv.RV32D.sub
import OpenvmFv.RV32D.xor
import OpenvmFv.RV32D.or
import OpenvmFv.RV32D.and
import OpenvmFv.RV32D.addi
import OpenvmFv.RV32D.andi
import OpenvmFv.RV32D.ori
import OpenvmFv.RV32D.xori

import OpenvmFv.Equivalence.BaseALU

namespace RV32IM.Equivalence

  section base_ALU

    open VmAirWrapper_alu.constraints
    open Equivalence.BaseALU

    attribute [local simp]
      _executionBus_row
      _memoryBus_row
      executionBus_row
      memoryBus_row
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
      (h_constraints : VmAirWrapper_alu.constraints.allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_axioms : VmAirWrapper_alu.constraints.axiomsPerRow air row)
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
        congr; symm
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
      let rs1_ptr := (_memoryBus_row air row)[0]!.ptr
      let rs2_ptr := (_memoryBus_row air row)[2]!.ptr
      let rd_ptr := (_memoryBus_row air row)[4]!.ptr
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
      let rs1_ptr := (_memoryBus_row air row)[0]!.ptr
      let imm := (_memoryBus_row air row)[2]!.ptr
      let rd_ptr := (_memoryBus_row air row)[4]!.ptr
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
      let rs1_ptr := (_memoryBus_row air row)[0]!.ptr
      let rs2_ptr := (_memoryBus_row air row)[2]!.ptr
      let rd_ptr := (_memoryBus_row air row)[4]!.ptr
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
      let rs1_ptr := (_memoryBus_row air row)[0]!.ptr
      let rs2_ptr := (_memoryBus_row air row)[2]!.ptr
      let rd_ptr := (_memoryBus_row air row)[4]!.ptr
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
      let rs1_ptr := (_memoryBus_row air row)[0]!.ptr
      let imm := (_memoryBus_row air row)[2]!.ptr
      let rd_ptr := (_memoryBus_row air row)[4]!.ptr
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.ITYPE (imm, r1, rd, iop.XORI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_imm_proof

    theorem equiv_AND
      (h_opcode : (air.core.ctx row 0).instruction.opcode = 516)
      (h_imm : air.adapter.rs2_as row 0 = 1)
    :
      let rs1_ptr := (_memoryBus_row air row)[0]!.ptr
      let rs2_ptr := (_memoryBus_row air row)[2]!.ptr
      let rd_ptr := (_memoryBus_row air row)[4]!.ptr
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
      let rs1_ptr := (_memoryBus_row air row)[0]!.ptr
      let imm := (_memoryBus_row air row)[2]!.ptr
      let rd_ptr := (_memoryBus_row air row)[4]!.ptr
      let r1 : regidx := ⟨ (Transpiler.wrap_to_regidx rs1_ptr).val, by simp ⟩
      let imm : BitVec 12 := BitVec.ofNat 12 imm.toNat
      let rd : regidx := ⟨ (Transpiler.wrap_to_regidx rd_ptr).val, by simp ⟩
      let instr : instruction := instruction.ITYPE (imm, r1, rd, iop.ANDI)
      execute_instruction instr state =
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2
    := by alu_imm_proof

  end base_ALU

end RV32IM.Equivalence
