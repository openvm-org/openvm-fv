import Mathlib

import OpenvmFv.Airs.Branch.VmAirWrapper_jallui
import OpenvmFv.Constraints.VmAirWrapper_jallui
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

namespace JalLui.NonValidRows

open VmAirWrapper_jallui.constraints

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_jallui FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_jallui.constraints.allHold air row row_in_range)

variable (row_not_valid : (executionBus_row air row)[0]!.1 = 0)

include
  row_not_valid
  constraints
in
/-- On non-valid rows, all interaction multiplicities
    on the execution, memory, and program buses
    equal zero -/
lemma non_valid_row_exec_mem_program_multiplicities_zero
:
  forall entry,
  entry ∈
    executionBus_row air row
     ++ memoryBus_row air row
     ++ programBus_row air row
    → entry.1 = 0
:= by
  rw [allHold_simplified_of_allHold] at constraints
  simp_all [VmAirWrapper_jallui_constraint_and_interaction_simplification]

end JalLui.NonValidRows

namespace JalLui.ValidRows

open VmAirWrapper_jallui.constraints

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_jallui FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_jallui.constraints.allHold air row row_in_range)
variable (axioms : axiomsPerRow air row)
variable (propertiesToAssume : wf_propertiesToAssumePerRow air row)

variable (row_valid : (executionBus_row air row)[0]!.1 = -1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2_000_000 in
include
  row_valid
  constraints
  axioms
  propertiesToAssume
in
/-- The properties that need to be proven actually hold -/
lemma wf_propertiesToAssert
:
  wf_propertiesToAssertPerRow air row
:= by
  simp [executionBus_row] at row_valid
  rw [allHold_simplified_of_allHold] at constraints

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  clear pa_range pa_read
  simp [row_valid,
        VmAirWrapper_jallui_constraint_and_interaction_simplification,
        and_assoc,
        Interaction.ProgramBusEntry.operand_properties]
    at axioms pa_exec pa_mem pa_bit constraints ⊢
  grind

section General

include
  row_valid
  constraints
  axioms
  propertiesToAssume in
/-- The constraints entail correct implementation
    of the `auipc` opcode
--/
theorem spec_lui
  (h_lui : air.core.expected_opcode row 0 = 561)
:
  U32.toBV #v[(air.core.rd_data_0 row 0).val,
              (air.core.rd_data_1 row 0).val,
              (air.core.rd_data_2 row 0).val,
              (air.core.rd_data_3 row 0).val]
    =
  (BitVec.ofNat 20 ((air.core.imm row 0).val) ++ 0#12)
:= by
  simp [VmAirWrapper_jallui_constraint_and_interaction_simplification] at row_valid
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  rw [allHold_simplified_of_allHold] at constraints
  clear pa_mem pa_range
  simp [row_valid, VmAirWrapper_jallui_constraint_and_interaction_simplification]
    at pa_exec pa_read pa_bit axioms constraints
  simp [Interaction.ProgramBusEntry.operand_properties] at pa_read
  obtain ⟨ instruction, multiplicity, data, h_transpile,
           hm, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8 ⟩ := pa_read
  have h_alignment := Transpiler.pc_aligned_of_some h_transpile
  have h_bound := Transpiler.pc_bound_of_some h_transpile
  obtain ⟨ imm, rd, eq_instr, nz_rd ⟩ := Transpiler.transpiler_opcode_561 h_transpile (by grind)
  subst instruction; dsimp [Transpiler.transpile_op] at h_transpile
  rw [if_pos (by grind)] at h_transpile
  split_ifs at h_transpile with z_rd
  all_goals
    simp [-Vector.mk_eq] at h_transpile
    obtain ⟨ hm, hdata ⟩ := h_transpile
    subst data; simp at *
  obtain ⟨ h_lui, h_jal ⟩ : air.core.is_jal row 0 = 0 ∧ air.core.is_lui row 0 = 1
  := by
    rw [← Rv32JalLuiCoreAir_4.is_valid_def] at row_valid
    rw [← Rv32JalLuiCoreAir_4.expected_opcode_def] at h_lui
    grind
  simp [h_lui, and_assoc] at pa_bit
  obtain ⟨ ub_rd0, ub_rd1, ub_rd2, ub_rd3 ⟩ := pa_bit
  simp [← BitVec.toNat_inj, U32.toNat]
  rw [BitVec.toNat_append]
  simp [Nat.shiftLeft_eq_mul_pow]
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
  have ub_imm : (air.core.imm row 0).val < 1048576
  := by
    simp [← hd4, Transpiler.utof]
    omega
  rw [Nat.mod_eq_of_lt ub_imm]
  simp_all
  trans (air.core.imm row 0 * 16).val * 256
  . rw [← constraints.2.2.1,
        ← Rv32JalLuiCoreAir_4.intermed_val_def]
    grind
  . grind

end General

end JalLui.ValidRows
