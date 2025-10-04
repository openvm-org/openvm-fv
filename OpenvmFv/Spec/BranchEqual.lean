import Mathlib

import OpenvmFv.Airs.Branch.VmAirWrapper_branch_eq
import OpenvmFv.Constraints.VmAirWrapper_branch_eq
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_branch_eq.constraints.allHold air row row_in_range)

namespace BranchEqual.NonValidRows

open VmAirWrapper_branch_eq.constraints

variable (row_not_valid : air.core.is_valid row 0 = 0)

include
  row_in_range
in
/-- Zeros required to form a non-valid row -/
lemma non_valid_row_BranchEqual_allZeros_allHold
:
  constrain_interactions air ∧
  air.core.a_0 row 0 = 0 ∧
  air.core.a_1 row 0 = 0 ∧
  air.core.a_2 row 0 = 0 ∧
  air.core.a_3 row 0 = 0 ∧
  air.core.b_0 row 0 = 0 ∧
  air.core.b_1 row 0 = 0 ∧
  air.core.b_2 row 0 = 0 ∧
  air.core.b_3 row 0 = 0 ∧
  air.core.cmp_result row 0 = 0 ∧
  air.core.opcode_beq_flag row 0 = 0 ∧
  air.core.opcode_bne_flag row 0 = 0 ∧
  air.core.diff_inv_marker_0 row 0 = 0 ∧
  air.core.diff_inv_marker_1 row 0 = 0 ∧
  air.core.diff_inv_marker_2 row 0 = 0 ∧
  air.core.diff_inv_marker_3 row 0 = 0
    → air.core.is_valid row 0 = 0 ∧
      allHold air row row_in_range
:= by
  rw [allHold_simplified_of_allHold]
  simp_all; intros
  simp_all [VmAirWrapper_branch_eq_constraint_and_interaction_simplification,
            Valid_BranchEqualCoreAir_4.is_valid]

include
  row_not_valid
in
/-- On non-valid rows, all interactin multiplicities equal zero -/
lemma non_valid_row_BranchEqual_all_interaction_multiplicities_zero
:
  forall entry,
  entry ∈ busRow air row → entry.1 = 0
:= by
  simp_all [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]

end BranchEqual.NonValidRows


open VmAirWrapper_branch_eq.constraints

namespace BranchEqual.ValidRows

variable (row_valid : air.core.is_valid row 0 = 1)

-- Row assumptions, properties to assume, and properties to prove
variable
  (assumptions : assumptionsPerRow air row)
  (propertiesToAssume : wf_propertiesToAssumePerRow air row)

section General

include
  row_valid
  constraints
  propertiesToAssume
in
/-- The properties that need to be proven actually hold -/
lemma wf_propertiesToAssert
:
  wf_propertiesToAssertPerRow air row
:= by
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read

  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := readInstructionBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at pa_read

  rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read
  obtain ⟨ ub_rs1, ub_a0, ub_a1, ub_a2, ub_a3, ub_rs2, ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := pa_mem
  obtain ⟨ ri_rs1, ri_rs2, lb_imm, ub_imm ⟩ := pa_read
  clear pa_exec pa_range

  have ⟨ sop0, sop1 ⟩ := single_op air row row_in_range constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp_all [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]

include
  row_valid
  assumptions
  constraints
  propertiesToAssume
in
/-- Some properties more important than others that should
    be easily accessible -/
lemma essentials
:
  (air.adapter.from_state.pc row 0).val < 1073741824 ∧
  (air.to_pc row 0).val < 1073741824 ∧
  (air.adapter.from_state.timestamp row 0) + 2 < 536870912 ∧
  List.Forall (fun x => x.val < 256)
    [air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0,
     air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0] ∧
  (air.core.expected_opcode row 0 = 544 ∨
   air.core.expected_opcode row 0 = 545) ∧
  (-2^12 ≤ BabyBear.toInt (air.core.imm row 0) ∧ BabyBear.toInt (air.core.imm row 0) < 2^12)
:= by
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read

  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := readInstructionBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at pa_read

  rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read
  obtain ⟨ ub_rs1, ub_a0, ub_a1, ub_a2, ub_a3, ub_rs2, ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := pa_mem
  obtain ⟨ ri_rs1, ri_rs2, lb_imm, ub_imm ⟩ := pa_read
  clear pa_exec pa_range

  simp [row_valid, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at assumptions
  clear constraints; simp_all
  split_ands <;> omega

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail the correct change
    of the `pc` for BEQ/BNE
--/
theorem spec_BEQ_BNE_pc
:
  (air.core.expected_opcode row 0 = 544 →
    air.to_pc row 0 =
      if U32.toBV #v[(air.core.a_0 row 0).val,
                    (air.core.a_1 row 0).val,
                    (air.core.a_2 row 0).val,
                    (air.core.a_3 row 0).val]
          ==
        U32.toBV #v[(air.core.b_0 row 0).val,
                    (air.core.b_1 row 0).val,
                    (air.core.b_2 row 0).val,
                    (air.core.b_3 row 0).val]
      then air.adapter.from_state.pc row 0 + air.core.imm row 0
      else air.adapter.from_state.pc row 0 + 4) ∧
  (air.core.expected_opcode row 0 = 545 →
    air.to_pc row 0 =
      if U32.toBV #v[(air.core.a_0 row 0).val,
                    (air.core.a_1 row 0).val,
                    (air.core.a_2 row 0).val,
                    (air.core.a_3 row 0).val]
          !=
        U32.toBV #v[(air.core.b_0 row 0).val,
                    (air.core.b_1 row 0).val,
                    (air.core.b_2 row 0).val,
                    (air.core.b_3 row 0).val]
      then air.adapter.from_state.pc row 0 + air.core.imm row 0
      else air.adapter.from_state.pc row 0 + 4)
:= by
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read

  -- Get all opcode properties
  obtain ⟨ sop0, sop1 ⟩ := single_op air row row_in_range constraints
  obtain ⟨ op0, op1 ⟩ := op_from_opcode air row row_in_range constraints row_valid
  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := readInstructionBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at pa_read

  rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read
  obtain ⟨ ub_rs1, ub_a0, ub_a1, ub_a2, ub_a3, ub_rs2, ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := pa_mem
  obtain ⟨ ri_rs1, ri_rs2, lb_imm, ub_imm ⟩ := pa_read
  clear pa_exec pa_range

  -- Prepare constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at *
  obtain ⟨ constrain_interactions,
           b_beq, b_bne, b_is_valid, b_cmp,
           cmp_0, cmp_1, cmp_2, cmp_3, sum, rest ⟩ := constraints
  clear constrain_interactions rest

  rw [← VmAirWrapper_branch_eq.to_pc_def] at *
  rw [← BranchEqualCoreAir_4.sum_def] at *
  rw [← BranchEqualCoreAir_4.cmp_eq_def] at *

  split_ands <;> intro h_opcode <;> simp_all

  all_goals
    rcases b_cmp with h_cmp | h_cmp <;> simp_all
    . intro h_eq
      have : air.core.a_0 row 0 = air.core.b_0 row 0 ∧
            air.core.a_1 row 0 = air.core.b_1 row 0 ∧
            air.core.a_2 row 0 = air.core.b_2 row 0 ∧
            air.core.a_3 row 0 = air.core.b_3 row 0
      := by
        simp [← BitVec.toNat_inj, U32.toNat] at h_eq
        grind
      simp_all

end General

end BranchEqual.ValidRows
