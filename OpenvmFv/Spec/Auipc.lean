import Mathlib

import OpenvmFv.Airs.Branch.VmAirWrapper_auipc
import OpenvmFv.Constraints.VmAirWrapper_auipc
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_auipc FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_auipc.constraints.allHold air row row_in_range)

namespace Auipc.NonValidRows

open VmAirWrapper_auipc.constraints

variable (row_not_valid : air.core.is_valid row 0 = 0)

include
  row_in_range
  row_not_valid
in
/-- Zeros required to form a non-valid row -/
lemma non_valid_row_auipc_allZeros_allHold
:
  constrain_interactions air ∧
  air.core.imm_limbs_0 = 0 ∧
  air.core.imm_limbs_1 = 0 ∧
  air.core.imm_limbs_2 = 0 ∧
  air.core.pc_limbs_0 = 0 ∧
  air.core.pc_limbs_1 = 0 ∧
  air.core.rd_data_0 row 0 = 0 ∧
  air.core.rd_data_1 row 0 = 0 ∧
  air.core.rd_data_2 row 0 = 0 ∧
  air.core.rd_data_3 row 0 = 0
    → allHold air row row_in_range
:= by
  rw [allHold_simplified_of_allHold]
  simp_all [VmAirWrapper_auipc_constraint_and_interaction_simplification]

include
  row_not_valid
in
/-- On non-valid rows, all interaction multiplicities equal zero -/
lemma non_valid_row_auipc_all_interaction_multiplicities_zero
:
  forall entry,
  entry ∈ busRow air row → entry.1 = 0
:= by
  simp_all [VmAirWrapper_auipc_constraint_and_interaction_simplification]

end Auipc.NonValidRows

open VmAirWrapper_auipc.constraints

namespace Auipc.ValidRows

variable (row_valid : air.core.is_valid row 0 = 1)

-- Row assumptions, properties to assume, and properties to prove
variable
  (assumptions : assumptionsPerRow air row)
  (propertiesToAssume : wf_propertiesToAssumePerRow air row)

section General

include
  row_valid
  propertiesToAssume
in
/-- The properties that need to be proven actually hold -/
lemma wf_propertiesToAssert
:
  wf_propertiesToAssertPerRow air row
:= by
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_auipc_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read pa_bit

  replace pa_read := readInstructionBus_properties_of_opcode_bounds _ (by simp) pa_read
  simp [VmAirWrapper_auipc_constraint_and_interaction_simplification] at pa_read

  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rd, ub_prev_0, ub_prev_1, ub_prev_2, ub_prev_3 ⟩ := pa_mem
  clear pa_range

  simp_all [VmAirWrapper_auipc_constraint_and_interaction_simplification]

include
  row_valid
  constraints
  assumptions
  propertiesToAssume in
/-- The constraints entail correct implementation
    of the `auipc` opcode
--/
theorem spec_auipc
:
  U32.toBV #v[(air.core.rd_data_0 row 0).val,
              (air.core.rd_data_1 row 0).val,
              (air.core.rd_data_2 row 0).val,
              (air.core.rd_data_3 row 0).val]
    =
  BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val +
  (BitVec.ofNat 20 ↑(air.core.imm row 0) ++ 0#12)

:= by
  -- rd_data represents limbs of rd
  -- pc_limbs are limbs of pc except the most and least significant limbs
  -- imm_limbs are limbs of imm except the least significant limb

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  rw [allHold_simplified_of_allHold] at constraints
  simp [row_valid, VmAirWrapper_auipc_constraint_and_interaction_simplification]
    at pa_exec pa_mem pa_range pa_read pa_bit assumptions constraints

  replace pa_read := readInstructionBus_properties_of_opcode_bounds _ (by simp) pa_read

  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit assumptions constraints
  obtain ⟨ ub_rd, ub_prev_0, ub_prev_1, ub_prev_2, ub_prev_3 ⟩ := pa_mem
  clear pa_range

  clear assumptions
  obtain ⟨ ub_rd0, ub_rd1, ub_rd2, ub_rd3, ub_imm0, ub_imm1, ub_imm2, ub_pc0, ub_pc1, ub_pc_msl ⟩ := pa_bit
  obtain ⟨ constrain_instructions, h_cry1, h_cry2, h_cry3, rest ⟩ := constraints; clear rest

  have := Rv32AuipcCoreAir.imm_def air.core row 0

  have ⟨ eq_imm0, eq_imm1, eq_imm2 ⟩
  :
    (air.core.imm_limbs_0 row 0).val = (air.core.imm row 0).val % 256 ∧
    (air.core.imm_limbs_1 row 0).val = ((air.core.imm row 0).val / 256) % 256 ∧
    (air.core.imm_limbs_2 row 0).val = ((air.core.imm row 0).val / 65536) % 256
  := by
  have := Rv32AuipcCoreAir.imm_def air.core row 0







end General

end Auipc.ValidRows
