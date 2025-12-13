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

variable (row_not_valid : (executionBus_row air row)[0]!.1 = 0)

omit
  [Field ExtF]
include
  row_not_valid
in
/-- On non-valid rows, all interactin multiplicities
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
  simp_all [VmAirWrapper_auipc_constraint_and_interaction_simplification]

end Auipc.NonValidRows

open VmAirWrapper_auipc.constraints

namespace Auipc.ValidRows

variable (row_valid : air.core.is_valid row 0 = 1)

-- Row axioms, properties to assume, and properties to prove
variable
  (axioms : axiomsPerRow air row)
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

  replace pa_read := programBus_properties_of_opcode_bounds _ (by simp) pa_read
  simp [VmAirWrapper_auipc_constraint_and_interaction_simplification] at pa_read

  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rd, ub_prev_0, ub_prev_1, ub_prev_2, ub_prev_3 ⟩ := pa_mem
  clear pa_range

  simp_all [VmAirWrapper_auipc_constraint_and_interaction_simplification]

include
  row_valid
  constraints
  axioms
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
BitVec.ofNat 32 ↑(air.adapter.from_state.pc row 0) +
(BitVec.ofNat 20 ((air.core.imm row 0).val >>> 4) ++ 0#12)

:= by
  -- rd_data represents limbs of rd
  -- pc_limbs are limbs of pc except the most and least significant limbs
  -- imm_limbs are limbs of imm except the least significant limb
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  rw [allHold_simplified_of_allHold] at constraints
  simp [row_valid, VmAirWrapper_auipc_constraint_and_interaction_simplification]
    at pa_exec pa_mem pa_range pa_read pa_bit axioms constraints

  replace pa_read := programBus_properties_of_opcode_bounds _ (by simp) pa_read

  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit axioms constraints
  obtain ⟨ ub_rd, ub_prev_0, ub_prev_1, ub_prev_2, ub_prev_3 ⟩ := pa_mem

  obtain ⟨ ub_rd0, ub_rd1, ub_rd2, ub_rd3, ub_imm0, ub_imm1, ub_imm2, ub_pc0, ub_pc1, ub_pc_msl ⟩ := pa_bit
  obtain ⟨ constrain_instructions, h_cry1, h_cry2, h_cry3, rest ⟩ := constraints; clear constrain_instructions rest

  simp [VmAirWrapper_auipc_constraint_and_interaction_simplification] at pa_read
  obtain ⟨ ub_imm, imm_mod ⟩ := pa_read

  trans BitVec.ofNat 32 ↑(air.adapter.from_state.pc row 0) + ((BitVec.ofNat 24 (air.core.imm row 0).val) ++ 0#8); rotate_left
  . clear *- ub_imm imm_mod
    simp [Fin.lt_def] at ub_imm
    simp [Fin.ext_iff] at imm_mod
    obtain ⟨ x, eq_x ⟩ : ∃ x, (air.core.imm row 0).val = x := by simp
    simp_all; clear *- ub_imm imm_mod
    simp [← BitVec.toNat_inj]
    repeat rw [BitVec.toNat_append]; simp
    omega
  . have ub_msl : (air.core.pc_msl row 0 (air.adapter.from_state.pc row 0)).val < 64
      := by
        have ub_msl :
          (air.core.pc_msl row 0 (air.adapter.from_state.pc row 0)).val < 64 ∨
          ((503316481 ≤ (air.core.pc_msl row 0 (air.adapter.from_state.pc row 0)).val) ∧
           ((air.core.pc_msl row 0 (air.adapter.from_state.pc row 0)).val ≤ 503316544)) ∨
          ((1006632961 ≤ (air.core.pc_msl row 0 (air.adapter.from_state.pc row 0)).val) ∧
           ((air.core.pc_msl row 0 (air.adapter.from_state.pc row 0)).val ≤ 1006633024)) ∨
          ((1509949441 ≤ (air.core.pc_msl row 0 (air.adapter.from_state.pc row 0)).val) ∧
           ((air.core.pc_msl row 0 (air.adapter.from_state.pc row 0)).val ≤ 1509949504))
        := by
          clear *- ub_pc_msl
          simp [Fin.val_mul] at ub_pc_msl
          obtain ⟨ x, ⟨ eq_x, ub_x ⟩ ⟩ : ∃ x, (air.core.pc_msl row 0 (air.adapter.from_state.pc row 0)).val = x ∧ x < BB_prime := by simp
          rw [eq_x] at ub_pc_msl ⊢
          grind
        rcases ub_msl with ub_msl | ub_msl
        . assumption
        . exfalso
          simp [← VmAirWrapper_auipc.carry_1_def,
                ← VmAirWrapper_auipc.carry_2_def,
                ← VmAirWrapper_auipc.carry_3_def] at *
          rcases h_cry1 <;>
          rcases h_cry2 <;>
          rcases h_cry3 <;>
          simp_all <;>
          omega
    clear ub_pc_msl

    obtain ⟨ hl, hh ⟩ :
      air.core.intermed_val row 0 = (air.adapter.from_state.pc row 0) % 16777216 ∧
      2013265801 * (air.adapter.from_state.pc row 0 - air.core.intermed_val row 0) = (air.adapter.from_state.pc row 0) / 16777216
    := by
      have : (air.core.intermed_val row 0).val < 16777216
        := by rw [← Rv32AuipcCoreAir.intermed_val_def]; grind
      rw [Valid_Rv32AuipcCoreAir.pc_msl] at *
      exact @BabyBear.inv2_24_prod_diff_div_mod
              _
              (air.adapter.from_state.pc row 0)
              this
              (by rw [mul_comm] at ub_msl; omega)

    have eq_pc :
      BitVec.ofNat 32 ↑(air.adapter.from_state.pc row 0) =
        U32.toBV
          #v[(air.core.rd_data_0 row 0).val,
              (air.core.pc_limbs_0 row 0).val,
              (air.core.pc_limbs_1 row 0).val,
              (air.core.pc_msl row 0 (air.adapter.from_state.pc row 0)).val]
      := by
        simp [← BitVec.toNat_inj, U32.toNat]
        repeat rw [Nat.mod_eq_of_lt (by omega)]
        rw [Valid_Rv32AuipcCoreAir.pc_msl] at *
        rw [mul_comm (b := 2013265801)] at ub_msl ⊢
        rw [hh] at ub_msl ⊢; clear hh
        rw [← Rv32AuipcCoreAir.intermed_val_def, ← add_assoc] at hl
        have ub_pc := axioms.1; simp [Fin.lt_def] at ub_pc
        clear *- ub_rd0 ub_pc ub_pc0 ub_pc1 hl
        simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at hl
        rw [Nat.mod_eq_of_lt (by omega)] at hl
        symm; rw [hl, add_comm, mul_comm]
        apply Nat.div_add_mod

    rw [eq_pc]; clear eq_pc hl hh

    have eq_imm :
      ((BitVec.ofNat 24 (air.core.imm_limbs_0 row 0 + air.core.imm_limbs_1 row 0 * 256 + air.core.imm_limbs_2 row 0 * 65536).val) ++ 0#8).toNat =
        (U32.toBV
          #v[0,
             (air.core.imm_limbs_0 row 0).val,
             (air.core.imm_limbs_1 row 0).val,
             (air.core.imm_limbs_2 row 0).val]).toNat
      := by
        rw [BitVec.toNat_append]
        simp [U32.toNat]
        repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
        simp [Fin.val_add, Fin.val_mul]
        rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
        rw [Nat.mod_eq_of_lt (b := 16777216) (by omega)]
        omega

    have := Rv32AuipcCoreAir.imm_def air.core row 0; symm at this
    rw [this] at *; clear this
    simp [← BitVec.toNat_inj, -BitVec.toNat_add]
    repeat rw [BitVec.toNat_add]
    simp [eq_imm]

    clear pa_range axioms
          ub_prev_0 ub_prev_1 ub_prev_2 ub_prev_3
          eq_imm ub_imm imm_mod

    simp [← VmAirWrapper_auipc.carry_1_def,
          ← VmAirWrapper_auipc.carry_2_def,
          ← VmAirWrapper_auipc.carry_3_def] at *

    simp [U32.toNat]
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
    rcases h_cry1 <;> rcases h_cry2 <;>
    rcases h_cry3 <;> simp_all <;> omega

end General

end Auipc.ValidRows
