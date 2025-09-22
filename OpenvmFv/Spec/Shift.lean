import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_shift
import OpenvmFv.Constraints.VmAirWrapper_shift
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000
set_option synthInstance.maxHeartbeats 1_000_000

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_shift FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_shift.constraints.allHold air row row_in_range)

namespace Shift.NonValidRows

open VmAirWrapper_shift.constraints

variable (row_not_valid : air.core.is_valid row 0 = 0)

set_option maxRecDepth 1_000_000 in
include
  row_in_range
in
/-- Zeros required to form a non-valid row -/
lemma non_valid_row_Shift_allZeros_allHold
:
  constrain_interactions air ∧
  air.adapter.rs2 row 0 = 0 ∧
  air.adapter.rs2_as row 0 = 0 ∧
  air.core.b_0 row 0 = 0 ∧
  air.core.b_1 row 0 = 0 ∧
  air.core.b_2 row 0 = 0 ∧
  air.core.b_3 row 0 = 0 ∧
  air.core.c_0 row 0 = 0 ∧
  air.core.c_1 row 0 = 0 ∧
  air.core.c_2 row 0 = 0 ∧
  air.core.c_3 row 0 = 0 ∧
  air.core.opcode_sll_flag row 0 = 0 ∧
  air.core.opcode_srl_flag row 0 = 0 ∧
  air.core.opcode_sra_flag row 0 = 0 ∧
  air.core.bit_multiplier_left row 0 = 0 ∧
  air.core.bit_multiplier_right row 0 = 0 ∧
  air.core.b_sign row 0 = 0 ∧
  air.core.bit_shift_marker_0 row 0 = 0 ∧
  air.core.bit_shift_marker_1 row 0 = 0 ∧
  air.core.bit_shift_marker_2 row 0 = 0 ∧
  air.core.bit_shift_marker_3 row 0 = 0 ∧
  air.core.bit_shift_marker_4 row 0 = 0 ∧
  air.core.bit_shift_marker_5 row 0 = 0 ∧
  air.core.bit_shift_marker_6 row 0 = 0 ∧
  air.core.bit_shift_marker_7 row 0 = 0 ∧
  air.core.limb_shift_marker_0 row 0 = 0 ∧
  air.core.limb_shift_marker_1 row 0 = 0 ∧
  air.core.limb_shift_marker_2 row 0 = 0 ∧
  air.core.limb_shift_marker_3 row 0 = 0 ∧
  air.core.bit_shift_carry_0 row 0 = 0 ∧
  air.core.bit_shift_carry_1 row 0 = 0 ∧
  air.core.bit_shift_carry_2 row 0 = 0 ∧
  air.core.bit_shift_carry_3 row 0 = 0
    → air.core.is_valid row 0 = 0 ∧
      allHold air row row_in_range
:= by
  rw [allHold_simplified_of_allHold]
  intro h_zeros
  simp [VmAirWrapper_shift_constraint_and_interaction_simplification,
        ← Valid_ShiftCoreAir_4_8.is_valid_def,
        ← Valid_ShiftCoreAir_4_8.right_shift_def,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_1,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_2,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_3,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_4,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_5,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_6,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_7,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_0_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_1_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_2_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_3_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_0_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_1_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_2_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_3_def,
        ← Valid_ShiftCoreAir_4_8.b_sign_shifted_def,
        ← VmAirWrapper_shift.rs2_imm_def,
        ← VmAirWrapper_shift.rs2_sign_limbs]
  grind

include
  row_in_range
  row_not_valid
  constraints
in
/-- On non-valid rows, all interactin multiplicities equal zero -/
lemma non_valid_row_Shift_all_interaction_multiplicities_zero
  (entry : FBB × List FBB)
:
  entry ∈ executionBus_row air row ++
          memoryBus_row air row ++
          rangeCheckerBus_row air row ++
          readInstructionBus_row air row ++
          bitwiseBus_row air row → entry.1 = 0
:= by
  obtain ⟨ hint, constraints ⟩ := constraints
  clear hint; unfold extracted_row_constraint_list at constraints
  simp only [VmAirWrapper_shift_air_simplification,
             VmAirWrapper_shift_constraint_and_interaction_simplification] at constraints
  simp at constraints
  have : air.adapter.rs2_as row 0 = 0 := by grind
  simp_all [VmAirWrapper_shift_constraint_and_interaction_simplification]
  simp_all [← Valid_ShiftCoreAir_4_8.is_valid_def,
            ← Valid_ShiftCoreAir_4_8.right_shift_def,
            ← Valid_ShiftCoreAir_4_8.expected_a_left_0_def,
            ← Valid_ShiftCoreAir_4_8.expected_a_left_1_def,
            ← Valid_ShiftCoreAir_4_8.expected_a_left_2_def,
            ← Valid_ShiftCoreAir_4_8.expected_a_left_3_def,
            ← Valid_ShiftCoreAir_4_8.expected_a_right_0_def,
            ← Valid_ShiftCoreAir_4_8.expected_a_right_1_def,
            ← Valid_ShiftCoreAir_4_8.expected_a_right_2_def,
            ← Valid_ShiftCoreAir_4_8.expected_a_right_3_def,
            ← Valid_ShiftCoreAir_4_8.b_sign_shifted_def,
            ← VmAirWrapper_shift.rs2_imm_def,
            ← VmAirWrapper_shift.rs2_sign_limbs]
  grind (splits := 37)

end Shift.NonValidRows

open VmAirWrapper_shift.constraints

namespace Shift.ValidRows

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
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_shift_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_bit
  repeat rw [Fin.ext_iff] at pa_mem pa_range pa_read pa_bit
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2n_c, ub_rs2p_c, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2_non_imm, ri_imm ⟩ := pa_read
  obtain ⟨ ba0, ba1, ba2, ba3, ba4, ba5 ⟩ := pa_bit
  clear pa_exec pa_range

  have ⟨ sop0, sop1, sop2 ⟩ := single_op air row row_in_range constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_shift_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           rest ⟩ := constraints
  clear constrain_interactions
  simp_all [VmAirWrapper_shift_constraint_and_interaction_simplification,
            wf_propertiesToAssertPerRow,
            propertiesToAssert]
  by_cases h_rs2_0 : air.adapter.rs2_as row 0 = 0 <;> simp_all
  . simp [Fin.ext_iff] at ub_rs2n_c
    assumption

include
  row_valid
  constraints
  propertiesToAssume
in
/-- Some properties more important than others that should
    be easily accessible -/
lemma essentials
:
  List.Forall (fun x => x.val < 256)
    [air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0,
     air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0,
     air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0] ∧
  ((air.core.ctx row 0).instruction.opcode = 517 ∨
   (air.core.ctx row 0).instruction.opcode = 518 ∨
   (air.core.ctx row 0).instruction.opcode = 519) ∧
  (air.adapter.rs2_as row 0 = 0 ∨ air.adapter.rs2_as row 0 = 1) ∧
  (air.adapter.rs2_as row 0 = 0 →
    (air.adapter.rs2 row 0).val < 16777216 ∧
    (air.adapter.rs2 row 0).val < 32 ∧
    (air.adapter.rs2_as row 0 = 0 ∨ air.adapter.rs2_as row 0 = 1) ∧
    air.adapter.rs2 row 0 = air.rs2_imm row 0 ∧
    air.rs2_sign row 0 = air.rs2_limbs row 0 3 ∧
    (air.core.c_2 row 0 = 0 ∨ air.core.c_2 row 0 = 255)) ∧
  ((air.core.bit_multiplier_left row 0).val ≤ 128) ∧
  ((air.core.bit_multiplier_right row 0).val ≤ 128) ∧
  ((air.core.bit_shift_carry_0 row 0).val < 128) ∧
  ((air.core.bit_shift_carry_1 row 0).val < 128) ∧
  ((air.core.bit_shift_carry_2 row 0).val < 128) ∧
  ((air.core.bit_shift_carry_3 row 0).val < 128)
:= by
  have assertedProperties := wf_propertiesToAssert _ air row row_in_range constraints row_valid propertiesToAssume
  obtain ⟨ pa_exec, pa_mem, rest ⟩ := assertedProperties
  clear pa_exec rest
  simp [row_valid,
        VmAirWrapper_shift_constraint_and_interaction_simplification,
        propertiesToAssert,
        and_assoc] at pa_mem

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_shift_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_bit

  repeat rw [Fin.ext_iff] at pa_mem pa_range pa_read pa_bit
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2n_c, ub_rs2p_c, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2_non_imm, ri_imm ⟩ := pa_read
  obtain ⟨ ra0, ra1, ra2, ra3, ra4, ra5, ra6, ra7, ra8, rest ⟩ := pa_range; clear rest
  obtain ⟨ ba0, ba1, ba2, ba3, ba4, ba5 ⟩ := pa_bit
  clear pa_exec

  -- Get all opcode properties
  obtain ⟨ sop0, sop1, sop2 ⟩ := single_op air row row_in_range constraints
  obtain ⟨ op0, op1 ⟩ := op_from_opcode air row row_in_range constraints row_valid
  have opcodes := opcode_bounds air row row_in_range constraints row_valid

  -- Get relevant constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_shift_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions, rest ⟩ := constraints
  clear constrain_interactions

  have b_rs2_as : (air.adapter.rs2_as row 0 = 0 ∨ air.adapter.rs2_as row 0 = 1)
    := by grind

  obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3 ⟩ :
     (air.core.c_0 row 0).val < 256 ∧
     (air.core.c_1 row 0).val < 256 ∧
     (air.core.c_2 row 0).val < 256 ∧
     (air.core.c_3 row 0).val < 256
  := by
    rcases b_rs2_as <;> simp_all
    rw [← VmAirWrapper_shift.rs2_sign_limbs] at *
    grind

  simp_all [← VmAirWrapper_shift.rs2_imm_def,
            ← VmAirWrapper_shift.rs2_sign_limbs]

  constructor
  . intro h_rs2_as; simp_all
    grind
  . simp [VmAirWrapper_shift_constraint_and_interaction_simplification,
          ← Valid_ShiftCoreAir_4_8.is_valid_def,
          ← Valid_ShiftCoreAir_4_8.right_shift_def,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_1,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_2,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_3,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_4,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_5,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_6,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_7,
          ← Valid_ShiftCoreAir_4_8.limb_shift_2_def,
          ← Valid_ShiftCoreAir_4_8.limb_shift_3_def,
          ← Valid_ShiftCoreAir_4_8.bit_shift_def,
          ← Valid_ShiftCoreAir_4_8.expected_a_left_0_def,
          ← Valid_ShiftCoreAir_4_8.expected_a_left_1_def,
          ← Valid_ShiftCoreAir_4_8.expected_a_left_2_def,
          ← Valid_ShiftCoreAir_4_8.expected_a_left_3_def,
          ← Valid_ShiftCoreAir_4_8.expected_a_right_0_def,
          ← Valid_ShiftCoreAir_4_8.expected_a_right_1_def,
          ← Valid_ShiftCoreAir_4_8.expected_a_right_2_def,
          ← Valid_ShiftCoreAir_4_8.expected_a_right_3_def,
          ← Valid_ShiftCoreAir_4_8.b_sign_shifted_def] at *

    obtain ⟨ h00, h01, h02, h03, h04, h05, h06, h07, h08, h09,
            h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
            h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
            h30, h31, h32, h33, h34, h35, h36, h37, h38, h39,
            h40, h41, h42, h53, h44, h45, h46, h47, h48, h49,
            h50, h51, h52, h63, h54, h55, h56, h57, h58, h59,
            h60, h61, h62, h73, h64, h65, h66, rest ⟩ := rest
    clear rest

    set lsm_0 := air.core.limb_shift_marker_0 row 0
    set lsm_1 := air.core.limb_shift_marker_1 row 0
    set lsm_2 := air.core.limb_shift_marker_2 row 0
    set lsm_3 := air.core.limb_shift_marker_3 row 0

    set bsm_0 := air.core.bit_shift_marker_0 row 0
    set bsm_1 := air.core.bit_shift_marker_1 row 0
    set bsm_2 := air.core.bit_shift_marker_2 row 0
    set bsm_3 := air.core.bit_shift_marker_3 row 0
    set bsm_4 := air.core.bit_shift_marker_4 row 0
    set bsm_5 := air.core.bit_shift_marker_5 row 0
    set bsm_6 := air.core.bit_shift_marker_6 row 0
    set bsm_7 := air.core.bit_shift_marker_7 row 0

    obtain ⟨ s_bsm_0, s_bsm_1, s_bsm_2, s_bsm_3, s_bsm_4, s_bsm_5, s_bsm_6, s_bsm_7 ⟩ :
      (bsm_0 = 1 → bsm_1 = 0 ∧ bsm_2 = 0 ∧ bsm_3 = 0 ∧ bsm_4 = 0 ∧ bsm_5 = 0 ∧ bsm_6 = 0 ∧ bsm_7 = 0) ∧
      (bsm_1 = 1 → bsm_0 = 0 ∧ bsm_2 = 0 ∧ bsm_3 = 0 ∧ bsm_4 = 0 ∧ bsm_5 = 0 ∧ bsm_6 = 0 ∧ bsm_7 = 0) ∧
      (bsm_2 = 1 → bsm_0 = 0 ∧ bsm_1 = 0 ∧ bsm_3 = 0 ∧ bsm_4 = 0 ∧ bsm_5 = 0 ∧ bsm_6 = 0 ∧ bsm_7 = 0) ∧
      (bsm_3 = 1 → bsm_0 = 0 ∧ bsm_1 = 0 ∧ bsm_2 = 0 ∧ bsm_4 = 0 ∧ bsm_5 = 0 ∧ bsm_6 = 0 ∧ bsm_7 = 0) ∧
      (bsm_4 = 1 → bsm_0 = 0 ∧ bsm_1 = 0 ∧ bsm_2 = 0 ∧ bsm_3 = 0 ∧ bsm_5 = 0 ∧ bsm_6 = 0 ∧ bsm_7 = 0) ∧
      (bsm_5 = 1 → bsm_0 = 0 ∧ bsm_1 = 0 ∧ bsm_2 = 0 ∧ bsm_3 = 0 ∧ bsm_4 = 0 ∧ bsm_6 = 0 ∧ bsm_7 = 0) ∧
      (bsm_6 = 1 → bsm_0 = 0 ∧ bsm_1 = 0 ∧ bsm_2 = 0 ∧ bsm_3 = 0 ∧ bsm_4 = 0 ∧ bsm_5 = 0 ∧ bsm_7 = 0) ∧
      (bsm_7 = 1 → bsm_0 = 0 ∧ bsm_1 = 0 ∧ bsm_2 = 0 ∧ bsm_3 = 0 ∧ bsm_4 = 0 ∧ bsm_5 = 0 ∧ bsm_6 = 0)
      := by clear *- h03 h06 h09 h12 h15 h18 h21 h24 h27; split_ands <;> grind (splits := 15)

    constructor
    . clear *- h00 h04 h07 h10 h13 h16 h19 h22 h25 h27
               s_bsm_0 s_bsm_1 s_bsm_2 s_bsm_3 s_bsm_4 s_bsm_5 s_bsm_6 s_bsm_7
      grind
    . constructor
      . clear *- row_valid h00 h01 h02 h05 h08 h11 h14 h17 h20 h23 h26 h27
               s_bsm_0 s_bsm_1 s_bsm_2 s_bsm_3 s_bsm_4 s_bsm_5 s_bsm_6 s_bsm_7
        grind (splits := 11)
      . clear *- h03 h06 h09 h12 h15 h18 h21 h24 h27 s_bsm_0 s_bsm_1 s_bsm_2 s_bsm_3 s_bsm_4 s_bsm_5 s_bsm_6 s_bsm_7 ra2 ra4 ra6 ra8
        split_ands <;> apply lt_of_lt_of_le (by assumption)
        all_goals
          suffices : (bsm_1 + 2 * bsm_2 + 3 * bsm_3 + 4 * bsm_4 + 5 * bsm_5 + 6 * bsm_6 + 7 * bsm_7) ≤ 7
          . trans 2 ^ 7 <;> [ rw [Fin.le_def] at this; simp ]
            apply pow_le_pow (by simp) (by omega); assumption
          . grind

/-- From Shift opcode to RISC-V opcode -/
def rop_of_Shift_opcode (opcode : FBB) : rop :=
  if opcode = 517 then .SLL else
  if opcode = 518 then .SRL else .SRA

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the SLL opcode:
    - the `b` operand read from memory; and
    - the `c` operand as per the circuit
--/
theorem spec_base_SLL
  (h_sll : air.core.opcode_sll_flag row 0 = 1)
:
  (U32.toBV #v[(air.core.a_0 row 0).val,
               (air.core.a_1 row 0).val,
               (air.core.a_2 row 0).val,
               (air.core.a_3 row 0).val])
    =
  execute_RTYPE_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .SLL
:= by
  have essentials := essentials _ air row row_in_range constraints row_valid propertiesToAssume
  simp [and_assoc] at essentials
  obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
           opcodes, b_rs2_as, h_imm, h_mul_left, h_mul_right, h_bs_0, h_bs_1, h_bs_2, h_bs_3 ⟩ := essentials
  clear b_rs2_as h_imm h_mul_right opcodes

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  clear pa_exec pa_mem pa_read pa_bit
  simp [row_valid, VmAirWrapper_shift_constraint_and_interaction_simplification, propertiesToAssume] at pa_range
  obtain ⟨ ra0, ⟨ h0, ub_bsc0 ⟩, ⟨ h1, ub_bsc1 ⟩, ⟨ h2, ub_bsc2 ⟩, ⟨ h3, ub_bsc3 ⟩, ra4, rest ⟩ := pa_range
  clear h0 h1 h2 h3 ra4 rest

  -- Prepare constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_shift_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions, rest ⟩ := constraints; clear constrain_interactions

  simp [VmAirWrapper_shift_constraint_and_interaction_simplification,
        ← Valid_ShiftCoreAir_4_8.is_valid_def,
        ← Valid_ShiftCoreAir_4_8.right_shift_def,
        ← Valid_ShiftCoreAir_4_8.limb_shift_2_def,
        ← Valid_ShiftCoreAir_4_8.limb_shift_3_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_0_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_1_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_2_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_3_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_0_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_1_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_2_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_3_def,
        ← Valid_ShiftCoreAir_4_8.b_sign_shifted_def,
        ← VmAirWrapper_shift.rs2_imm_def,
        ← VmAirWrapper_shift.rs2_sign_limbs] at *

  simp [row_valid] at rest

  obtain ⟨ h00, h01, h02, h03, h04, h05, h06, h07, h08, h09,
           h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
           h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
           h30, h31, h32, h33, h34, h35, h36, h37, h38, h39,
           h40, h41, h42, h43, h44, h45, h46, h47, h48, h49,
           h50, h51, h52, h53, h54, h55, h56, h57, h58, h59,
           h60, h61, h62, h63, h64, h65, h66, rest ⟩ := rest
  clear h00 h01 h02 h05 h08 h11 h14 h17 h20 h23 h26
        h30 h32 h34 h36 h39 h41 h43 h45 h48 h50 h52
        h54 h57 h59 h61 h63 h65 h66 rest

  simp [h_sll] at *

  set lsm_0 := air.core.limb_shift_marker_0 row 0
  set lsm_1 := air.core.limb_shift_marker_1 row 0
  set lsm_2 := air.core.limb_shift_marker_2 row 0
  set lsm_3 := air.core.limb_shift_marker_3 row 0

  have ub_lsm : lsm_1 + 2 * lsm_2 + 3 * lsm_3 < 4
    := by clear *- h28 h37 h46 h55 h64; grind

  have ub_bsm : air.core.bit_shift row 0 < 8
  := by
    simp [← Valid_ShiftCoreAir_4_8.bit_shift_def]
    rw [← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_7,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_6,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_5,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_4,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_3,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_2,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_1] at h27
    clear *- h03 h06 h09 h12 h15 h18 h21 h24 h27; grind

  have h_is := @FBB_invert_shift
                (air.core.c_0 row 0)
                (lsm_1 + 2 * lsm_2 + 3 * lsm_3)
                (air.core.bit_shift row 0)
                ub_c0
                ub_lsm
                ub_bsm
                ra0

  have eq_c_mod_32 : (U32.toNat #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] % 32) = ((air.core.c_0 row 0) % 32).val
    := by simp [U32.toNat]; omega
  rw [h_is] at eq_c_mod_32
  simp [Fin.val_add, Fin.val_mul] at eq_c_mod_32
  rw [Nat.mod_eq_of_lt
       (b := 2013265921)
       (by clear *- h28 h37 h46 h55 h64 ub_bsm; grind)
     ] at eq_c_mod_32

  have eq_bml : 2 ^ (air.core.bit_shift row 0).val = (air.core.bit_multiplier_left row 0).val
  := by
    clear *- h03 h04 h06 h07 h09 h10 h12 h13 h15 h16 h18 h19 h21 h22 h24 h25 h27
    simp [← Valid_ShiftCoreAir_4_8.bit_shift_def,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_7,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_6,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_5,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_4,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_3,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_2,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_1] at *
    rcases h03 <;> [ skip; simp_all ]
    rcases h06 <;> [ skip; simp_all ]
    rcases h09 <;> [ skip; simp_all ]
    rcases h12 <;> [ skip; simp_all ]
    rcases h15 <;> [ skip; simp_all ]
    rcases h18 <;> [ skip; simp_all ]
    rcases h21 <;> [ skip; simp_all ]
    rcases h24 <;> simp_all

  simp [execute_RTYPE_pure, eq_c_mod_32]
  simp [← BitVec.toNat_inj, Nat.shiftLeft_eq_mul_pow]
  rw [pow_add, eq_bml]
  simp [U32.toNat]
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]

  obtain ⟨ s_lsm_0, s_lsm_1, s_lsm_2, s_lsm_3 ⟩ :
    (lsm_0 = 1 → lsm_1 = 0 ∧ lsm_2 = 0 ∧ lsm_3 = 0) ∧
    (lsm_1 = 1 → lsm_0 = 0 ∧ lsm_2 = 0 ∧ lsm_3 = 0) ∧
    (lsm_2 = 1 → lsm_0 = 0 ∧ lsm_1 = 0 ∧ lsm_3 = 0) ∧
    (lsm_3 = 1 → lsm_0 = 0 ∧ lsm_1 = 0 ∧ lsm_2 = 0)
    := by clear *- h28 h37 h46 h55 h64; split_ands <;> grind

  have p0 : (air.core.b_0 row 0).val * (air.core.bit_multiplier_left row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind
  have p1 : (air.core.b_1 row 0).val * (air.core.bit_multiplier_left row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind
  have p2 : (air.core.b_2 row 0).val * (air.core.bit_multiplier_left row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind
  have p3 : (air.core.b_3 row 0).val * (air.core.bit_multiplier_left row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind

  rcases h37 <;> [ (rcases h46 <;> [ (rcases h55 <;> simp_all); simp_all ]); simp_all ]

  . obtain ⟨ ub_a0', eqn0, eqz0, q0 ⟩ := FBB_quotient_with_properties ub_a0 h_bs_0
    obtain ⟨ ub_a1', eqn1, eqz1, q1 ⟩ := FBB_quotient_with_properties ub_a1 h_bs_1
    obtain ⟨ ub_a2', eqn2, eqz2, q2 ⟩ := FBB_quotient_with_properties ub_a2 h_bs_2
    obtain ⟨ ub_a3', eqn3, eqz3, q3 ⟩ := FBB_quotient_with_properties ub_a3 h_bs_3
    rw [← Fin.div_val, ← Fin.ext_iff] at q0 q1 q2 q3
    zify
    rw [eqz0, eqz1, eqz2, eqz3]
    simp [Fin.val_add, Fin.val_mul]
    iterate 4 rw [Int.emod_eq_of_lt (b := 2013265921) (by omega) (by omega)]
    ring_nf
    rw [← q2, ← q1, ← q0] at q3
    suffices : ↑↑(air.core.bit_shift_carry_3 row 0) =
      (((air.core.b_0 row 0) : ℤ) * (air.core.bit_multiplier_left row 0) +
        (air.core.bit_multiplier_left row 0) * (air.core.b_1 row 0) * 256 +
        (air.core.bit_multiplier_left row 0) * (air.core.b_2 row 0) * 65536 +
        (air.core.bit_multiplier_left row 0) * (air.core.b_3 row 0) * 16777216) / 4294967296
    . rw [this]
      omega
    . rw [← q3]
      clear *- ub_b0 ub_b1 ub_b2 ub_b3 p0 p1 p2 p3 h_mul_left
      simp [Fin.val_add, Fin.val_mul]
      repeat rw [Int.emod_eq_of_lt (b := 2013265921) (by omega) (by omega)]
      grind

  . obtain ⟨ ub_a0', eqn0, eqz0, q0 ⟩ := FBB_quotient_with_properties ub_a3 h_bs_0
    rw [← Fin.div_val, ← Fin.ext_iff] at q0
    zify
    rw [eqz0]
    simp [Fin.val_mul]
    rw [Int.emod_eq_of_lt (b := 2013265921) (by omega) (by omega)]
    ring_nf
    suffices : ↑↑(air.core.bit_shift_carry_0 row 0) =
      (((air.core.b_0 row 0) : ℤ) * (air.core.bit_multiplier_left row 0)) / 256
    . rw [this]
      omega
    . rw [← q0]
      clear *- ub_b0 ub_b1 ub_b2 ub_b3 p0 p1 p2 p3 h_mul_left
      simp [Fin.val_mul]
      repeat rw [Int.emod_eq_of_lt (b := 2013265921) (by omega) (by omega)]

  . obtain ⟨ ub_a0', eqn0, eqz0, q0 ⟩ := FBB_quotient_with_properties ub_a2 h_bs_0
    obtain ⟨ ub_a1', eqn1, eqz1, q1 ⟩ := FBB_quotient_with_properties ub_a3 h_bs_1
    rw [← Fin.div_val, ← Fin.ext_iff] at q0 q1
    zify
    rw [eqz0, eqz1]
    simp [Fin.val_add, Fin.val_mul]
    iterate 2 rw [Int.emod_eq_of_lt (b := 2013265921) (by omega) (by omega)]
    ring_nf
    rw [← q0] at q1
    suffices : ↑↑(air.core.bit_shift_carry_1 row 0) =
      (((air.core.b_0 row 0) : ℤ) * (air.core.bit_multiplier_left row 0) +
        (air.core.bit_multiplier_left row 0) * (air.core.b_1 row 0) * 256) / 65536
    . rw [this]
      omega
    . rw [← q1]
      clear *- ub_b0 ub_b1 ub_b2 ub_b3 p0 p1 p2 p3 h_mul_left
      simp [Fin.val_add, Fin.val_mul]
      repeat rw [Int.emod_eq_of_lt (b := 2013265921) (by omega) (by omega)]
      grind

  . obtain ⟨ ub_a0', eqn0, eqz0, q0 ⟩ := FBB_quotient_with_properties ub_a1 h_bs_0
    obtain ⟨ ub_a1', eqn1, eqz1, q1 ⟩ := FBB_quotient_with_properties ub_a2 h_bs_1
    obtain ⟨ ub_a2', eqn2, eqz2, q2 ⟩ := FBB_quotient_with_properties ub_a3 h_bs_2
    rw [← Fin.div_val, ← Fin.ext_iff] at q0 q1 q2
    zify
    rw [eqz0, eqz1, eqz2]
    simp [Fin.val_add, Fin.val_mul]
    iterate 3 rw [Int.emod_eq_of_lt (b := 2013265921) (by omega) (by omega)]
    ring_nf
    rw [← q1, ← q0] at q2
    suffices : ↑↑(air.core.bit_shift_carry_2 row 0) =
      (((air.core.b_0 row 0) : ℤ) * (air.core.bit_multiplier_left row 0) +
        (air.core.bit_multiplier_left row 0) * (air.core.b_1 row 0) * 256 +
        (air.core.bit_multiplier_left row 0) * (air.core.b_2 row 0) * 65536) / 16777216
    . rw [this]
      omega
    . rw [← q2]
      clear *- ub_b0 ub_b1 ub_b2 ub_b3 p0 p1 p2 p3 h_mul_left
      simp [Fin.val_add, Fin.val_mul]
      repeat rw [Int.emod_eq_of_lt (b := 2013265921) (by omega) (by omega)]
      grind

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the SRL opcode:
    - the `b` operand read from memory; and
    - the `c` operand as per the circuit
--/
theorem spec_base_SRL
  (h_srl : air.core.opcode_srl_flag row 0 = 1 ∨ (air.core.opcode_sra_flag row 0 = 1 ∧ air.core.b_sign row 0 = 0))
:
  (U32.toBV #v[(air.core.a_0 row 0).val,
               (air.core.a_1 row 0).val,
               (air.core.a_2 row 0).val,
               (air.core.a_3 row 0).val])
    =
  execute_RTYPE_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .SRL
:= by
  have essentials := essentials _ air row row_in_range constraints row_valid propertiesToAssume
  simp [and_assoc] at essentials
  obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
           opcodes, b_rs2_as, h_imm, h_mul_left, h_mul_right, h_bs_0, h_bs_1, h_bs_2, h_bs_3 ⟩ := essentials
  clear b_rs2_as h_imm h_mul_left opcodes

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  clear pa_exec pa_mem pa_read pa_bit
  simp [row_valid, VmAirWrapper_shift_constraint_and_interaction_simplification, propertiesToAssume] at pa_range
  obtain ⟨ ra0, ⟨ h0, ub_bsc0 ⟩, ⟨ h1, ub_bsc1 ⟩, ⟨ h2, ub_bsc2 ⟩, ⟨ h3, ub_bsc3 ⟩, ra4, rest ⟩ := pa_range
  clear h0 h1 h2 h3 ra4 rest

  have ⟨ sop0, sop1, sop2 ⟩ := single_op air row row_in_range constraints

  -- Prepare constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_shift_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions, rest ⟩ := constraints; clear constrain_interactions

  simp [VmAirWrapper_shift_constraint_and_interaction_simplification,
        ← Valid_ShiftCoreAir_4_8.is_valid_def,
        ← Valid_ShiftCoreAir_4_8.right_shift_def,
        ← Valid_ShiftCoreAir_4_8.limb_shift_2_def,
        ← Valid_ShiftCoreAir_4_8.limb_shift_3_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_0_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_1_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_2_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_3_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_0_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_1_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_2_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_3_def,
        ← Valid_ShiftCoreAir_4_8.b_sign_shifted_def,
        ← VmAirWrapper_shift.rs2_imm_def,
        ← VmAirWrapper_shift.rs2_sign_limbs] at *

  simp [row_valid] at rest

  obtain ⟨ h00, h01, h02, h03, h04, h05, h06, h07, h08, h09,
           h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
           h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
           h30, h31, h32, h33, h34, h35, h36, h37, h38, h39,
           h40, h41, h42, h43, h44, h45, h46, h47, h48, h49,
           h50, h51, h52, h53, h54, h55, h56, h57, h58, h59,
           h60, h61, h62, h63, h64, h65, h66, rest ⟩ := rest
  have ⟨ h_sll, h_sr ⟩ : air.core.opcode_sll_flag row 0 = 0 ∧ air.core.opcode_srl_flag row 0 + air.core.opcode_sra_flag row 0 = 1
    := by clear *- h_srl sop1 sop2; rcases h_srl <;> simp_all
  simp [h_sll, h_sr] at *
  have h_b_sign_z : air.core.b_sign row 0 = 0
    := by clear *- h_srl h65 h66 sop1 sop2; grind
  simp [h_b_sign_z] at *

  clear row_valid sop0 sop1 sop2 h_srl h_sll h_sr h_b_sign_z
        h00 h01 h02 h04 h07 h10 h13 h16 h19 h22 h25 h29 h31
        h33  h35 h38 h40 h42 h44 h47 h49 h51 h53 h62 rest

  set lsm_0 := air.core.limb_shift_marker_0 row 0
  set lsm_1 := air.core.limb_shift_marker_1 row 0
  set lsm_2 := air.core.limb_shift_marker_2 row 0
  set lsm_3 := air.core.limb_shift_marker_3 row 0

  have ub_lsm : lsm_1 + 2 * lsm_2 + 3 * lsm_3 < 4
    := by clear *- h28 h37 h46 h55 h64; grind

  have ub_bsm : air.core.bit_shift row 0 < 8
  := by
    simp [← Valid_ShiftCoreAir_4_8.bit_shift_def]
    rw [← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_7,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_6,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_5,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_4,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_3,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_2,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_1] at h27
    clear *- h03 h06 h09 h12 h15 h18 h21 h24 h27; grind

  have h_is := @FBB_invert_shift
                (air.core.c_0 row 0)
                (lsm_1 + 2 * lsm_2 + 3 * lsm_3)
                (air.core.bit_shift row 0)
                ub_c0
                ub_lsm
                ub_bsm
                ra0

  have eq_c_mod_32 : (U32.toNat #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] % 32) = ((air.core.c_0 row 0) % 32).val
    := by simp [U32.toNat]; omega
  rw [h_is] at eq_c_mod_32
  simp [Fin.val_add, Fin.val_mul] at eq_c_mod_32
  rw [Nat.mod_eq_of_lt
       (b := 2013265921)
       (by clear *- h28 h37 h46 h55 h64 ub_bsm; grind)
     ] at eq_c_mod_32

  obtain ⟨ nz_bmr, eq_bmr, cases_bmr ⟩ :
    0 < (air.core.bit_multiplier_right row 0).val ∧
    2 ^ (air.core.bit_shift row 0).val = (air.core.bit_multiplier_right row 0).val ∧
    (air.core.bit_multiplier_right row 0 = 1 ∨ air.core.bit_multiplier_right row 0 = 2 ∨ air.core.bit_multiplier_right row 0 = 4 ∨ air.core.bit_multiplier_right row 0 = 8 ∨
     air.core.bit_multiplier_right row 0 = 16 ∨ air.core.bit_multiplier_right row 0 = 32 ∨ air.core.bit_multiplier_right row 0 = 64 ∨ air.core.bit_multiplier_right row 0 = 128)
  := by
    clear *- h03 h05 h06 h08 h09 h11 h12 h14 h15 h17 h18 h20 h21 h23 h24 h26 h27
    simp [← Valid_ShiftCoreAir_4_8.bit_shift_def,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_7,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_6,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_5,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_4,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_3,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_2,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_1] at *
    rcases h03 <;> [ skip; simp_all ]
    rcases h06 <;> [ skip; simp_all ]
    rcases h09 <;> [ skip; simp_all ]
    rcases h12 <;> [ skip; simp_all ]
    rcases h15 <;> [ skip; simp_all ]
    rcases h18 <;> [ skip; simp_all ]
    rcases h21 <;> [ skip; simp_all ]
    rcases h24 <;> simp_all

  simp [execute_RTYPE_pure, eq_c_mod_32]
  simp [← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow]
  rw [pow_add, eq_bmr]
  simp [U32.toNat]
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]

  obtain ⟨ s_lsm_0, s_lsm_1, s_lsm_2, s_lsm_3 ⟩ :
    (lsm_0 = 1 → lsm_1 = 0 ∧ lsm_2 = 0 ∧ lsm_3 = 0) ∧
    (lsm_1 = 1 → lsm_0 = 0 ∧ lsm_2 = 0 ∧ lsm_3 = 0) ∧
    (lsm_2 = 1 → lsm_0 = 0 ∧ lsm_1 = 0 ∧ lsm_3 = 0) ∧
    (lsm_3 = 1 → lsm_0 = 0 ∧ lsm_1 = 0 ∧ lsm_2 = 0)
    := by clear *- h28 h37 h46 h55 h64; split_ands <;> grind

  have p0 : (air.core.a_0 row 0).val * (air.core.bit_multiplier_right row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind
  have p1 : (air.core.a_1 row 0).val * (air.core.bit_multiplier_right row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind
  have p2 : (air.core.a_2 row 0).val * (air.core.bit_multiplier_right row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind
  have p3 : (air.core.a_3 row 0).val * (air.core.bit_multiplier_right row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind

  rcases h28 with lsm0z | lsm0o; rotate_left

  . obtain ⟨ lsm1z, lsm2z, lsm3z ⟩ := s_lsm_0 lsm0o
    simp [lsm0o, lsm1z, lsm2z, lsm3z] at *
    simp_all

    trans ((air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256 + (air.core.a_2 row 0) * 65536 + (air.core.a_3 row 0) * 16777216) * (air.core.bit_multiplier_right row 0).val / (air.core.bit_multiplier_right row 0).val
    . rw [Nat.mul_div_cancel
           (m := (air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256 + (air.core.a_2 row 0) * 65536 + (air.core.a_3 row 0) * 16777216)
           (n := (air.core.bit_multiplier_right row 0).val)
           (by grind)]
    . trans ((air.core.a_0 row 0 * air.core.bit_multiplier_right row 0).val +
             (air.core.a_1 row 0 * air.core.bit_multiplier_right row 0).val * 256 +
             (air.core.a_2 row 0 * air.core.bit_multiplier_right row 0).val * 65536 +
             (air.core.a_3 row 0 * air.core.bit_multiplier_right row 0).val * 16777216) / (air.core.bit_multiplier_right row 0).val
      . simp [Fin.val_mul]
        iterate 4 rw [Nat.mod_eq_of_lt (by omega)]
        ring_nf
      . rw [h30, h32, h34, h36]
        have p0' : (air.core.bit_shift_carry_1 row 0 * 256 + (air.core.b_0 row 0 - air.core.bit_shift_carry_0 row 0)).val ≤ 32640 := by omega
        have p1' : (air.core.bit_shift_carry_2 row 0 * 256 + (air.core.b_1 row 0 - air.core.bit_shift_carry_1 row 0)).val ≤ 32640 := by omega
        have p2' : (air.core.bit_shift_carry_3 row 0 * 256 + (air.core.b_2 row 0 - air.core.bit_shift_carry_2 row 0)).val ≤ 32640 := by omega
        have p3' : (air.core.b_3 row 0 - air.core.bit_shift_carry_3 row 0).val ≤ 32640 := by omega

        rw [← add_sub_assoc] at p0' p1' p2'
        repeat rw [← add_sub_assoc]

        zify
        repeat rw [Fin.sub_val_of_le (by omega), Int.natCast_sub (by omega)]
        simp [Fin.val_add, Fin.val_mul]
        repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
        ring_nf
        repeat rw [add_assoc]
        rw [Int.add_ediv_of_dvd_right
            (by clear *- cases_bmr
                rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                simp_all <;>
                omega)]
        rw [Int.add_ediv_of_dvd_right
              (a := ↑↑(air.core.b_0 row 0))
              (by clear *- cases_bmr
                  rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                  simp_all <;>
                  omega)]
        rw [add_right_cancel_iff]
        suffices : ((air.core.bit_multiplier_right row 0) : ℤ) ∣ ↑↑(air.core.b_0 row 0) - ↑↑(air.core.bit_shift_carry_0 row 0)
        . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
          simp_all <;>
          omega
        . suffices : ((air.core.bit_multiplier_right row 0) : ℕ) ∣ (air.core.bit_shift_carry_1 row 0 * 256 + (air.core.b_0 row 0 - air.core.bit_shift_carry_0 row 0)).val
          . zify at this
            rw [← add_sub_assoc,
                Fin.sub_val_of_le (by omega),
                Int.natCast_sub (by omega)] at this
            rw [Fin.val_add, Nat.mod_eq_of_lt (by grind)] at this
            rw [Fin.val_mul, Nat.mod_eq_of_lt (by grind)] at this
            simp [add_sub_assoc] at this
            apply Int.dvd_iff_dvd_of_dvd_add at this
            rw [← this]
            rcases cases_bmr with h | h | h | h | h | h | h | h <;>
            simp [h] <;>
            omega
          . rw [← h30]
            simp [Fin.mul_def]
            rw [Nat.mod_eq_of_lt (by omega)]
            simp

  . rcases h37 with lsm1z | lsm1o; rotate_left
    obtain ⟨ lsm0z, lsm2z, lsm3z ⟩ := s_lsm_1 lsm1o
    simp [lsm0z, lsm1o, lsm2z, lsm3z] at *
    simp_all

    . trans ((air.core.b_1 row 0).val + (air.core.b_2 row 0) * 256 + (air.core.b_3 row 0) * 65536) / (air.core.bit_multiplier_right row 0).val
      . trans ((air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256 + (air.core.a_2 row 0) * 65536) * (air.core.bit_multiplier_right row 0).val / (air.core.bit_multiplier_right row 0).val
        . rw [Nat.mul_div_cancel
              (m := (air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256 + (air.core.a_2 row 0) * 65536)
              (n := (air.core.bit_multiplier_right row 0).val)
              (by grind)]
        . trans ((air.core.a_0 row 0 * air.core.bit_multiplier_right row 0).val +
                (air.core.a_1 row 0 * air.core.bit_multiplier_right row 0).val * 256 +
                (air.core.a_2 row 0 * air.core.bit_multiplier_right row 0).val * 65536) / (air.core.bit_multiplier_right row 0).val
          . simp [Fin.val_mul]
            iterate 3 rw [Nat.mod_eq_of_lt (by omega)]
            ring_nf
          . rw [h39, h41, h43]
            have p1' : (air.core.bit_shift_carry_2 row 0 * 256 + (air.core.b_1 row 0 - air.core.bit_shift_carry_1 row 0)).val ≤ 32640 := by omega
            have p2' : (air.core.bit_shift_carry_3 row 0 * 256 + (air.core.b_2 row 0 - air.core.bit_shift_carry_2 row 0)).val ≤ 32640 := by omega
            have p3' : (air.core.b_3 row 0 - air.core.bit_shift_carry_3 row 0).val ≤ 32640 := by omega

            rw [← add_sub_assoc] at p1' p2'
            repeat rw [← add_sub_assoc]

            zify
            repeat rw [Fin.sub_val_of_le (by omega), Int.natCast_sub (by omega)]
            simp [Fin.val_add, Fin.val_mul]
            repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
            ring_nf
            repeat rw [add_assoc]
            rw [Int.add_ediv_of_dvd_right
                (by clear *- cases_bmr
                    rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                    simp_all <;>
                    omega)]
            rw [Int.add_ediv_of_dvd_right
                  (a := ↑↑(air.core.b_1 row 0))
                  (by clear *- cases_bmr
                      rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                      simp_all <;>
                      omega)]
            rw [add_right_cancel_iff]
            suffices : ((air.core.bit_multiplier_right row 0) : ℤ) ∣ ↑↑(air.core.b_1 row 0) - ↑↑(air.core.bit_shift_carry_1 row 0)
            . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
              simp_all <;>
              omega
            . suffices : ((air.core.bit_multiplier_right row 0) : ℕ) ∣ (air.core.bit_shift_carry_2 row 0 * 256 + (air.core.b_1 row 0 - air.core.bit_shift_carry_1 row 0)).val
              . zify at this
                rw [← add_sub_assoc,
                    Fin.sub_val_of_le (by omega),
                    Int.natCast_sub (by omega)] at this
                rw [Fin.val_add, Nat.mod_eq_of_lt (by grind)] at this
                rw [Fin.val_mul, Nat.mod_eq_of_lt (by grind)] at this
                simp [add_sub_assoc] at this
                apply Int.dvd_iff_dvd_of_dvd_add at this
                rw [← this]
                rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                simp [h] <;>
                omega
              . rw [← h39]
                simp [Fin.mul_def]
                rw [Nat.mod_eq_of_lt (by omega)]
                simp
      . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
        simp [h] <;>
        omega

    . rcases h46 with lsm2z | lsm2o; rotate_left
      obtain ⟨ lsm0z, lsm1z, lsm3z ⟩ := s_lsm_2 lsm2o
      simp [lsm0z, lsm1z, lsm2o, lsm3z] at *
      simp_all

      . trans ((air.core.b_2 row 0) + (air.core.b_3 row 0) * 256) / (air.core.bit_multiplier_right row 0).val
        . trans ((air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256) * (air.core.bit_multiplier_right row 0).val / (air.core.bit_multiplier_right row 0).val
          . rw [Nat.mul_div_cancel
                (m := (air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256)
                (n := (air.core.bit_multiplier_right row 0).val)
                (by grind)]
          . trans ((air.core.a_0 row 0 * air.core.bit_multiplier_right row 0).val +
                  (air.core.a_1 row 0 * air.core.bit_multiplier_right row 0).val * 256) / (air.core.bit_multiplier_right row 0).val
            . simp [Fin.val_mul]
              iterate 2 rw [Nat.mod_eq_of_lt (by omega)]
              ring_nf
            . rw [h48, h50]
              have p2' : (air.core.bit_shift_carry_3 row 0 * 256 + (air.core.b_2 row 0 - air.core.bit_shift_carry_2 row 0)).val ≤ 32640 := by omega
              have p3' : (air.core.b_3 row 0 - air.core.bit_shift_carry_3 row 0).val ≤ 32640 := by omega

              rw [← add_sub_assoc] at p2'
              repeat rw [← add_sub_assoc]

              zify
              repeat rw [Fin.sub_val_of_le (by omega), Int.natCast_sub (by omega)]
              simp [Fin.val_add, Fin.val_mul]
              repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
              ring_nf
              rw [Int.add_ediv_of_dvd_right
                  (by clear *- cases_bmr
                      rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                      simp_all <;>
                      omega)]
              rw [Int.add_ediv_of_dvd_right
                    (a := ↑↑(air.core.b_2 row 0))
                    (by clear *- cases_bmr
                        rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                        simp_all <;>
                        omega)]
              rw [add_right_cancel_iff]
              suffices : ((air.core.bit_multiplier_right row 0) : ℤ) ∣ ↑↑(air.core.b_2 row 0) - ↑↑(air.core.bit_shift_carry_2 row 0)
              . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                simp_all <;>
                omega
              . suffices : ((air.core.bit_multiplier_right row 0) : ℕ) ∣ (air.core.bit_shift_carry_3 row 0 * 256 + (air.core.b_2 row 0 - air.core.bit_shift_carry_2 row 0)).val
                . zify at this
                  rw [← add_sub_assoc,
                      Fin.sub_val_of_le (by omega),
                      Int.natCast_sub (by omega)] at this
                  rw [Fin.val_add, Nat.mod_eq_of_lt (by grind)] at this
                  rw [Fin.val_mul, Nat.mod_eq_of_lt (by grind)] at this
                  simp [add_sub_assoc] at this
                  apply Int.dvd_iff_dvd_of_dvd_add at this
                  rw [← this]
                  rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                  simp [h] <;>
                  omega
                . rw [← h48]
                  simp [Fin.mul_def]
                  rw [Nat.mod_eq_of_lt (by omega)]
                  simp
        . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
          simp [h] <;>
          omega

      . rcases h55 with lsm3z | lsm3o; rotate_left
        obtain ⟨ lsm0z, lsm1z, lsm2z ⟩ := s_lsm_3 lsm3o
        simp [lsm0z, lsm1z, lsm2z, lsm3o] at *
        simp_all

        . trans (air.core.b_3 row 0) / (air.core.bit_multiplier_right row 0).val
          . trans (air.core.a_0 row 0).val * (air.core.bit_multiplier_right row 0).val / (air.core.bit_multiplier_right row 0).val
            . rw [Nat.mul_div_cancel
                  (m := (air.core.a_0 row 0).val)
                  (n := (air.core.bit_multiplier_right row 0).val)
                  (by grind)]
            . trans ((air.core.a_0 row 0 * air.core.bit_multiplier_right row 0).val) / (air.core.bit_multiplier_right row 0).val
              . simp [Fin.val_mul]
                rw [Nat.mod_eq_of_lt (by omega)]
              . rw [h57]
                have p3' : (air.core.b_3 row 0 - air.core.bit_shift_carry_3 row 0).val ≤ 32640 := by omega

                zify
                repeat rw [Fin.sub_val_of_le (by omega), Int.natCast_sub (by omega)]
                ring_nf
                suffices : ((air.core.bit_multiplier_right row 0) : ℤ) ∣ ↑↑(air.core.b_3 row 0) - ↑↑(air.core.bit_shift_carry_3 row 0)
                . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                  simp_all <;>
                  omega
                . suffices : ((air.core.bit_multiplier_right row 0) : ℕ) ∣ (air.core.b_3 row 0 - air.core.bit_shift_carry_3 row 0).val
                  . zify at this
                    rw [Fin.sub_val_of_le (by omega),
                        Int.natCast_sub (by omega)] at this
                    assumption
                  . rw [← h57]
                    simp [Fin.mul_def]
                    rw [Nat.mod_eq_of_lt (by omega)]
                    simp
          . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
            simp [h] <;>
            omega
        . simp_all

section auxiliaries

  include
    row_valid
    constraints
    propertiesToAssume
  in
  lemma b_sign_properties [Field ExtF]
  :
    (air.core.b_sign row 0 = 0 ∨ air.core.b_sign row 0 = 1) ∧
    (air.core.opcode_sra_flag row 0 = 1 →
      (air.core.b_sign row 0 = 1 ↔
         U32.negative #v[(air.core.b_0 row 0).val,
                         (air.core.b_1 row 0).val,
                         (air.core.b_2 row 0).val,
                         (air.core.b_3 row 0).val]))
  := by
    have h_b_b_sign : (air.core.b_sign row 0 = 0 ∨ air.core.b_sign row 0 = 1)
    := by
      rw [@allHold_simplified_of_allHold] at constraints
      simp_all [VmAirWrapper_shift_constraint_and_interaction_simplification]
    constructor
    . assumption
    . intro h_sra
      obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
      clear pa_exec pa_mem pa_read pa_range
      simp [row_valid, VmAirWrapper_shift_constraint_and_interaction_simplification, propertiesToAssume] at pa_bit
      obtain ⟨ h_b_sign', rest ⟩ := pa_bit; clear rest
      simp [h_sra] at *
      obtain ⟨ ub_b3, h_b_sign ⟩ := h_b_sign'
      have h_b_sign' := @BabyBear.xor_as_and (air.core.b_sign row 0 * 128) (air.core.b_3 row 0) 128 ub_b3 (by simp) h_b_sign
      clear h_b_sign; simp at h_b_sign'
      constructor
      . intro h_b_sign
        simp [h_b_sign] at *
        simp [← U32.msb_3_negative, BitVec.msb_eq_decide]
        have := @Nat.and_le_left (air.core.b_3 row 0) 128
        omega
      . intro h_b_neg
        simp [← U32.msb_3_negative, BitVec.msb_eq_decide] at h_b_neg
        rcases h_b_b_sign with h_b_sign | h_b_sign <;> simp [h_b_sign] at *
        rw [Nat.mod_eq_of_lt ub_b3] at h_b_neg
        have := Nat.and_two_pow (air.core.b_3 row 0) (i := 7)
        simp at this; rw [this] at h_b_sign'; simp at h_b_sign'; clear this
        suffices : (air.core.b_3 row 0).val < 128
        . omega
        . clear h_b_neg h_b_sign
          grind

end auxiliaries

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the SRA opcode:
    - the `b` operand read from memory; and
    - the `c` operand as per the circuit
--/
theorem spec_base_SRA
  (h_sra : air.core.opcode_sra_flag row 0 = 1)
  (h_b_sign : air.core.b_sign row 0 = 1)
:
  (U32.toBV #v[(air.core.a_0 row 0).val,
               (air.core.a_1 row 0).val,
               (air.core.a_2 row 0).val,
               (air.core.a_3 row 0).val])
    =
  execute_RTYPE_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .SRA
:= by
  have essentials := essentials _ air row row_in_range constraints row_valid propertiesToAssume
  simp [and_assoc] at essentials
  obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
           opcodes, b_rs2_as, h_imm, h_mul_left, h_mul_right, h_bs_0, h_bs_1, h_bs_2, h_bs_3 ⟩ := essentials
  clear b_rs2_as h_imm h_mul_left opcodes

  have ⟨ h0, b_sign_msb ⟩ := b_sign_properties _ air row row_in_range constraints row_valid propertiesToAssume
  clear h0

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  clear pa_exec pa_mem pa_read
  simp [row_valid, VmAirWrapper_shift_constraint_and_interaction_simplification, propertiesToAssume] at pa_range pa_bit
  obtain ⟨ ra0, ⟨ h0, ub_bsc0 ⟩, ⟨ h1, ub_bsc1 ⟩, ⟨ h2, ub_bsc2 ⟩, ⟨ h3, ub_bsc3 ⟩, ra4, rest ⟩ := pa_range
  clear h0 h1 h2 h3 ra4 rest

  have ⟨ sop0, sop1, sop2 ⟩ := single_op air row row_in_range constraints

  -- Prepare constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_shift_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions, rest ⟩ := constraints; clear constrain_interactions

  simp [VmAirWrapper_shift_constraint_and_interaction_simplification,
        ← Valid_ShiftCoreAir_4_8.is_valid_def,
        ← Valid_ShiftCoreAir_4_8.right_shift_def,
        ← Valid_ShiftCoreAir_4_8.limb_shift_2_def,
        ← Valid_ShiftCoreAir_4_8.limb_shift_3_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_0_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_1_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_2_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_left_3_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_0_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_1_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_2_def,
        ← Valid_ShiftCoreAir_4_8.expected_a_right_3_def,
        ← Valid_ShiftCoreAir_4_8.b_sign_shifted_def,
        ← VmAirWrapper_shift.rs2_imm_def,
        ← VmAirWrapper_shift.rs2_sign_limbs] at *

  simp [row_valid] at rest

  obtain ⟨ h00, h01, h02, h03, h04, h05, h06, h07, h08, h09,
           h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
           h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
           h30, h31, h32, h33, h34, h35, h36, h37, h38, h39,
           h40, h41, h42, h43, h44, h45, h46, h47, h48, h49,
           h50, h51, h52, h53, h54, h55, h56, h57, h58, h59,
           h60, h61, h62, h63, h64, h65, h66, rest ⟩ := rest
  have h_srl : air.core.opcode_srl_flag row 0 = 0 := by clear *- h_sra sop2; grind
  simp [h_srl, h_sra, h_b_sign] at *
  clear row_valid sop0 sop1 sop2 h_srl h_sra h00 h01 h02
        h04 h07 h10 h13 h16 h19 h22 h25 h29 h31 h33 h35
        h38 h40 h42 h44 h47 h49 h51 h53 h62 rest

  set lsm_0 := air.core.limb_shift_marker_0 row 0
  set lsm_1 := air.core.limb_shift_marker_1 row 0
  set lsm_2 := air.core.limb_shift_marker_2 row 0
  set lsm_3 := air.core.limb_shift_marker_3 row 0

  have ub_lsm : lsm_1 + 2 * lsm_2 + 3 * lsm_3 < 4
    := by clear *- h28 h37 h46 h55 h64; grind

  have ub_bsm : air.core.bit_shift row 0 < 8
  := by
    simp [← Valid_ShiftCoreAir_4_8.bit_shift_def]
    rw [← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_7,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_6,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_5,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_4,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_3,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_2,
        ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_1] at h27
    clear *- h03 h06 h09 h12 h15 h18 h21 h24 h27; grind

  have h_is := @FBB_invert_shift
                (air.core.c_0 row 0)
                (lsm_1 + 2 * lsm_2 + 3 * lsm_3)
                (air.core.bit_shift row 0)
                ub_c0
                ub_lsm
                ub_bsm
                ra0

  have eq_c_mod_32 : (U32.toNat #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] % 32) = ((air.core.c_0 row 0) % 32).val
    := by simp [U32.toNat]; omega
  rw [h_is] at eq_c_mod_32
  simp [Fin.val_add, Fin.val_mul] at eq_c_mod_32
  rw [Nat.mod_eq_of_lt
       (b := 2013265921)
       (by clear *- h28 h37 h46 h55 h64 ub_bsm; grind)
     ] at eq_c_mod_32

  obtain ⟨ nz_bmr, eq_bmr, cases_bmr ⟩ :
    0 < (air.core.bit_multiplier_right row 0).val ∧
    2 ^ (air.core.bit_shift row 0).val = (air.core.bit_multiplier_right row 0).val ∧
    (air.core.bit_multiplier_right row 0 = 1 ∨ air.core.bit_multiplier_right row 0 = 2 ∨ air.core.bit_multiplier_right row 0 = 4 ∨ air.core.bit_multiplier_right row 0 = 8 ∨
     air.core.bit_multiplier_right row 0 = 16 ∨ air.core.bit_multiplier_right row 0 = 32 ∨ air.core.bit_multiplier_right row 0 = 64 ∨ air.core.bit_multiplier_right row 0 = 128)
  := by
    clear *- h03 h05 h06 h08 h09 h11 h12 h14 h15 h17 h18 h20 h21 h23 h24 h26 h27
    simp [← Valid_ShiftCoreAir_4_8.bit_shift_def,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_7,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_6,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_5,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_4,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_3,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_2,
          ← Valid_ShiftCoreAir_4_8.bit_marker_sum_def_1] at *
    rcases h03 <;> [ skip; simp_all ]
    rcases h06 <;> [ skip; simp_all ]
    rcases h09 <;> [ skip; simp_all ]
    rcases h12 <;> [ skip; simp_all ]
    rcases h15 <;> [ skip; simp_all ]
    rcases h18 <;> [ skip; simp_all ]
    rcases h21 <;> [ skip; simp_all ]
    rcases h24 <;> simp_all

  simp only [execute_RTYPE_pure]

  simp [← BitVec.toNat_inj, BitVec.sshiftright_eq, eq_c_mod_32]
  rw [← U32.toBV_msb_negative] at b_sign_msb
  rw [BitVec.toNat_signExtend, if_pos b_sign_msb, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt
        (b := 2 ^ _)
        (by apply lt_of_lt_of_le (b := 2 ^ 32)
            . omega
            . apply pow_le_pow (by simp) (by simp) (by omega)
        )]
  rw [Nat.mod_eq_of_lt]; rotate_left
  . set x := ((lsm_1.val + 2 * lsm_2 + 3 * lsm_3) * 8 + ↑(air.core.bit_shift row 0))
    rw [Nat.shiftRight_eq_div_pow]
    suffices :
      ((U32.toBV #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0),
                    BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0)]).toNat + (2 ^ (32 + x) - 2 ^ 32))
        < 2 ^ (x + 32)
    . clear *- this
      simp [pow_add] at *
      apply Nat.div_lt_of_lt_mul; assumption
    . simp [pow_add]
      apply lt_of_lt_of_eq (b := 2 ^ 32 + (4294967296 * 2 ^ x - 4294967296))
      . grind
      . clear *-
        rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.mul_comm]
        . simp
        . have := Nat.one_le_pow x 2 (by simp)
          omega
  . simp [U32.toNat]
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]

    obtain ⟨ s_lsm_0, s_lsm_1, s_lsm_2, s_lsm_3 ⟩ :
      (lsm_0 = 1 → lsm_1 = 0 ∧ lsm_2 = 0 ∧ lsm_3 = 0) ∧
      (lsm_1 = 1 → lsm_0 = 0 ∧ lsm_2 = 0 ∧ lsm_3 = 0) ∧
      (lsm_2 = 1 → lsm_0 = 0 ∧ lsm_1 = 0 ∧ lsm_3 = 0) ∧
      (lsm_3 = 1 → lsm_0 = 0 ∧ lsm_1 = 0 ∧ lsm_2 = 0)
      := by clear *- h28 h37 h46 h55 h64; split_ands <;> grind

    have p0 : (air.core.a_0 row 0).val * (air.core.bit_multiplier_right row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind
    have p1 : (air.core.a_1 row 0).val * (air.core.bit_multiplier_right row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind
    have p2 : (air.core.a_2 row 0).val * (air.core.bit_multiplier_right row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind
    have p3 : (air.core.a_3 row 0).val * (air.core.bit_multiplier_right row 0).val ≤ 255 * 128 := by apply mul_le_mul <;> grind

    have neg_one : (((-1 + air.core.bit_multiplier_right row 0).val) : ℤ) = -1 + air.core.bit_multiplier_right row 0
    := by
      clear *- nz_bmr h_mul_right
      trans (((air.core.bit_multiplier_right row 0 - 1).val) : ℤ)
      . congr
      . omega

    rcases h28 with lsm0z | lsm0o; rotate_left

    . obtain ⟨ lsm1z, lsm2z, lsm3z ⟩ := s_lsm_0 lsm0o
      rw [lsm1z, lsm2z, lsm3z]
      simp [lsm0o, lsm1z, lsm2z, lsm3z] at *
      simp_all

      trans ((air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256 + (air.core.a_2 row 0) * 65536 + (air.core.a_3 row 0) * 16777216) * (air.core.bit_multiplier_right row 0).val / (air.core.bit_multiplier_right row 0).val
      . rw [Nat.mul_div_cancel
            (m := (air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256 + (air.core.a_2 row 0) * 65536 + (air.core.a_3 row 0) * 16777216)
            (n := (air.core.bit_multiplier_right row 0).val)
            (by grind)]
      . trans ((air.core.a_0 row 0 * air.core.bit_multiplier_right row 0).val +
              (air.core.a_1 row 0 * air.core.bit_multiplier_right row 0).val * 256 +
              (air.core.a_2 row 0 * air.core.bit_multiplier_right row 0).val * 65536 +
              (air.core.a_3 row 0 * air.core.bit_multiplier_right row 0).val * 16777216) / (air.core.bit_multiplier_right row 0).val
        . simp [Fin.val_mul]
          iterate 4 rw [Nat.mod_eq_of_lt (by omega)]
          ring_nf
        . rw [h30, h32, h34, h36]

          have p0' : (air.core.bit_shift_carry_1 row 0 * 256 + (air.core.b_0 row 0 - air.core.bit_shift_carry_0 row 0)).val ≤ 32640 := by omega
          have p1' : (air.core.bit_shift_carry_2 row 0 * 256 + (air.core.b_1 row 0 - air.core.bit_shift_carry_1 row 0)).val ≤ 32640 := by omega
          have p2' : (air.core.bit_shift_carry_3 row 0 * 256 + (air.core.b_2 row 0 - air.core.bit_shift_carry_2 row 0)).val ≤ 32640 := by omega

          rw [← add_sub_assoc] at p0' p1' p2'
          repeat rw [← add_sub_assoc]

          zify
          repeat rw [Fin.sub_val_of_le (by omega), Int.natCast_sub (by omega)]
          simp [Fin.val_add, Fin.val_mul]
          repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
          ring_nf
          have : 2 ^ (air.core.bit_shift row 0).val * 4294967296 - 4294967296 = (-1 + air.core.bit_multiplier_right row 0).val * 4294967296
            := by simp [eq_bmr, Fin.add_def]; grind
          rw [this]; clear this
          repeat rw [add_assoc]
          rw [add_comm (b := _ * 16777216)]
          simp [Nat.shiftRight_eq_div_pow, eq_bmr]
          rw [Int.add_ediv_of_dvd_right
              (by clear *- cases_bmr
                  rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                  simp_all <;>
                  omega)]
          rw [Int.add_ediv_of_dvd_right
                (a := ↑↑(air.core.b_0 row 0))
                (by clear *- cases_bmr
                    rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                    simp_all <;>
                    omega)]
          rw [add_right_cancel_iff]
          suffices : ((air.core.bit_multiplier_right row 0) : ℤ) ∣ ↑↑(air.core.b_0 row 0) - ↑↑(air.core.bit_shift_carry_0 row 0)
          . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
            simp_all <;>
            omega
          . suffices : ((air.core.bit_multiplier_right row 0) : ℕ) ∣ (air.core.bit_shift_carry_1 row 0 * 256 + (air.core.b_0 row 0 - air.core.bit_shift_carry_0 row 0)).val
            . zify at this
              rw [← add_sub_assoc,
                  Fin.sub_val_of_le (by omega),
                  Int.natCast_sub (by omega)] at this
              rw [Fin.val_add, Nat.mod_eq_of_lt (by grind)] at this
              rw [Fin.val_mul, Nat.mod_eq_of_lt (by grind)] at this
              simp [add_sub_assoc] at this
              apply Int.dvd_iff_dvd_of_dvd_add at this
              rw [← this]
              rcases cases_bmr with h | h | h | h | h | h | h | h <;>
              simp [h] <;>
              omega
            . rw [← h30]
              simp [Fin.mul_def]
              rw [Nat.mod_eq_of_lt (by omega)]
              simp

    . rcases h37 with lsm1z | lsm1o; rotate_left

      . obtain ⟨ lsm0z, lsm2z, lsm3z ⟩ := s_lsm_1 lsm1o
        simp [lsm0z, lsm1o, lsm2z, lsm3z] at *
        simp_all

        . trans ((air.core.b_1 row 0).val + (air.core.b_2 row 0) * 256 + (air.core.b_3 row 0) * 65536 + (2 ^ (32 + (air.core.bit_shift row 0).val) - 16777216)) / (air.core.bit_multiplier_right row 0).val
          . trans ((air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256 + (air.core.a_2 row 0) * 65536 + 4278190080) * (air.core.bit_multiplier_right row 0).val / (air.core.bit_multiplier_right row 0).val
            . rw [Nat.mul_div_cancel
                  (m := (air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256 + (air.core.a_2 row 0) * 65536 + 4278190080)
                  (n := (air.core.bit_multiplier_right row 0).val)
                  (by grind)]
            . trans ((air.core.a_0 row 0 * air.core.bit_multiplier_right row 0).val +
                    (air.core.a_1 row 0 * air.core.bit_multiplier_right row 0).val * 256 +
                    (air.core.a_2 row 0 * air.core.bit_multiplier_right row 0).val * 65536 +
                    4278190080 * (air.core.bit_multiplier_right row 0).val) / (air.core.bit_multiplier_right row 0).val
              . simp [Fin.val_mul]
                iterate 3 rw [Nat.mod_eq_of_lt (by omega)]
                ring_nf
              . rw [h39, h41, h43]
                have p1' : (air.core.bit_shift_carry_2 row 0 * 256 + (air.core.b_1 row 0 - air.core.bit_shift_carry_1 row 0)).val ≤ 32640 := by omega
                have p2' : (air.core.bit_shift_carry_3 row 0 * 256 + (air.core.b_2 row 0 - air.core.bit_shift_carry_2 row 0)).val ≤ 32640 := by omega

                rw [← add_sub_assoc] at p1' p2'
                repeat rw [← add_sub_assoc]
                repeat rw [Fin.sub_val_of_le (by omega)]
                simp [Fin.val_add, Fin.val_mul]
                repeat rw [Nat.mod_eq_of_lt (by omega)]
                zify
                repeat rw [Int.natCast_sub (by omega)]
                simp only [Int.natCast_add, Int.natCast_mul]
                ring_nf
                rw [eq_bmr, Int.natCast_sub (by omega)]
                simp [neg_one]
                repeat rw [add_assoc]
                rw [Int.add_ediv_of_dvd_right
                    (by clear *- cases_bmr
                        rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                        simp_all <;>
                        omega)]
                rw [Int.add_ediv_of_dvd_right
                      (a := ↑↑(air.core.b_1 row 0))
                      (by clear *- cases_bmr
                          rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                          simp_all <;>
                          omega)]
                ring_nf
                rw [add_comm]
                rw [add_left_cancel_iff]
                suffices : ((air.core.bit_multiplier_right row 0) : ℤ) ∣ ↑↑(air.core.b_1 row 0) - ↑↑(air.core.bit_shift_carry_1 row 0)
                . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                  simp_all <;>
                  omega
                . suffices : ((air.core.bit_multiplier_right row 0) : ℕ) ∣ (air.core.bit_shift_carry_2 row 0 * 256 + (air.core.b_1 row 0 - air.core.bit_shift_carry_1 row 0)).val
                  . zify at this
                    rw [← add_sub_assoc,
                        Fin.sub_val_of_le (by omega),
                        Int.natCast_sub (by omega)] at this
                    rw [Fin.val_add, Nat.mod_eq_of_lt (by grind)] at this
                    rw [Fin.val_mul, Nat.mod_eq_of_lt (by grind)] at this
                    simp [add_sub_assoc] at this
                    apply Int.dvd_iff_dvd_of_dvd_add at this
                    rw [← this]
                    rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                    simp [h] <;>
                    omega
                  . rw [← h39]
                    simp [Fin.mul_def]
                    rw [Nat.mod_eq_of_lt (by omega)]
                    simp
          . rw [Nat.shiftRight_eq_div_pow]
            simp [pow_add, eq_bmr]
            rcases cases_bmr with h | h | h | h | h | h | h | h <;>
            simp [h] <;>
            ring_nf <;>
            grind

      . rcases h46 with lsm2z | lsm2o; rotate_left

        . obtain ⟨ lsm0z, lsm1z, lsm3z ⟩ := s_lsm_2 lsm2o
          simp [lsm0z, lsm1z, lsm2o, lsm3z] at *
          simp_all

          . trans ((air.core.b_2 row 0).val + (air.core.b_3 row 0) * 256 + (2 ^ (32 + (air.core.bit_shift row 0).val) - 65536)) / (air.core.bit_multiplier_right row 0).val
            . trans ((air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256 + 16711680 + 4278190080) * (air.core.bit_multiplier_right row 0).val / (air.core.bit_multiplier_right row 0).val
              . rw [Nat.mul_div_cancel
                    (m := (air.core.a_0 row 0).val + (air.core.a_1 row 0) * 256 + 16711680 + 4278190080)
                    (n := (air.core.bit_multiplier_right row 0).val)
                    (by grind)]
              . trans ((air.core.a_0 row 0 * air.core.bit_multiplier_right row 0).val +
                      (air.core.a_1 row 0 * air.core.bit_multiplier_right row 0).val * 256 +
                      16711680 * (air.core.bit_multiplier_right row 0).val +
                      4278190080 * (air.core.bit_multiplier_right row 0).val) / (air.core.bit_multiplier_right row 0).val
                . simp [Fin.val_mul]
                  iterate 2 rw [Nat.mod_eq_of_lt (by omega)]
                  ring_nf
                . rw [h48, h50]
                  have p2' : (air.core.bit_shift_carry_3 row 0 * 256 + (air.core.b_2 row 0 - air.core.bit_shift_carry_2 row 0)).val ≤ 32640 := by omega

                  rw [← add_sub_assoc] at p2'
                  repeat rw [← add_sub_assoc]
                  repeat rw [Fin.sub_val_of_le (by omega)]
                  simp [Fin.val_add, Fin.val_mul]
                  repeat rw [Nat.mod_eq_of_lt (by omega)]
                  zify
                  repeat rw [Int.natCast_sub (by omega)]
                  simp only [Int.natCast_add, Int.natCast_mul]
                  ring_nf
                  rw [eq_bmr, Int.natCast_sub (by omega)]
                  simp [neg_one]
                  repeat rw [add_assoc]
                  rw [Int.add_ediv_of_dvd_right
                      (by clear *- cases_bmr
                          rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                          simp_all <;>
                          omega)]
                  rw [Int.add_ediv_of_dvd_right
                        (a := ↑↑(air.core.b_2 row 0))
                        (by clear *- cases_bmr
                            rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                            simp_all <;>
                            omega)]
                  ring_nf
                  rw [add_comm]
                  rw [add_left_cancel_iff]
                  suffices : ((air.core.bit_multiplier_right row 0) : ℤ) ∣ ↑↑(air.core.b_2 row 0) - ↑↑(air.core.bit_shift_carry_2 row 0)
                  . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                    simp_all <;>
                    omega
                  . suffices : ((air.core.bit_multiplier_right row 0) : ℕ) ∣ (air.core.bit_shift_carry_3 row 0 * 256 + (air.core.b_2 row 0 - air.core.bit_shift_carry_2 row 0)).val
                    . zify at this
                      rw [← add_sub_assoc,
                          Fin.sub_val_of_le (by omega),
                          Int.natCast_sub (by omega)] at this
                      rw [Fin.val_add, Nat.mod_eq_of_lt (by grind)] at this
                      rw [Fin.val_mul, Nat.mod_eq_of_lt (by grind)] at this
                      simp [add_sub_assoc] at this
                      apply Int.dvd_iff_dvd_of_dvd_add at this
                      rw [← this]
                      rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                      simp [h] <;>
                      omega
                    . rw [← h48]
                      simp [Fin.mul_def]
                      rw [Nat.mod_eq_of_lt (by omega)]
                      simp
            . rw [Nat.shiftRight_eq_div_pow]
              simp [pow_add, eq_bmr]
              rcases cases_bmr with h | h | h | h | h | h | h | h <;>
              simp [h] <;>
              ring_nf <;>
              grind

        . rcases h55 with lsm3z | lsm3o; rotate_left

          . obtain ⟨ lsm0z, lsm1z, lsm2z ⟩ := s_lsm_3 lsm3o
            simp [lsm0z, lsm1z, lsm2z, lsm3o] at *
            simp [h63] at *; rw [h61] at *; rw [h59] at *
            simp_all

            . trans ((air.core.b_3 row 0).val + (2 ^ (32 + (air.core.bit_shift row 0).val) - 256)) / (air.core.bit_multiplier_right row 0).val
              . trans ((air.core.a_0 row 0).val + 65280 + 16711680 + 4278190080) * (air.core.bit_multiplier_right row 0).val / (air.core.bit_multiplier_right row 0).val
                . rw [Nat.mul_div_cancel
                      (m := (air.core.a_0 row 0).val + 65280 + 16711680 + 4278190080)
                      (n := (air.core.bit_multiplier_right row 0).val)
                      (by grind)]
                . trans ((air.core.a_0 row 0 * air.core.bit_multiplier_right row 0).val +
                        65280 * (air.core.bit_multiplier_right row 0).val +
                        16711680 * (air.core.bit_multiplier_right row 0).val +
                        4278190080 * (air.core.bit_multiplier_right row 0).val) / (air.core.bit_multiplier_right row 0).val
                  . simp [Fin.val_mul]
                    rw [Nat.mod_eq_of_lt (by omega)]
                    ring_nf
                  . rw [h57]
                    have p3' : ((air.core.bit_multiplier_right row 0 - 1) * 256 + air.core.b_3 row 0 - air.core.bit_shift_carry_3 row 0).val ≤ 32640 := by omega

                    repeat rw [← add_sub_assoc]
                    repeat rw [Fin.sub_val_of_le (by omega)]
                    simp [Fin.val_add, Fin.val_mul]
                    repeat rw [Nat.mod_eq_of_lt (by omega)]
                    zify
                    repeat rw [Int.natCast_sub (by omega)]
                    simp only [Int.natCast_add, Int.natCast_mul]
                    ring_nf
                    rw [eq_bmr, Int.natCast_sub (by omega)]
                    simp [neg_one]
                    repeat rw [add_assoc]
                    ring_nf
                    rw [add_comm]
                    rw [Int.add_ediv_of_dvd_right
                        (by clear *- cases_bmr
                            rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                            simp_all)]
                    rw [add_comm (b := ((air.core.b_3 row 0) : ℤ))]
                    rw [Int.add_ediv_of_dvd_right
                          (a := ↑↑(air.core.b_3 row 0))
                          (by clear *- cases_bmr
                              rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                              simp_all)]
                    ring_nf
                    rw [add_comm]
                    rw [add_left_cancel_iff]
                    suffices : ((air.core.bit_multiplier_right row 0) : ℤ) ∣ ↑↑(air.core.b_3 row 0) - ↑↑(air.core.bit_shift_carry_3 row 0)
                    . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                      simp_all <;>
                      omega
                    . suffices : ((air.core.bit_multiplier_right row 0) : ℕ) ∣ ((air.core.bit_multiplier_right row 0 - 1) * 256 + (air.core.b_3 row 0 - air.core.bit_shift_carry_3 row 0)).val
                      . zify at this
                        rw [← add_sub_assoc] at this
                        rw [Fin.sub_val_of_le (by omega),
                            Int.natCast_sub (by omega)] at this
                        simp [Fin.add_def] at this
                        rw [Int.emod_eq_of_lt (by omega) (by omega)] at this
                        rw [add_sub_assoc] at this
                        rw [← Int.dvd_add_right (b := ↑↑((air.core.bit_multiplier_right row 0 - 1) * 256))]
                        . assumption
                        . rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                          simp [h]
                      . rw [← h57]
                        simp [Fin.mul_def]
                        rw [Nat.mod_eq_of_lt (by omega)]
                        simp
              . rw [Nat.shiftRight_eq_div_pow]
                simp [pow_add, eq_bmr]
                rcases cases_bmr with h | h | h | h | h | h | h | h <;>
                simp [h] <;>
                ring_nf <;>
                omega
          . simp_all

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the
    three base Shift opcodes for:
    - the `b` operand read from memory; and
    - the `c` operand as per the circuit
--/
theorem spec_base_Shift
:
  (U32.toBV #v[(air.core.a_0 row 0).val,
               (air.core.a_1 row 0).val,
               (air.core.a_2 row 0).val,
               (air.core.a_3 row 0).val])
    =
  execute_RTYPE_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    (rop_of_Shift_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  have essentials := essentials _ air row row_in_range constraints row_valid propertiesToAssume
  have opcodes : ((air.core.ctx row 0).instruction.opcode = 517 ∨
                  (air.core.ctx row 0).instruction.opcode = 518 ∨
                  (air.core.ctx row 0).instruction.opcode = 519) := by grind
  clear essentials

  obtain ⟨ op0, op1, op2 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  rcases opcodes with sll | srl | sra
  . have := @spec_base_SLL _ _ air row row_in_range constraints row_valid propertiesToAssume
    simp_all [rop_of_Shift_opcode]
  . have := @spec_base_SRL _ _ air row row_in_range constraints row_valid propertiesToAssume
    simp_all [rop_of_Shift_opcode]
  . obtain ⟨ b_b_sign, b_sign_msb ⟩ := b_sign_properties _ air row row_in_range constraints row_valid propertiesToAssume
    rcases b_b_sign with hbz | hb0
    . have := @spec_base_SRL _ _ air row row_in_range constraints row_valid propertiesToAssume
      trans execute_RTYPE_pure
              (U32.toBV
                #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0),
                  BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0)])
              (U32.toBV
                #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0),
                  BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)])
              rop.SRL
      . apply this; right; simp_all
      . clear this
        simp_all [execute_RTYPE_pure, rop_of_Shift_opcode]
        symm; apply BitVec.sshiftRight_eq_of_msb_false
        rw [← U32.toBV_msb_negative] at b_sign_msb
        grind
    . simp only [rop_of_Shift_opcode, sra, Fin.reduceEq, ↓reduceIte]
      apply op2 at sra
      have := @spec_base_SRA _ _ air row row_in_range constraints row_valid propertiesToAssume sra hb0
      assumption

end General

section NonImmediate

include
  row_valid
  constraints
  propertiesToAssume in
/-- The non-immediate variants of the five base ALU opcodes
    are implemented as per the RISC-V spec -/
theorem spec_base_Shift_non_imm
  (_ : air.adapter.rs2_as row 0 = 1)
:
  (U32.toBV #v[(air.core.a_0 row 0).val,
               (air.core.a_1 row 0).val,
               (air.core.a_2 row 0).val,
               (air.core.a_3 row 0).val])
    =
  execute_RTYPE_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    (rop_of_Shift_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  apply spec_base_Shift <;> assumption

end NonImmediate

section Immediate

/-- From Shift opcode to RISC-V opcode -/
def iop_of_Shift_opcode (opcode : FBB) : sop :=
  if opcode = 517 then .SLLI else
  if opcode = 518 then .SRLI else .SRAI

include
  row_valid
  constraints
  propertiesToAssume in
/-- The immediate variants of the five base ALU opcodes
    are implemented as per the RISC-V spec -/
theorem spec_base_ALU_imm
  (h_imm : air.adapter.rs2_as row 0 = 0)
:
  (U32.toBV #v[(air.core.a_0 row 0).val,
               (air.core.a_1 row 0).val,
               (air.core.a_2 row 0).val,
               (air.core.a_3 row 0).val])
    =
  execute_SHIFTIOP_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (BitVec.ofNat 6 (air.adapter.rs2 row 0).val)
    (iop_of_Shift_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  have propertiesToAssume' := propertiesToAssume
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume'
  clear pa_exec pa_mem pa_range pa_bit

  simp [row_valid,
        VmAirWrapper_shift_constraint_and_interaction_simplification,
        VmAirWrapper_shift.constraints.propertiesToAssume] at pa_read
  repeat rw [Fin.ext_iff] at pa_read
  obtain ⟨ ri_rd, ri_rs1, ri_rs2_non_imm, ri_imm ⟩ := pa_read

  suffices eq_c
  : U32.toBV #v[(air.core.c_0 row 0).val,
                (air.core.c_1 row 0).val,
                (air.core.c_2 row 0).val,
                (air.core.c_3 row 0).val]
      = (BitVec.setWidth 32 (BitVec.ofNat 6 ↑(air.adapter.rs2 row 0)))
  . trans execute_RTYPE_pure
            (U32.toBV #v[(air.core.b_0 row 0).val,
                         (air.core.b_1 row 0).val,
                         (air.core.b_2 row 0).val,
                         (air.core.b_3 row 0).val])
            (U32.toBV #v[(air.core.c_0 row 0).val,
                         (air.core.c_1 row 0).val,
                         (air.core.c_2 row 0).val,
                         (air.core.c_3 row 0).val])
            (rop_of_Shift_opcode (air.core.ctx row 0).instruction.opcode)
    . apply spec_base_Shift <;> assumption
    . simp [execute_SHIFTIOP_pure]
      rw [← eq_c]; congr

      have opcodes := opcode_bounds air row row_in_range constraints row_valid
      simp [rop_of_Shift_opcode, iop_of_Shift_opcode]
      grind
  . simp [*, ← BitVec.toNat_inj]
    trans (BitVec.ofNat 24 (air.adapter.rs2 row 0).val).toNat
    . have essentials := essentials _ air row row_in_range constraints row_valid propertiesToAssume
      simp [h_imm, and_assoc] at essentials
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
               opcodes, h_rs2, imm_sign_extend, rs2_as_imm, imm_sign, imm_sign_extend' ⟩ := essentials
      rw [← VmAirWrapper_shift.rs2_imm_def] at rs2_as_imm
      rw [← VmAirWrapper_shift.rs2_sign_limbs] at imm_sign
      simp [rs2_as_imm, Fin.val_add, Fin.val_mul]
      simp [U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (by omega)]
      grind
    . grind

end Immediate

end Shift.ValidRows
