import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_divrem
import OpenvmFv.Constraints.VmAirWrapper_divrem
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000
set_option synthInstance.maxHeartbeats 1_000_000

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_divrem FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_divrem.constraints.allHold air row row_in_range)

namespace DivRem.NonValidRows

open VmAirWrapper_divrem.constraints

variable (row_not_valid : air.core.is_valid row 0 = 0)

set_option maxRecDepth 1_000_000 in
include
  row_in_range
in
/-- Zeros required to form a non-valid row -/
lemma non_valid_row_Mul_allZeros_allHold
:
  constrain_interactions air ∧
  air.core.b_0 row 0 = 0 ∧
  air.core.b_1 row 0 = 0 ∧
  air.core.b_2 row 0 = 0 ∧
  air.core.b_3 row 0 = 0 ∧
  air.core.c_0 row 0 = 0 ∧
  air.core.c_1 row 0 = 0 ∧
  air.core.c_2 row 0 = 0 ∧
  air.core.c_3 row 0 = 0 ∧
  air.core.q_0 row 0 = 0 ∧
  air.core.q_1 row 0 = 0 ∧
  air.core.q_2 row 0 = 0 ∧
  air.core.q_3 row 0 = 0 ∧
  air.core.r_0 row 0 = 0 ∧
  air.core.r_1 row 0 = 0 ∧
  air.core.r_2 row 0 = 0 ∧
  air.core.r_3 row 0 = 0 ∧
  air.core.zero_divisor row 0 = 0 ∧
  air.core.r_zero row 0 = 0 ∧
  air.core.b_sign row 0 = 0 ∧
  air.core.c_sign row 0 = 0 ∧
  air.core.q_sign row 0 = 0 ∧
  air.core.c_ext row 0 = 0 ∧
  air.core.sign_xor row 0 = 0 ∧
  air.core.c_sum_inv row 0 = 0 ∧
  air.core.r_sum_inv row 0 = 0 ∧
  air.core.r_prime_0 row 0 = 0 ∧
  air.core.r_prime_1 row 0 = 0 ∧
  air.core.r_prime_2 row 0 = 0 ∧
  air.core.r_prime_3 row 0 = 0 ∧
  air.core.r_inv_0 row 0 = 0 ∧
  air.core.r_inv_1 row 0 = 0 ∧
  air.core.r_inv_2 row 0 = 0 ∧
  air.core.r_inv_3 row 0 = 0 ∧
  air.core.lt_marker_0 row 0 = 0 ∧
  air.core.lt_marker_1 row 0 = 0 ∧
  air.core.lt_marker_2 row 0 = 0 ∧
  air.core.lt_marker_3 row 0 = 0 ∧
  air.core.lt_diff row 0 = 0 ∧
  air.core.opcode_div_flag row 0 = 0 ∧
  air.core.opcode_divu_flag row 0 = 0 ∧
  air.core.opcode_rem_flag row 0 = 0 ∧
  air.core.opcode_remu_flag row 0 = 0
    → air.core.is_valid row 0 = 0 ∧
      allHold air row row_in_range
:= by
  rw [allHold_simplified_of_allHold]
  intro ⟨ h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
          h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
          h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
          h30, h31, h32, h33, h34, h35, h36, h37, h38, h39,
          h40, h41, h42 ⟩
  simp [VmAirWrapper_divrem_constraint_and_interaction_simplification,
        ← DivRemCoreAir_4_8.is_valid_def,
        ← DivRemCoreAir_4_8.special_case_def,
        ← DivRemCoreAir_4_8.c_sum_def,
        ← DivRemCoreAir_4_8.valid_and_not_zero_divisor_def,
        ← DivRemCoreAir_4_8.r_sum_def,
        ← DivRemCoreAir_4_8.valid_and_not_special_case_def,
        ← DivRemCoreAir_4_8.signed_def,
        ← DivRemCoreAir_4_8.nonzero_q_def,
        ← DivRemCoreAir_4_8.carry_lt_0_def,
        ← DivRemCoreAir_4_8.carry_lt_1_def,
        ← DivRemCoreAir_4_8.carry_lt_2_def,
        ← DivRemCoreAir_4_8.carry_lt_3_def]
  grind

include
  row_in_range
  row_not_valid
  constraints
in
/-- On non-valid rows, all interactin multiplicities equal zero -/
lemma non_valid_row_Mul_all_interaction_multiplicities_zero
  (entry : FBB × List FBB)
:
  entry ∈ executionBus_row air row ++
          memoryBus_row air row ++
          rangeCheckerBus_row air row ++
          programBus_row air row ++
          rangeTupleCheckerBus_row air row ++
          bitwiseBus_row air row → entry.1 = 0
:= by
  obtain ⟨ hint, constraints ⟩ := constraints
  clear hint; unfold extracted_row_constraint_list at constraints
  simp only [VmAirWrapper_divrem_air_simplification,
             VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
  simp at constraints
  simp_all
      [VmAirWrapper_divrem_constraint_and_interaction_simplification,
        ← DivRemCoreAir_4_8.is_valid_def,
        ← DivRemCoreAir_4_8.special_case_def,
        ← DivRemCoreAir_4_8.c_sum_def,
        ← DivRemCoreAir_4_8.valid_and_not_zero_divisor_def,
        ← DivRemCoreAir_4_8.r_sum_def,
        ← DivRemCoreAir_4_8.valid_and_not_special_case_def,
        ← DivRemCoreAir_4_8.signed_def,
        ← DivRemCoreAir_4_8.nonzero_q_def,
        ← DivRemCoreAir_4_8.carry_lt_0_def,
        ← DivRemCoreAir_4_8.carry_lt_1_def,
        ← DivRemCoreAir_4_8.carry_lt_2_def,
        ← DivRemCoreAir_4_8.carry_lt_3_def]
  simp [or_imp]
  split_ands <;> intro hyp <;> simp [hyp]
  . obtain ⟨ h0, h1, h2, h3, rest ⟩ := constraints
    clear rest
    grind
  . suffices : air.core.zero_divisor row 0 + air.core.r_zero row 0 = 0
    . grind
    . obtain ⟨ z0, z1, z2, z3 ⟩ :
        air.core.opcode_div_flag row 0 = 0 ∧
        air.core.opcode_divu_flag row 0 = 0 ∧
        air.core.opcode_rem_flag row 0 = 0 ∧
        air.core.opcode_remu_flag row 0 = 0
      := by
        obtain ⟨ h0, h1, h2, h3, rest ⟩ := constraints
        clear rest
        grind
      simp [z0, z1, z2, z3] at constraints
      grind

end DivRem.NonValidRows

open VmAirWrapper_divrem.constraints

namespace DivRem.ValidRows

variable (row_valid : air.core.is_valid row 0 = 1)

-- Row assumptions, properties to assume, and properties to prove
variable
  (assumptions : assumptionsPerRow air row)
  (propertiesToAssume : wf_propertiesToAssumePerRow air row)

section General

set_option maxRecDepth 1_000_000 in
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
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_divrem_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ub_q0, ub_cq0, ub_q1, ub_cq1, ub_q2, ub_cq2, ub_q3, ub_cq3,
           ub_r0, ub_cr0, ub_r1, ub_cr1, ub_r2, ub_cr2, ub_r3, ub_cr3 ⟩ := pa_rtc
  obtain ⟨ h_signed_msb, h_diff ⟩ := pa_bit
  clear pa_read

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
           b_zd, h_zd_c0, h_zd_q0, h_zd_c1, h_zd_q1, h_zd_c2, h_zd_q2, h_zd_c3, h_zd_q3,
           b_vnzd, h_vnzd,
           b_rz, b_rz_r0, b_rz_r1, b_rz_r2, b_rz_r3,
           b_vnsc, h_vnsc,
           b_bsgn, b_csgn, h_bsgn, h_csgn, h_xor_eq,
           b_qsgn, h_xor_qsgn_eq, h_xor_qsgn_z,
           h_r'_0, b_lt_0, h_r'inv_0, h_lt_0,
           h_r'_1, b_lt_1, h_r'inv_1, h_lt_1,
           h_r'_2, b_lt_2, h_r'inv_2, h_lt_2,
           h_r'_3, b_lt_3, h_r'inv_3, h_lt_3,
           b_ltm_3, h_prod_3, h_diff_3,
           b_ltm_2, h_prod_2, h_diff_2,
           b_ltm_1, h_prod_1, h_diff_1,
           b_ltm_0, h_prod_0, h_diff_0,
           h_sum_sc_ltm,
           rest ⟩ := constraints
  clear constrain_interactions rest
  simp_all [VmAirWrapper_divrem_constraint_and_interaction_simplification,
            wf_propertiesToAssertPerRow,
            propertiesToAssert]
  repeat rw [← and_assoc]
  constructor
  . constructor
    . simp [← DivRemCoreAir_4_8.a_0_def,
            ← DivRemCoreAir_4_8.a_1_def,
            ← DivRemCoreAir_4_8.a_2_def,
            ← DivRemCoreAir_4_8.a_3_def]
      clear *- ub_q0 ub_q1 ub_q2 ub_q3 ub_r0 ub_r1 ub_r2 ub_r3
               b_div b_divu b_rem b_remu row_valid
      simp [← DivRemCoreAir_4_8.is_valid_def] at row_valid
      grind
    . simp [← DivRemCoreAir_4_8.signed_def]
      clear *- b_div b_divu b_rem b_remu row_valid
      grind
  . simp [← DivRemCoreAir_4_8.valid_and_not_special_case_def,
          row_valid]
    clear *- b_sc
    grind

set_option maxRecDepth 1_000_000 in
include
  row_valid
  constraints
  assumptions
  propertiesToAssume
in
/-- Some properties more important than others that should
    be easily accessible -/
lemma essentials
:
  (air.adapter.from_state.pc row 0).val + 4 < 1073741824 ∧
  (air.core.a row 0 0).val < 256 ∧ (air.core.a row 0 1).val < 256 ∧ (air.core.a row 0 2).val < 256 ∧ (air.core.a row 0 3).val < 256 ∧
  (air.core.b_0 row 0).val < 256 ∧ (air.core.b_1 row 0).val < 256 ∧ (air.core.b_2 row 0).val < 256 ∧ (air.core.b_3 row 0).val < 256 ∧
  (air.core.c_0 row 0).val < 256 ∧ (air.core.c_1 row 0).val < 256 ∧ (air.core.c_2 row 0).val < 256 ∧ (air.core.c_3 row 0).val < 256 ∧
  (((air.core.ctx row 0).instruction.opcode = 596 ∨ (air.core.ctx row 0).instruction.opcode = 597) →
      air.core.a row 0 0 = air.core.q_0 row 0 ∧ air.core.a row 0 1 = air.core.q_1 row 0 ∧ air.core.a row 0 2 = air.core.q_2 row 0 ∧ air.core.a row 0 3 = air.core.q_3 row 0) ∧
  (((air.core.ctx row 0).instruction.opcode = 598 ∨ (air.core.ctx row 0).instruction.opcode = 599) →
      air.core.a row 0 0 = air.core.r_0 row 0 ∧ air.core.a row 0 1 = air.core.r_1 row 0 ∧ air.core.a row 0 2 = air.core.r_2 row 0 ∧ air.core.a row 0 3 = air.core.r_3 row 0)
:= by
  have props_asrt := wf_propertiesToAssert ExtF air row row_in_range constraints row_valid propertiesToAssume

  obtain ⟨ sop0, sop1, sop2, sop3 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2, op3 ⟩ := op_from_opcode air row row_in_range constraints row_valid
  clear constraints

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_divrem_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ub_q0, ub_cq0, ub_q1, ub_cq1, ub_q2, ub_cq2, ub_q3, ub_cq3,
           ub_r0, ub_cr0, ub_r1, ub_cr1, ub_r2, ub_cr2, ub_r3, ub_cr3 ⟩ := pa_rtc
  clear pa_bit pa_read

  simp_all [VmAirWrapper_divrem_constraint_and_interaction_simplification,
            wf_propertiesToAssertPerRow,
            propertiesToAssert]

  simp [← DivRemCoreAir_4_8.a_0_def,
        ← DivRemCoreAir_4_8.a_1_def,
        ← DivRemCoreAir_4_8.a_2_def,
        ← DivRemCoreAir_4_8.a_3_def]

  split_ands
  . clear *- assumptions; grind
  . intro h_op; rcases h_op with h_op | h_op <;> simp_all
  . intro h_op; rcases h_op with h_op | h_op <;> simp_all

section signed

lemma divrem_split
{ b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 q0 q1 q2 q3 r0 r1 r2 r3 c_ext q_ext r_ext : FBB }
(ub_b0 : b0.val < 256)
(ub_b1 : b1.val < 256)
(ub_b2 : b2.val < 256)
(ub_b3 : b3.val < 256)
(ub_b4 : b4.val < 256)
(ub_b5 : b5.val < 256)
(ub_b6 : b6.val < 256)
(ub_b7 : b7.val < 256)
(ub_c0 : c0.val < 256)
(ub_c1 : c1.val < 256)
(ub_c2 : c2.val < 256)
(ub_c3 : c3.val < 256)
(ub_q0 : q0.val < 256)
(ub_q1 : q1.val < 256)
(ub_q2 : q2.val < 256)
(ub_q3 : q3.val < 256)
(ub_r0 : r0.val < 256)
(ub_r1 : r1.val < 256)
(ub_r2 : r2.val < 256)
(ub_r3 : r3.val < 256)
(ub_ce : c_ext.val < 256)
(ub_qe : q_ext.val < 256)
(ub_re : r_ext.val < 256)
(ub_cry0 : (2005401601 * ((r0 + c0 * q0) - b0)).val < 2048)
(ub_cry1 : (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1)).val < 2048)
(ub_cry2 : (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2)).val < 2048)
(ub_cry3 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2) + (r3 + c0 * q3 + c1 * q2 + c2 * q1 + c3 * q0) - b3)).val < 2048)
(ub_cry4 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2) + (r3 + c0 * q3 + c1 * q2 + c2 * q1 + c3 * q0) - b3) + (r_ext + c1 * q3 + c2 * q2 + c3 * q1 + c0 * q_ext + q0 * c_ext) - b4)).val < 2048)
(ub_cry5 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2) + (r3 + c0 * q3 + c1 * q2 + c2 * q1 + c3 * q0) - b3) + (r_ext + c1 * q3 + c2 * q2 + c3 * q1 + c0 * q_ext + q0 * c_ext) - b4) + (r_ext + c2 * q3 + c3 * q2 + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext) - b5)).val < 2048)
(ub_cry6 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2) + (r3 + c0 * q3 + c1 * q2 + c2 * q1 + c3 * q0) - b3) + (r_ext + c1 * q3 + c2 * q2 + c3 * q1 + c0 * q_ext + q0 * c_ext) - b4) + (r_ext + c2 * q3 + c3 * q2 + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext) - b5) + (r_ext + c3 * q3 + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext + c2 * q_ext + q2 * c_ext) - b6)).val < 2048)
(ub_cry7 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2) + (r3 + c0 * q3 + c1 * q2 + c2 * q1 + c3 * q0) - b3) + (r_ext + c1 * q3 + c2 * q2 + c3 * q1 + c0 * q_ext + q0 * c_ext) - b4) + (r_ext + c2 * q3 + c3 * q2 + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext) - b5) + (r_ext + c3 * q3 + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext + c2 * q_ext + q2 * c_ext) - b6) + (r_ext + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext + c2 * q_ext + q2 * c_ext + c3 * q_ext + q3 * c_ext) - b7)).val < 2048)
:
  U64.toBV #v[BitVec.ofNat 8 b0, BitVec.ofNat 8 b1, BitVec.ofNat 8 b2, BitVec.ofNat 8 b3, BitVec.ofNat 8 b4, BitVec.ofNat 8 b5, BitVec.ofNat 8 b6, BitVec.ofNat 8 b7] =
  U64.toBV #v[BitVec.ofNat 8 c0, BitVec.ofNat 8 c1, BitVec.ofNat 8 c2, BitVec.ofNat 8 c3,
              BitVec.ofNat 8 c_ext, BitVec.ofNat 8 c_ext, BitVec.ofNat 8 c_ext, BitVec.ofNat 8 c_ext] *
  U64.toBV #v[BitVec.ofNat 8 q0, BitVec.ofNat 8 q1, BitVec.ofNat 8 q2, BitVec.ofNat 8 q3,
              BitVec.ofNat 8 q_ext, BitVec.ofNat 8 q_ext, BitVec.ofNat 8 q_ext, BitVec.ofNat 8 q_ext] +
  U64.toBV #v[BitVec.ofNat 8 r0, BitVec.ofNat 8 r1, BitVec.ofNat 8 r2, BitVec.ofNat 8 r3,
              BitVec.ofNat 8 r_ext, BitVec.ofNat 8 r_ext, BitVec.ofNat 8 r_ext, BitVec.ofNat 8 r_ext]
:= by
  replace ub_cry0 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry0; simp]
  replace ub_cry1 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry1; simp]
  replace ub_cry2 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry2; simp]
  replace ub_cry3 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry3; simp]
  replace ub_cry4 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry4; simp]
  replace ub_cry5 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry5; simp]
  replace ub_cry6 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry6; simp]
  replace ub_cry7 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry7; simp]

  have ub_p00 : c0.val * q0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_b0, eq_cry0 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_b0 ub_cry0
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_b0
  rw [Nat.mod_eq_of_lt (b := 2013265921) (by clear ub_cry1 ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7; omega)] at eq_b0
  rw [eq_cry0] at ub_cry1 ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry0 eq_cry0

  have ub_p01 : c0.val * q1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p10 : c1.val * q0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_b1, eq_cry1 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_b1 ub_cry1
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_b1
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by clear ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7; omega)] at eq_b1
  rw [eq_cry1] at ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry1 eq_cry1

  have ub_p02 : c0.val * q2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p11 : c1.val * q1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p20 : c2.val * q0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_b2, eq_cry2 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_b2 ub_cry2
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_b2
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by clear ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7; omega)] at eq_b2
  rw [eq_cry2] at ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry2 eq_cry2

  have ub_p03 : c0.val * q3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p12 : c1.val * q2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p21 : c2.val * q1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p30 : c3.val * q0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_b3, eq_cry3 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_b3 ub_cry3
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_b3
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by clear ub_cry4 ub_cry5 ub_cry6 ub_cry7; omega)] at eq_b3
  rw [eq_cry3] at ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry3 eq_cry3

  have ub_p13 : c1.val * q3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p22 : c2.val * q2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p31 : c3.val * q1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_ce0 : c0.val * q_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_qe0 : q0.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_b4, eq_cry4 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_b4 ub_cry4
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_b4
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by clear ub_cry5 ub_cry6 ub_cry7; omega)] at eq_b4
  rw [eq_cry4] at ub_cry5 ub_cry6 ub_cry7
  clear ub_cry4 eq_cry4

  have ub_p23 : c2.val * q3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p32 : c3.val * q2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_ce1 : c1.val * q_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_qe1 : q1.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_b5, eq_cry5 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_b5 ub_cry5
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_b5
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by clear ub_cry6 ub_cry7; omega)] at eq_b5
  rw [eq_cry5] at ub_cry6 ub_cry7
  clear ub_cry5 eq_cry5

  have ub_p33 : c3.val * q3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_ce2 : c2.val * q_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_qe2 : q2.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_b6, eq_cry6 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_b6 ub_cry6
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_b6
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by clear eq_cry6 ub_cry6 ub_cry7; omega)] at eq_b6
  rw [eq_cry6] at ub_cry7
  clear ub_cry6 eq_cry6

  have ub_ce3 : c3.val * q_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_qe3 : q3.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_b7, eq_cry7 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_b7 ub_cry7
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_b7
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_b7
  clear ub_cry7 eq_cry7

  rw [eq_b0, eq_b1, eq_b2, eq_b3, eq_b4, eq_b5, eq_b6, eq_b7]

  simp [← BitVec.toNat_inj, U64.toNat]
  rw [Nat.DivMod.div_8 (a := _ + _ * _), Nat.DivMod.div_16, Nat.DivMod.div_24,
      Nat.DivMod.div_32, Nat.DivMod.div_40, Nat.DivMod.div_48]
  rw [Nat.DivMod.join_8, Nat.DivMod.join_16, Nat.DivMod.join_24,
      Nat.DivMod.join_32, Nat.DivMod.join_40, Nat.DivMod.join_48, Nat.DivMod.join_56]

  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
  ring_nf
  omega

lemma divrem_quot_rem_sign
{ b0 b1 b2 b3 c0 c1 c2 c3 q0 q1 q2 q3 r0 r1 r2 r3 b_ext c_ext q_ext : FBB }
(ub_b0 : b0.val < 256)
(ub_b1 : b1.val < 256)
(ub_b2 : b2.val < 256)
(ub_b3 : b3.val < 256)
(ub_c0 : c0.val < 256)
(ub_c1 : c1.val < 256)
(ub_c2 : c2.val < 256)
(ub_c3 : c3.val < 256)
(ub_q0 : q0.val < 256)
(ub_q1 : q1.val < 256)
(ub_q2 : q2.val < 256)
(ub_q3 : q3.val < 256)
(ub_r0 : r0.val < 256)
(ub_r1 : r1.val < 256)
(ub_r2 : r2.val < 256)
(ub_r3 : r3.val < 256)
(ub_be : b_ext.val < 256)
(ub_ce : c_ext.val < 256)
(ub_qe : q_ext.val < 256)
(ub_cry0 : (2005401601 * ((r0 + c0 * q0) - b0)).val < 2048)
(ub_cry1 : (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1)).val < 2048)
(ub_cry2 : (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2)).val < 2048)
(ub_cry3 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2) + (r3 + c0 * q3 + c1 * q2 + c2 * q1 + c3 * q0) - b3)).val < 2048)
(ub_cry4 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2) + (r3 + c0 * q3 + c1 * q2 + c2 * q1 + c3 * q0) - b3) + (b_ext + c1 * q3 + c2 * q2 + c3 * q1 + c0 * q_ext + q0 * c_ext) - b_ext)).val < 2048)
(ub_cry5 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2) + (r3 + c0 * q3 + c1 * q2 + c2 * q1 + c3 * q0) - b3) + (b_ext + c1 * q3 + c2 * q2 + c3 * q1 + c0 * q_ext + q0 * c_ext) - b_ext) + (b_ext + c2 * q3 + c3 * q2 + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext) - b_ext)).val < 2048)
(ub_cry6 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2) + (r3 + c0 * q3 + c1 * q2 + c2 * q1 + c3 * q0) - b3) + (b_ext + c1 * q3 + c2 * q2 + c3 * q1 + c0 * q_ext + q0 * c_ext) - b_ext) + (b_ext + c2 * q3 + c3 * q2 + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext) - b_ext) + (b_ext + c3 * q3 + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext + c2 * q_ext + q2 * c_ext) - b_ext)).val < 2048)
(ub_cry7 : (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * (2005401601 * ((r0 + c0 * q0) - b0) + (r1 + c0 * q1 + c1 * q0) - b1) + (r2 + c0 * q2 + c1 * q1 + c2 * q0) - b2) + (r3 + c0 * q3 + c1 * q2 + c2 * q1 + c3 * q0) - b3) + (b_ext + c1 * q3 + c2 * q2 + c3 * q1 + c0 * q_ext + q0 * c_ext) - b_ext) + (b_ext + c2 * q3 + c3 * q2 + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext) - b_ext) + (b_ext + c3 * q3 + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext + c2 * q_ext + q2 * c_ext) - b_ext) + (b_ext + c0 * q_ext + q0 * c_ext + c1 * q_ext + q1 * c_ext + c2 * q_ext + q2 * c_ext + c3 * q_ext + q3 * c_ext) - b_ext)).val < 2048)
(h_c_nz : ¬(U32.toInt #v[c0, c1, c2, c3] = 0))
(h_r_nz : ¬(U32.toInt #v[r0, r1, r2, r3] = 0))
(h_b_ext : b_ext = U32.ext #v[b0.val, b1.val, b2.val, b3.val] true)
(h_c_ext : c_ext = U32.ext #v[c0.val, c1.val, c2.val, c3.val] true)
(h_q_ext : q_ext = if U32.toInt #v[q0.val, q1.val, q2.val, q3.val] = 0 then 0 else (if (b_ext = c_ext) then 0 else 255))
:
  q_ext = U32.ext #v[q0.val, q1.val, q2.val, q3.val] true ∧ b_ext = U32.ext #v[r0.val, r1.val, r2.val, r3.val] true
:= by
  have h_bv_eq :=
    @divrem_split
      b0 b1 b2 b3 b_ext b_ext b_ext b_ext
      c0 c1 c2 c3
      q0 q1 q2 q3
      r0 r1 r2 r3
      c_ext q_ext b_ext
      ub_b0 ub_b1 ub_b2 ub_b3 ub_be ub_be ub_be ub_be
      ub_c0 ub_c1 ub_c2 ub_c3 ub_q0 ub_q1 ub_q2 ub_q3
      ub_r0 ub_r1 ub_r2 ub_r3
      ub_ce ub_qe ub_be
      ub_cry0 ub_cry1 ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7

  have : U64.toBV
          #v[BitVec.ofNat 8 ↑b0, BitVec.ofNat 8 ↑b1, BitVec.ofNat 8 ↑b2, BitVec.ofNat 8 ↑b3, BitVec.ofNat 8 ↑b_ext,
             BitVec.ofNat 8 ↑b_ext, BitVec.ofNat 8 ↑b_ext, BitVec.ofNat 8 ↑b_ext] =
         U64.toBV (U32.extend #v[b0, b1, b2, b3] true)
  := by
    simp [U32.extend, h_b_ext, U32.ext, U32.negative, U32.toNat, BitVec.ofNat]
    split_ifs <;> congr
  rw [this] at h_bv_eq; clear this

  have : U64.toBV
          #v[BitVec.ofNat 8 ↑c0, BitVec.ofNat 8 ↑c1, BitVec.ofNat 8 ↑c2, BitVec.ofNat 8 ↑c3, BitVec.ofNat 8 ↑c_ext,
             BitVec.ofNat 8 ↑c_ext, BitVec.ofNat 8 ↑c_ext, BitVec.ofNat 8 ↑c_ext] =
         U64.toBV (U32.extend #v[c0, c1, c2, c3] true)
  := by
    simp [U32.extend, h_c_ext, U32.ext, U32.negative, U32.toNat, BitVec.ofNat]
    split_ifs <;> congr
  rw [this] at h_bv_eq; clear this

  clear ub_cry0 ub_cry1 ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7

  simp [← BitVec.toInt_inj] at h_bv_eq

  have ⟨ lb_b, ub_b ⟩ := U32.toInt_range #v[b0, b1, b2, b3]
  have ⟨ lb_c, ub_c ⟩ := U32.toInt_range #v[c0, c1, c2, c3]

  rw [h_bv_eq] at lb_b ub_b

  have mod_b : b0.val % 256 = b0 ∧ b1.val % 256 = b1 ∧ b2.val % 256 = b2 ∧ b3.val % 256 = b3 := by omega
  simp [mod_b] at *
  have mod_c : c0.val % 256 = c0 ∧ c1.val % 256 = c1 ∧ c2.val % 256 = c2 ∧ c3.val % 256 = c3 := by omega
  simp [mod_c] at *
  have mod_q : q0.val % 256 = q0 ∧ q1.val % 256 = q1 ∧ q2.val % 256 = q2 ∧ q3.val % 256 = q3 := by omega
  simp [mod_q] at *
  have mod_r : r0.val % 256 = r0 ∧ r1.val % 256 = r1 ∧ r2.val % 256 = r2 ∧ r3.val % 256 = r3 := by omega
  simp [mod_r] at *
  clear mod_b mod_c mod_q mod_r

  simp [U32.toInt] at *
  unfold U32.ext at *
  simp [U32.negative] at *
  simp [U32.toNat] at *

  have simp_mul : forall x, 4294967296 ≤ 2 * x ↔ 2147483648 ≤ x := by omega
  simp [simp_mul] at *; clear simp_mul
  clear mod_b mod_c mod_r

  by_cases h_q_nz_n : (q0 : ℕ) + ↑q1 * 256 + ↑q2 * 65536 + ↑q3 * 16777216 = 0
  . simp at h_q_nz_n
    simp [h_q_nz_n] at *
    simp [h_q_ext] at *
    conv at ub_b =>
      lhs; arg 1; arg 1
      simp [U64.toInt, U64.negative, U64.toNat]
    conv at lb_b =>
      rhs; arg 1; arg 1
      simp [U64.toInt, U64.negative, U64.toNat]
    conv at h_bv_eq =>
      rhs; arg 1; arg 1
      simp [U64.toInt, U64.negative, U64.toNat]
    simp [U64.toInt_bmod_eq] at h_bv_eq ub_b lb_b
    simp [U64.toInt, U64.negative, U64.toNat] at h_bv_eq ub_b lb_b
    split_ifs at h_b_ext with h_cond_bext
    . simp_all [-BabyBear.to_the_right_FBB_255]
      split_ifs at lb_b <;> omega
    . simp_all [-BabyBear.to_the_right_FBB_0]
      split_ifs at ub_b <;> omega
  . zify at h_q_nz_n
    rw [if_neg (by split_ifs <;> omega)] at h_q_ext
    split_ifs at h_b_ext with h_cond_bext <;>
    split_ifs at h_c_ext with h_cond_cext
    -- `b` and `c` both negative
    . simp_all [-BabyBear.to_the_right_FBB_255]
      clear lb_c ub_c h_bv_eq
      conv at lb_b =>
        rhs; arg 1; arg 1; arg 2
        simp [U64.toInt, U64.negative, U64.toNat]
        rw [if_neg (by omega)]
        simp
      repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at lb_b
      conv at ub_b =>
        lhs; arg 1; arg 1; arg 2
        simp [U64.toInt, U64.negative, U64.toNat]
        rw [if_neg (by omega)]
        simp
      repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at ub_b
      have ⟨ lb_cx, ub_cx ⟩ :
        -2147483648 ≤ (c0 : ℤ) + ↑↑c1 * 256 + ↑↑c2 * 65536 + ↑↑c3 * 16777216 - 4294967296 ∧
        (c0 : ℤ) + ↑↑c1 * 256 + ↑↑c2 * 65536 + ↑↑c3 * 16777216 - 4294967296 < 0
      := by omega
      have ⟨ lb_qx, ub_qx ⟩ :
        0 < (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 ∧
        (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 < 4294967296
      := by omega
      have ⟨ lb_r, ub_r ⟩ :
        0 < (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 ∧
        (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 < 4294967296
      := by clear *- ub_r0 ub_r1 ub_r2 ub_r3 h_r_nz; omega
      clear h_cond_bext h_cond_cext h_b_ext h_c_ext h_q_ext h_q_nz_n h_c_nz
      clear h_c_ext h_q_ext
      obtain ⟨ q, eq_q ⟩ : exists q, q = (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 := by simp
      suffices :
        q < 2147483648 ∧
        2147483648 ≤ (r0 : ℤ) + ↑r1 * 256 + ↑r2 * 65536 + ↑r3 * 16777216
      . rw [eq_q] at this; zify at this ⊢; clear *- this ub_q0 ub_q1 ub_q2 ub_q3 ub_r0 ub_r1 ub_r2 ub_r3; omega
      . rw [← eq_q] at lb_b ub_b lb_qx ub_qx; clear eq_q ub_q0 ub_q1 ub_q2 ub_q3 q0 q1 q2 q3
        rw [if_pos (by omega)] at lb_b ub_b
        obtain ⟨ c, eq_c ⟩ : exists c, c = (c0 : ℤ) + ↑↑c1 * 256 + ↑↑c2 * 65536 + ↑↑c3 * 16777216 - 4294967296 := by simp
        simp [← eq_c] at *; clear ub_c0 ub_c1 ub_c2 ub_c3 c0 c1 c2 c3 eq_c
        simp [U64.toInt, U64.negative, U64.toNat] at lb_b ub_b; clear h_b_ext
        rw [if_pos (by omega)] at lb_b ub_b
        have h_eq :
          c * q + (↑↑r0 % 256 + ↑↑r1 % 256 * 256 + ↑↑r2 % 256 * 65536 + ↑↑r3 % 256 * 16777216 + 1095216660480 + 280375465082880 + 71776119061217280 + 18374686479671623680 - 18446744073709551616) =
          c * q + (↑↑r0 + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 - 4294967296)
          := by omega
        rw [h_eq] at lb_b ub_b; clear h_eq ub_b0 ub_b1 ub_b2 ub_b3 b0 b1 b2 b3
        obtain ⟨ r, eq_r ⟩ : exists r, r = (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 := by simp
        simp [← eq_r] at *; clear h_r_nz ub_r0 ub_r1 ub_r2 ub_r3 r0 r1 r2 r3 eq_r
        by_cases h_q : q < 2147483648
        . simp [h_q]
          have ⟨ lb_prod, ub_prod ⟩ :
            -2147483648 * 2147483647 ≤ c * q ∧ c * q ≤ -1
          := by split_ands <;> nlinarith
          simp at lb_prod
          rw [Int.bmod_eq_of_le (by omega) (by omega)] at lb_b ub_b
          omega
        . exfalso
          simp at h_q
          have ⟨ lb_prod, ub_prod ⟩ :
            -2147483648 * 4294967295 ≤ c * q ∧ c * q ≤ -2147483648
          := by split_ands <;> nlinarith
          simp at lb_prod
          have ⟨ lb_exp, ub_exp ⟩ :
            -9223372034707292160 + (1 - 4294967296) ≤ c * q + (r - 4294967296) ∧ c * q + (r - 4294967296) ≤ -2147483648 + (4294967295 - 4294967296)
          := by omega
          simp at lb_exp ub_exp
          clear lb_prod ub_prod
          by_cases ub_exp' : -9223372036854775808 ≤ c * q + (r - 4294967296)
          . rw [Int.bmod_eq_of_le (by omega) (by omega)] at lb_b ub_b
            omega
          . simp [Int.bmod_def] at *
            omega
    -- `b` is negative, `c` is positive
    . simp_all [-BabyBear.to_the_right_FBB_255]
      clear h_bv_eq
      conv at lb_b =>
        rhs; arg 1; arg 1; arg 2
        simp [U64.toInt, U64.negative, U64.toNat]
        rw [if_pos (by omega)]
        simp
      repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at lb_b
      conv at ub_b =>
        lhs; arg 1; arg 1; arg 2
        simp [U64.toInt, U64.negative, U64.toNat]
        rw [if_pos (by omega)]
        simp
      repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at ub_b
      have h_eq :
        (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 + 1095216660480 + 280375465082880 + 71776119061217280 + 18374686479671623680 - 18446744073709551616 =
        (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 - 4294967296
        := by omega
      simp [h_eq] at lb_b ub_b; clear h_eq
      have ⟨ lb_qx, ub_qx ⟩ :
        -4294967295 ≤ (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 - 4294967296 ∧
        (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 - 4294967296 < 0
      := by omega
      have ⟨ lb_r, ub_r ⟩ :
        0 < (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 ∧
        (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 < 4294967296
      := by clear *- ub_r0 ub_r1 ub_r2 ub_r3 h_r_nz; omega
      clear h_cond_bext h_b_ext h_c_ext h_q_ext h_q_nz_n
      clear h_c_ext h_q_ext
      obtain ⟨ c, eq_c ⟩ : exists c, c = (c0 : ℤ) + ↑↑c1 * 256 + ↑↑c2 * 65536 + ↑↑c3 * 16777216 := by simp
      obtain ⟨ q, eq_q ⟩ : exists q, q = (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 - 4294967296 := by simp
      simp [U64.toInt, U64.negative, U64.toNat] at lb_b ub_b; clear h_b_ext
      rw [if_neg (by omega)] at lb_b ub_b h_c_nz ub_c lb_c
      rw [if_pos (by omega)] at lb_b ub_b
      clear h_cond_cext
      have h_eq :
        (r0 : ℤ) % 256 + ↑↑r1 % 256 * 256 + ↑↑r2 % 256 * 65536 + ↑↑r3 % 256 * 16777216 + 1095216660480 + 280375465082880 + 71776119061217280 + 18374686479671623680 - 18446744073709551616 =
        (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 - 4294967296
        := by omega
      simp [h_eq] at lb_b ub_b; clear h_eq
      obtain ⟨ r, eq_r ⟩ : exists r, r = (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 - 4294967296 := by simp
      suffices : -2147483648 ≤ q ∧ -2147483648 ≤ r
      . rw [eq_q, eq_r] at this; zify at this ⊢; clear *- this ub_q0 ub_q1 ub_q2 ub_q3 ub_r0 ub_r1 ub_r2 ub_r3; omega
      . replace lb_c : 0 < c := by clear *- eq_c h_c_nz; rw [eq_c]; omega
        clear h_r_nz
        rw [← eq_c] at ub_c lb_b ub_b h_c_nz; clear eq_c ub_c0 ub_c1 ub_c2 ub_c3 c0 c1 c2 c3
        rw [← eq_q] at lb_qx ub_qx lb_b ub_b; clear eq_q ub_q0 ub_q1 ub_q2 ub_q3 q0 q1 q2 q3
        have ⟨ lb_rx, ub_rx ⟩ : -4294967295 ≤ r ∧ r < 0 := by omega
        rw [← eq_r] at lb_b ub_b; clear lb_r ub_r eq_r ub_r0 ub_r1 ub_r2 ub_r3 r0 r1 r2 r3
        by_cases h_r : -2147483648 ≤ r
        . simp [h_r]
          clear h_c_nz lb_rx
          by_contra h_q; simp at h_q
          have ⟨ lb_prod, ub_prod ⟩ :
            -2147483647 * 4294967295 ≤ c * q ∧ c * q ≤ -2147483649
          := by split_ands <;> nlinarith
          simp at lb_prod
          have ⟨ lb_exp, ub_exp ⟩ :
            -9223372030412324865 - 2147483648 ≤ c * q + r ∧ c * q + r ≤ -2147483650
          := by omega
          simp at lb_exp
          clear ub_prod lb_prod
          by_cases ub_exp' : -9223372036854775808 ≤ c * q + r
          . rw [Int.bmod_eq_of_le (by omega) (by omega)] at lb_b ub_b
            omega
          . simp [Int.bmod_def] at *
            omega
        . exfalso
          simp at h_r
          clear h_c_nz ub_rx
          have ⟨ lb_prod, ub_prod ⟩ :
            -2147483647 * 4294967295 ≤ c * q ∧ c * q ≤ -1
          := by split_ands <;> nlinarith
          simp at lb_prod
          have ⟨ lb_exp, ub_exp ⟩ :
            -9223372030412324865 - 4294967295 ≤ c * q + r ∧ c * q + r ≤ -2147483650
          := by omega
          simp at lb_exp
          clear ub_prod lb_prod
          by_cases ub_exp' : -9223372036854775808 ≤ c * q + r
          . rw [Int.bmod_eq_of_le (by omega) (by omega)] at lb_b ub_b
            omega
          . simp [Int.bmod_def] at *
            omega
    -- `b` is positive, `c` is negative
    . simp_all [-BabyBear.to_the_right_FBB_255]
      clear h_bv_eq
      conv at lb_b =>
        rhs; arg 1; arg 1; arg 2
        simp [U64.toInt, U64.negative, U64.toNat]
        rw [if_pos (by omega)]
        simp
      repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at lb_b
      conv at ub_b =>
        lhs; arg 1; arg 1; arg 2
        simp [U64.toInt, U64.negative, U64.toNat]
        rw [if_pos (by omega)]
        simp
      repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at ub_b
      have h_eq :
        (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 + 1095216660480 + 280375465082880 + 71776119061217280 + 18374686479671623680 - 18446744073709551616 =
        (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 - 4294967296
        := by omega
      simp [h_eq] at lb_b ub_b; clear h_eq
      have ⟨ lb_cx, ub_cx ⟩ :
        -2147483648 ≤ (c0 : ℤ) + ↑↑c1 * 256 + ↑↑c2 * 65536 + ↑↑c3 * 16777216 - 4294967296 ∧
        (c0 : ℤ) + ↑↑c1 * 256 + ↑↑c2 * 65536 + ↑↑c3 * 16777216 - 4294967296 < 0
      := by omega
      clear lb_c ub_c
      have ⟨ lb_qx, ub_qx ⟩ :
        -4294967295 ≤ (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 - 4294967296 ∧
        (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 - 4294967296 < 0
      := by omega
      have ⟨ lb_r, ub_r ⟩ :
        0 < (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 ∧
        (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 < 4294967296
      := by clear *- ub_r0 ub_r1 ub_r2 ub_r3 h_r_nz; omega
      clear h_cond_bext h_b_ext h_c_ext h_q_ext h_q_nz_n
      clear h_c_ext h_q_ext
      obtain ⟨ c, eq_c ⟩ : exists c, c = (c0 : ℤ) + ↑↑c1 * 256 + ↑↑c2 * 65536 + ↑↑c3 * 16777216 - 4294967296 := by simp
      obtain ⟨ q, eq_q ⟩ : exists q, q = (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 - 4294967296 := by simp
      simp [U64.toInt, U64.negative, U64.toNat] at lb_b ub_b; clear h_b_ext
      rw [if_pos (by omega)] at lb_b ub_b h_c_nz
      rw [if_neg (by omega)] at lb_b ub_b
      clear h_cond_cext
      have h_eq :
        (r0 : ℤ) % 256 + ↑↑r1 % 256 * 256 + ↑↑r2 % 256 * 65536 + ↑↑r3 % 256 * 16777216 - 0 =
        (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216
        := by omega
      simp [h_eq] at lb_b ub_b; clear h_eq
      obtain ⟨ r, eq_r ⟩ : exists r, r = (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 := by simp
      suffices : -2147483648 ≤ q ∧ r < 2147483648
      . rw [eq_q, eq_r] at this; zify at this ⊢; clear *- this ub_q0 ub_q1 ub_q2 ub_q3 ub_r0 ub_r1 ub_r2 ub_r3; omega
      . clear h_r_nz
        rw [← eq_c] at lb_cx ub_cx lb_b ub_b h_c_nz; clear eq_c ub_c0 ub_c1 ub_c2 ub_c3 c0 c1 c2 c3
        rw [← eq_q] at lb_qx ub_qx lb_b ub_b; clear eq_q ub_q0 ub_q1 ub_q2 ub_q3 q0 q1 q2 q3
        have ⟨ lb_rx, ub_rx ⟩ : 0 < r ∧ r < 4294967296 := by omega
        rw [← eq_r] at lb_b ub_b; clear lb_r ub_r eq_r ub_r0 ub_r1 ub_r2 ub_r3 r0 r1 r2 r3
        by_cases h_r : r < 2147483648
        . simp [h_r]
          clear h_c_nz ub_rx
          by_contra h_q; simp at h_q
          have ⟨ lb_prod, ub_prod ⟩ :
            2147483648 < c * q ∧ c * q ≤ 2147483648 * 4294967295
          := by split_ands <;> nlinarith
          simp at ub_prod
          have ⟨ lb_exp, ub_exp ⟩ :
            2147483649 < c * q + r ∧ c * q + r < 2147483648 * 4294967295 + 2147483648
          := by omega
          simp at ub_exp
          clear ub_prod lb_prod
          by_cases ub_exp' : -9223372036854775808 ≤ c * q + r
          . rw [Int.bmod_eq_of_le (by omega) (by omega)] at lb_b ub_b
            omega
          . simp [Int.bmod_def] at *
            omega
        . exfalso
          simp at h_r
          clear h_c_nz lb_rx
          have ⟨ lb_prod, ub_prod ⟩ :
            1 ≤ c * q ∧ c * q ≤ 2147483648 * 4294967295
          := by split_ands <;> nlinarith
          simp at ub_prod
          have ⟨ lb_exp, ub_exp ⟩ :
            2147483649 ≤ c * q + r ∧ c * q + r ≤ 2147483648 * 4294967295 + 4294967295
          := by omega
          simp at ub_exp
          clear ub_prod lb_prod
          by_cases ub_exp' : c * q + r < 9223372036854775808
          . rw [Int.bmod_eq_of_le (by omega) (by omega)] at lb_b ub_b
            omega
          . simp [Int.bmod_def] at *
            omega
    -- `b` and `c` both positive
    . simp_all [-BabyBear.to_the_right_FBB_0]
      clear h_bv_eq
      simp [U64.toInt, U64.negative, U64.toNat] at lb_b ub_b
      repeat rw [if_neg (by omega)] at lb_b ub_b
      simp at lb_b ub_b
      repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at lb_b ub_b
      repeat clear h_b_ext h_c_ext h_q_ext
      have ⟨ lb_r, ub_r ⟩ :
        0 < (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 ∧
        (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 < 4294967296
      := by clear *- ub_r0 ub_r1 ub_r2 ub_r3 h_r_nz; omega
      clear h_cond_bext h_r_nz
      obtain ⟨ c, eq_c ⟩ : exists c, c = (c0 : ℤ) + ↑↑c1 * 256 + ↑↑c2 * 65536 + ↑↑c3 * 16777216 := by simp
      obtain ⟨ q, eq_q ⟩ : exists q, q = (q0 : ℤ) + ↑↑q1 * 256 + ↑↑q2 * 65536 + ↑↑q3 * 16777216 := by simp
      obtain ⟨ r, eq_r ⟩ : exists r, r = (r0 : ℤ) + ↑↑r1 * 256 + ↑↑r2 * 65536 + ↑↑r3 * 16777216 := by simp
      suffices : q < 2147483648 ∧ r < 2147483648
      . rw [eq_q, eq_r] at this; zify at this ⊢; clear *- this; omega
      . rw [if_neg (by omega)] at h_c_nz ub_c lb_c
        replace lb_c : 0 < c := by clear *- h_c_nz eq_c ub_c0 ub_c1 ub_c2 ub_c3; rw [eq_c]; omega
        have lb_q : 0 < q := by clear *- eq_q h_q_nz_n ub_q0 ub_q1 ub_q2 ub_q3; rw [eq_q]; omega
        have ub_q : q < 4294967296 := by clear *- eq_q ub_q0 ub_q1 ub_q2 ub_q3; rw [eq_q]; omega
        rw [← eq_c] at ub_c lb_b ub_b; clear h_cond_cext h_c_nz eq_c ub_c0 ub_c1 ub_c2 ub_c3 c0 c1 c2 c3
        rw [← eq_q] at lb_b ub_b; clear h_q_nz_n eq_q ub_q0 ub_q1 ub_q2 ub_q3 q0 q1 q2 q3
        rw [← eq_r] at lb_b ub_b lb_r ub_r; clear eq_r ub_r0 ub_r1 ub_r2 ub_r3 r0 r1 r2 r3
        by_cases h_r : r < 2147483648
        . simp [h_r]
          by_contra h_q; simp at h_q
          have ⟨ lb_prod, ub_prod ⟩ :
            2147483648 ≤ c * q ∧ c * q ≤ 2147483647 * 4294967295
          := by split_ands <;> nlinarith
          simp at ub_prod
          have ⟨ lb_exp, ub_exp ⟩ :
            2147483649 ≤ c * q + r ∧ c * q + r < 2147483647 * 4294967295 + 2147483648
          := by omega
          simp at ub_exp
          clear ub_prod lb_prod
          by_cases ub_exp' : c * q + r < 9223372036854775808
          . rw [Int.bmod_eq_of_le (by omega) (by omega)] at lb_b ub_b
            omega
          . simp [Int.bmod_def] at *
            omega
        . exfalso
          simp at h_r
          clear lb_r
          have ⟨ lb_prod, ub_prod ⟩ :
            1 ≤ c * q ∧ c * q ≤ 2147483647 * 4294967295
          := by split_ands <;> nlinarith
          simp at ub_prod
          have ⟨ lb_exp, ub_exp ⟩ :
            2147483649 ≤ c * q + r ∧ c * q + r ≤ 2147483647 * 4294967295 + 4294967295
          := by omega
          simp at ub_exp
          clear ub_prod lb_prod
          by_cases ub_exp' : c * q + r < 9223372036854775808
          . rw [Int.bmod_eq_of_le (by omega) (by omega)] at lb_b ub_b
            omega
          . simp [Int.bmod_def] at *
            omega

attribute [-simp]
  BabyBear.to_the_right_FBB_0
  BabyBear.to_the_right_FBB_1
  BabyBear.to_the_right_FBB_255
  to_the_right_nat_0
  to_the_right_nat_1
  to_the_right_nat_255
  to_the_right_nat_256
  not_and

set_option maxRecDepth 1_000_000 in
include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the DIV/REM opcode, Part 1 --/
theorem spec_DIVREM_czero
  (h_divrem :
    (air.core.ctx row 0).instruction.opcode = 596 ∨
    (air.core.ctx row 0).instruction.opcode = 598)
  (h_c_zero : air.core.zero_divisor row 0 = 1)
:
  (U32.toBV #v[(air.core.q_0 row 0).val,
               (air.core.q_1 row 0).val,
               (air.core.q_2 row 0).val,
               (air.core.q_3 row 0).val],
   U32.toBV #v[(air.core.r_0 row 0).val,
               (air.core.r_1 row 0).val,
               (air.core.r_2 row 0).val,
               (air.core.r_3 row 0).val])
    =
  (execute_DIV_REM_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .DRS)
:= by
  obtain ⟨ sop0, sop1, sop2, sop3 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2, op3 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  have ⟨ op_sum, op_divu, op_remu ⟩ :
    (air.core.opcode_div_flag row 0 + air.core.opcode_rem_flag row 0 = 1) ∧
    air.core.opcode_divu_flag row 0 = 0 ∧
    air.core.opcode_remu_flag row 0 = 0
    := by grind

  clear h_divrem sop0 sop1 sop2 sop3 op0 op1 op2 op3

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_divrem_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ub_q0, ub_cq0, ub_q1, ub_cq1, ub_q2, ub_cq2, ub_q3, ub_cq3,
           ub_r0, ub_cr0, ub_r1, ub_cr1, ub_r2, ub_cr2, ub_r3, ub_cr3 ⟩ := pa_rtc
  obtain ⟨ h_signed_msb, h_diff ⟩ := pa_bit
  clear pa_range pa_read

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
           b_zd, h_zd_c0, h_zd_q0, h_zd_c1, h_zd_q1, h_zd_c2, h_zd_q2, h_zd_c3, h_zd_q3,
           b_vnzd, h_vnzd,
           b_rz, b_rz_r0, b_rz_r1, b_rz_r2, b_rz_r3,
           b_vnsc, h_vnsc,
           b_bsgn, b_csgn, h_bsgn, h_csgn, h_xor_eq,
           b_qsgn, h_xor_qsgn_eq, h_xor_qsgn_z,
           h_r'_0, b_lt_0, h_r'inv_0, h_lt_0,
           h_r'_1, b_lt_1, h_r'inv_1, h_lt_1,
           h_r'_2, b_lt_2, h_r'inv_2, h_lt_2,
           h_r'_3, b_lt_3, h_r'inv_3, h_lt_3,
           b_ltm_3, h_prod_3, h_diff_3,
           b_ltm_2, h_prod_2, h_diff_2,
           b_ltm_1, h_prod_1, h_diff_1,
           b_ltm_0, h_prod_0, h_diff_0,
           h_sum_sc_ltm,
           rest ⟩ := constraints
  clear constrain_interactions rest

  have eq_sgn : air.core.signed row 0 = 1
    := by simpa [← DivRemCoreAir_4_8.signed_def]
  simp [eq_sgn] at *; clear h_bsgn h_csgn eq_sgn

  clear b_vnzd
  simp [← DivRemCoreAir_4_8.valid_and_not_zero_divisor_def] at h_vnzd
  simp [row_valid] at h_vnzd

  have ub_be : (air.core.b_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.b_ext_def]; clear *- b_bsgn; grind

  have ub_ce : (air.core.c_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.c_ext_def]; clear *- b_csgn; grind

  have ub_qe : (air.core.q_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.q_ext_def]; clear *- b_qsgn; grind

  have eq_zero_divisor :
    air.core.zero_divisor row 0 = 1 ↔
      air.core.c_0 row 0 = 0 ∧ air.core.c_1 row 0 = 0 ∧ air.core.c_2 row 0 = 0 ∧ air.core.c_3 row 0 = 0
  := by
    constructor
    . intro h_div; simp_all
    . intro ⟨ z_c0, z_c1, z_c2, z_c3 ⟩
      clear *- b_zd h_vnzd z_c0 z_c1 z_c2 z_c3
      simp [← DivRemCoreAir_4_8.c_sum_def] at h_vnzd
      grind

  simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
  simp [BabyBear.toInt_0_inv ub_c0 ub_c1 ub_c2 ub_c3,
        BabyBear.toInt_neg_2_pow_32_inv ub_b0 ub_b1 ub_b2 ub_b3,
        BabyBear.toInt_neg_1_inv ub_c0 ub_c1 ub_c2 ub_c3]

  simp [← DivRemCoreAir_4_8.carry_0,
        ← DivRemCoreAir_4_8.carry_1,
        ← DivRemCoreAir_4_8.carry_2,
        ← DivRemCoreAir_4_8.carry_3] at *
  simp_all

  split_ands
  . simp [← BitVec.toInt_inj]
    simp [U32.toInt, U32.negative, U32.toNat]
  . repeat rw [mul_comm (b := 2005401601)] at *
    have : air.core.r_0 row 0 = air.core.b_0 row 0
    := by
      have ⟨ h_eq, _ ⟩ :=
        @BabyBear.inv256_prod_diff_div_mod (air.core.b_0 row 0) (air.core.r_0 row 0) ub_b0 (by omega)
      clear *- ub_r0 h_eq
      simp_all [Fin.ext_iff]; omega
    simp_all
    have : air.core.r_1 row 0 = air.core.b_1 row 0
    := by
      have ⟨ h_eq, _ ⟩ :=
        @BabyBear.inv256_prod_diff_div_mod (air.core.b_1 row 0) (air.core.r_1 row 0) ub_b1 (by omega)
      clear *- ub_r1 h_eq
      simp_all [Fin.ext_iff]; omega
    simp_all
    have : air.core.r_2 row 0 = air.core.b_2 row 0
    := by
      have ⟨ h_eq, _ ⟩ :=
        @BabyBear.inv256_prod_diff_div_mod (air.core.b_2 row 0) (air.core.r_2 row 0) ub_b2 (by omega)
      clear *- ub_r2 h_eq
      simp_all [Fin.ext_iff]; omega
    simp_all
    have : air.core.r_3 row 0 = air.core.b_3 row 0
    := by
      have ⟨ h_eq, _ ⟩ :=
        @BabyBear.inv256_prod_diff_div_mod (air.core.b_3 row 0) (air.core.r_3 row 0) ub_b3 (by omega)
      clear *- ub_r3 h_eq
      simp_all [Fin.ext_iff]; omega
    simp_all [← BitVec.toInt_inj]
    conv =>
      rhs; arg 1; arg 2
      simp [U32.toInt, U32.negative, U32.toNat]
    simp_all [U32.toInt_bmod_eq]

set_option maxRecDepth 1_000_000 in
include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the DIV/REM opcode, Part 2 --/
theorem spec_DIVREM_nczero_sc
  (h_divrem :
    (air.core.ctx row 0).instruction.opcode = 596 ∨
    (air.core.ctx row 0).instruction.opcode = 598)
  (h_c_zero : air.core.zero_divisor row 0 = 0)
  (h_scase : U32.toInt
              #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0),
                 BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0)] = -2147483648 ∧
             U32.toInt
              #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0),
                 BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] = -1)
:
  (U32.toBV #v[(air.core.q_0 row 0).val,
               (air.core.q_1 row 0).val,
               (air.core.q_2 row 0).val,
               (air.core.q_3 row 0).val],
   U32.toBV #v[(air.core.r_0 row 0).val,
               (air.core.r_1 row 0).val,
               (air.core.r_2 row 0).val,
               (air.core.r_3 row 0).val])
    =
  (execute_DIV_REM_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .DRS)
:= by
  obtain ⟨ sop0, sop1, sop2, sop3 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2, op3 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  have ⟨ op_sum, op_divu, op_remu ⟩ :
    (air.core.opcode_div_flag row 0 + air.core.opcode_rem_flag row 0 = 1) ∧
    air.core.opcode_divu_flag row 0 = 0 ∧
    air.core.opcode_remu_flag row 0 = 0
    := by grind

  clear h_divrem sop0 sop1 sop2 sop3 op0 op1 op2 op3

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_divrem_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ub_q0, ub_cq0, ub_q1, ub_cq1, ub_q2, ub_cq2, ub_q3, ub_cq3,
           ub_r0, ub_cr0, ub_r1, ub_cr1, ub_r2, ub_cr2, ub_r3, ub_cr3 ⟩ := pa_rtc
  obtain ⟨ h_signed_msb, h_diff ⟩ := pa_bit
  clear pa_range pa_read

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
           b_zd, h_zd_c0, h_zd_q0, h_zd_c1, h_zd_q1, h_zd_c2, h_zd_q2, h_zd_c3, h_zd_q3,
           b_vnzd, h_vnzd,
           b_rz, b_rz_r0, b_rz_r1, b_rz_r2, b_rz_r3,
           b_vnsc, h_vnsc,
           b_bsgn, b_csgn, h_bsgn, h_csgn, h_xor_eq,
           b_qsgn, h_xor_qsgn_eq, h_xor_qsgn_z,
           h_r'_0, b_lt_0, h_r'inv_0, h_lt_0,
           h_r'_1, b_lt_1, h_r'inv_1, h_lt_1,
           h_r'_2, b_lt_2, h_r'inv_2, h_lt_2,
           h_r'_3, b_lt_3, h_r'inv_3, h_lt_3,
           b_ltm_3, h_prod_3, h_diff_3,
           b_ltm_2, h_prod_2, h_diff_2,
           b_ltm_1, h_prod_1, h_diff_1,
           b_ltm_0, h_prod_0, h_diff_0,
           h_sum_sc_ltm,
           rest ⟩ := constraints
  clear constrain_interactions rest

  have eq_sgn : air.core.signed row 0 = 1
    := by simpa [← DivRemCoreAir_4_8.signed_def]
  simp [eq_sgn] at *; clear h_bsgn h_csgn eq_sgn

  clear b_vnzd
  simp [← DivRemCoreAir_4_8.valid_and_not_zero_divisor_def] at h_vnzd
  simp [row_valid] at h_vnzd

  have ub_be : (air.core.b_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.b_ext_def]; clear *- b_bsgn; grind

  have ub_ce : (air.core.c_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.c_ext_def]; clear *- b_csgn; grind

  have ub_qe : (air.core.q_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.q_ext_def]; clear *- b_qsgn; grind

  have eq_zero_divisor :
    air.core.zero_divisor row 0 = 1 ↔
      air.core.c_0 row 0 = 0 ∧ air.core.c_1 row 0 = 0 ∧ air.core.c_2 row 0 = 0 ∧ air.core.c_3 row 0 = 0
  := by
    constructor
    . intro h_div; simp_all
    . intro ⟨ z_c0, z_c1, z_c2, z_c3 ⟩
      clear *- b_zd h_vnzd z_c0 z_c1 z_c2 z_c3
      simp [← DivRemCoreAir_4_8.c_sum_def] at h_vnzd
      grind

  have b_sign_is_bsgn
  :
    U32.ext #v[(air.core.b_0 row 0).val,
               (air.core.b_1 row 0).val,
               (air.core.b_2 row 0).val,
               (air.core.b_3 row 0).val] true =
    air.core.b_ext row 0
  := by
    rw [← DivRemCoreAir_4_8.b_ext_def]
    clear *- b_bsgn ub_b0 ub_b1 ub_b2 ub_b3 h_signed_msb
    simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
    rw [Nat.mod_eq_of_lt (by omega)]
    grind

  have c_sign_is_csgn
  :
    U32.ext #v[(air.core.c_0 row 0).val,
               (air.core.c_1 row 0).val,
               (air.core.c_2 row 0).val,
               (air.core.c_3 row 0).val] true =
    air.core.c_ext row 0
  := by
    rw [← DivRemCoreAir_4_8.c_ext_def]
    clear *- b_csgn ub_c0 ub_c1 ub_c2 ub_c3 h_signed_msb
    simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
    rw [Nat.mod_eq_of_lt (by omega)]
    grind

  simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
  simp [BabyBear.toInt_0_inv ub_c0 ub_c1 ub_c2 ub_c3,
        BabyBear.toInt_neg_2_pow_32_inv ub_b0 ub_b1 ub_b2 ub_b3,
        BabyBear.toInt_neg_1_inv ub_c0 ub_c1 ub_c2 ub_c3]

  simp [← DivRemCoreAir_4_8.carry_0,
        ← DivRemCoreAir_4_8.carry_1,
        ← DivRemCoreAir_4_8.carry_2,
        ← DivRemCoreAir_4_8.carry_3,
        ← DivRemCoreAir_4_8.carry_ext_0_def,
        ← DivRemCoreAir_4_8.carry_ext_1_def,
        ← DivRemCoreAir_4_8.carry_ext_2_def,
        ← DivRemCoreAir_4_8.carry_ext_3_def
        ] at *

  simp_all

  rw [BabyBear.toInt_neg_1_inv ub_c0 ub_c1 ub_c2 ub_c3] at h_scase
  rw [BabyBear.toInt_neg_2_pow_32_inv ub_b0 ub_b1 ub_b2 ub_b3] at h_scase
  simp_all

  simp [← BitVec.toInt_inj]
  simp [← DivRemCoreAir_4_8.valid_and_not_special_case_def,
        ← DivRemCoreAir_4_8.special_case_def] at *

  have eq_bext : air.core.b_ext row 0 = 255
  := by
    clear *- b_sign_is_bsgn
    simp [U32.ext, U32.negative, U32.toNat] at b_sign_is_bsgn
    omega

  have eq_bsgn : air.core.b_sign row 0 = 1
  := by
    clear *- eq_bext
    simp [← DivRemCoreAir_4_8.b_ext_def] at eq_bext
    assumption

  have eq_cext : air.core.c_ext row 0 = 255
  := by
    clear *- c_sign_is_csgn
    simp [U32.ext, U32.negative, U32.toNat] at c_sign_is_csgn
    omega

  have eq_csgn : air.core.c_sign row 0 = 1
  := by
    clear *- eq_cext
    simp [← DivRemCoreAir_4_8.c_ext_def] at eq_cext
    assumption

  symm at h_xor_eq
  clear b_sign_is_bsgn c_sign_is_csgn
  simp_all

  have eq_qext : air.core.q_ext row 0 = 0
  := by
    clear *- h_xor_qsgn_z
    simp [← DivRemCoreAir_4_8.q_ext_def]
    assumption

  rw [BabyBear.toInt_neg_2_pow_32_inv ub_q0 ub_q1 ub_q2 ub_q3]
  rw [BabyBear.toInt_0_inv ub_r0 ub_r1 ub_r2 ub_r3]
  repeat rw [mul_comm (b := 2005401601)] at *
  simp_all

  have r_zero :
    air.core.r_prime_0 row 0 = 0 ∧
    air.core.r_prime_1 row 0 = 0 ∧
    air.core.r_prime_2 row 0 = 0 ∧
    air.core.r_prime_3 row 0 = 0
  := by
    clear ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cr0 ub_cr1 ub_cr2 ub_cr3
    rcases b_rz with h_rz | h_rz <;> simp_all
    . rcases b_ltm_0 with lm0 | lm0
      . rcases b_ltm_1 with lm1 | lm1
        . rcases b_ltm_2 with lm2 | lm2
          . simp_all; clear *- ub_r3 h_diff; omega
          . simp_all; clear *- ub_r2 h_diff; omega
        . simp_all; clear *- ub_r1 h_diff; omega
      . simp_all; clear *- ub_r0 h_diff; omega
  simp_all

  have : air.core.q_0 row 0 = 0
  := by
    have ⟨ h_eq, _ ⟩ :=
      @BabyBear.inv256_prod_diff_div_mod 0 (255 * air.core.q_0 row 0) (by simp) (by clear *- ub_cq0; simp; omega)
    symm at h_eq
    rw [Fin.ext_iff, Fin.mod_val, Fin.val_mul] at h_eq
    rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at h_eq
    simp at h_eq
    omega
  simp [this] at *
  have : air.core.q_1 row 0 = 0
  := by
    have ⟨ h_eq, _ ⟩ :=
      @BabyBear.inv256_prod_diff_div_mod 0 (255 * air.core.q_1 row 0) (by simp) (by clear *- ub_cq1; simp; omega)
    symm at h_eq
    rw [Fin.ext_iff, Fin.mod_val, Fin.val_mul] at h_eq
    rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at h_eq
    simp at h_eq
    omega
  simp [this] at *
  have : air.core.q_2 row 0 = 0
  := by
    have ⟨ h_eq, _ ⟩ :=
      @BabyBear.inv256_prod_diff_div_mod 0 (255 * air.core.q_2 row 0) (by simp) (by clear *- ub_cq2; simp; omega)
    symm at h_eq
    rw [Fin.ext_iff, Fin.mod_val, Fin.val_mul] at h_eq
    rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at h_eq
    simp at h_eq
    omega
  simp [this] at *
  have ⟨ h_eq, _ ⟩ :=
    @BabyBear.inv256_prod_diff_div_mod 128 (255 * air.core.q_3 row 0) (by simp) (by clear *- ub_cq3; omega)
  rw [Fin.ext_iff, Fin.mod_val, Fin.val_mul] at h_eq
  rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at h_eq
  simp at h_eq
  omega

set_option maxRecDepth 1_000_000 in
include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the DIV/REM opcode, Part 3 --/
theorem spec_DIVREM_nczero_nsc_rzero
  (h_divrem :
    (air.core.ctx row 0).instruction.opcode = 596 ∨
    (air.core.ctx row 0).instruction.opcode = 598)
  (h_c_zero : air.core.zero_divisor row 0 = 0)
  (h_scase : ¬ (U32.toInt
                  #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0),
                    BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0)] = -2147483648 ∧
                U32.toInt
                  #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0),
                    BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] = -1))
  (h_r_zero : air.core.r_zero row 0 = 1)
:
  (U32.toBV #v[(air.core.q_0 row 0).val,
               (air.core.q_1 row 0).val,
               (air.core.q_2 row 0).val,
               (air.core.q_3 row 0).val],
   U32.toBV #v[(air.core.r_0 row 0).val,
               (air.core.r_1 row 0).val,
               (air.core.r_2 row 0).val,
               (air.core.r_3 row 0).val])
    =
  (execute_DIV_REM_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .DRS)
:= by
  obtain ⟨ sop0, sop1, sop2, sop3 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2, op3 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  have ⟨ op_sum, op_divu, op_remu ⟩ :
    (air.core.opcode_div_flag row 0 + air.core.opcode_rem_flag row 0 = 1) ∧
    air.core.opcode_divu_flag row 0 = 0 ∧
    air.core.opcode_remu_flag row 0 = 0
    := by grind

  clear h_divrem sop0 sop1 sop2 sop3 op0 op1 op2 op3

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_divrem_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ub_q0, ub_cq0, ub_q1, ub_cq1, ub_q2, ub_cq2, ub_q3, ub_cq3,
           ub_r0, ub_cr0, ub_r1, ub_cr1, ub_r2, ub_cr2, ub_r3, ub_cr3 ⟩ := pa_rtc
  obtain ⟨ h_signed_msb, h_diff ⟩ := pa_bit
  clear pa_range pa_read

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
           b_zd, h_zd_c0, h_zd_q0, h_zd_c1, h_zd_q1, h_zd_c2, h_zd_q2, h_zd_c3, h_zd_q3,
           b_vnzd, h_vnzd,
           b_rz, b_rz_r0, b_rz_r1, b_rz_r2, b_rz_r3,
           b_vnsc, h_vnsc,
           b_bsgn, b_csgn, h_bsgn, h_csgn, h_xor_eq,
           b_qsgn, h_xor_qsgn_eq, h_xor_qsgn_z,
           h_r'_0, b_lt_0, h_r'inv_0, h_lt_0,
           h_r'_1, b_lt_1, h_r'inv_1, h_lt_1,
           h_r'_2, b_lt_2, h_r'inv_2, h_lt_2,
           h_r'_3, b_lt_3, h_r'inv_3, h_lt_3,
           b_ltm_3, h_prod_3, h_diff_3,
           b_ltm_2, h_prod_2, h_diff_2,
           b_ltm_1, h_prod_1, h_diff_1,
           b_ltm_0, h_prod_0, h_diff_0,
           h_sum_sc_ltm,
           rest ⟩ := constraints
  clear constrain_interactions rest

  have eq_sgn : air.core.signed row 0 = 1
    := by simpa [← DivRemCoreAir_4_8.signed_def]
  simp [eq_sgn] at *; clear h_bsgn h_csgn eq_sgn

  clear b_vnzd
  simp [← DivRemCoreAir_4_8.valid_and_not_zero_divisor_def] at h_vnzd
  simp [row_valid] at h_vnzd

  have ub_be : (air.core.b_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.b_ext_def]; clear *- b_bsgn; grind

  have ub_ce : (air.core.c_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.c_ext_def]; clear *- b_csgn; grind

  have ub_qe : (air.core.q_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.q_ext_def]; clear *- b_qsgn; grind

  have eq_zero_divisor :
    air.core.zero_divisor row 0 = 1 ↔
      air.core.c_0 row 0 = 0 ∧ air.core.c_1 row 0 = 0 ∧ air.core.c_2 row 0 = 0 ∧ air.core.c_3 row 0 = 0
  := by
    constructor
    . intro h_div; simp_all
    . intro ⟨ z_c0, z_c1, z_c2, z_c3 ⟩
      clear *- b_zd h_vnzd z_c0 z_c1 z_c2 z_c3
      simp [← DivRemCoreAir_4_8.c_sum_def] at h_vnzd
      grind

  suffices h_toInt :
    U32.toInt #v[(air.core.q_0 row 0).val,
                 (air.core.q_1 row 0).val,
                 (air.core.q_2 row 0).val,
                 (air.core.q_3 row 0).val]
      =
    (U32.toInt #v[(air.core.b_0 row 0).val,
                  (air.core.b_1 row 0).val,
                  (air.core.b_2 row 0).val,
                  (air.core.b_3 row 0).val]).tdiv
    (U32.toInt #v[(air.core.c_0 row 0).val,
                  (air.core.c_1 row 0).val,
                  (air.core.c_2 row 0).val,
                  (air.core.c_3 row 0).val]) ∧
    U32.toInt #v[(air.core.r_0 row 0).val,
                 (air.core.r_1 row 0).val,
                 (air.core.r_2 row 0).val,
                 (air.core.r_3 row 0).val]
      =
    (U32.toInt #v[(air.core.b_0 row 0).val,
                  (air.core.b_1 row 0).val,
                  (air.core.b_2 row 0).val,
                  (air.core.b_3 row 0).val]).tmod
    (U32.toInt #v[(air.core.c_0 row 0).val,
                  (air.core.c_1 row 0).val,
                  (air.core.c_2 row 0).val,
                  (air.core.c_3 row 0).val])
  . simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
    simp [BabyBear.toInt_0_inv ub_c0 ub_c1 ub_c2 ub_c3]
    simp_all
    clear *- ub_b0 ub_b1 ub_b2 ub_b3
             ub_c0 ub_c1 ub_c2 ub_c3
             ub_q0 ub_q1 ub_q2 ub_q3
             h_toInt h_scase eq_zero_divisor
    simp [← BitVec.toInt_inj]
    have range_b := U32.toInt_range #v[(air.core.b_0 row 0).val, (air.core.b_1 row 0).val, (air.core.b_2 row 0).val, (air.core.b_3 row 0).val]
    have range_c := U32.toInt_range #v[(air.core.c_0 row 0).val, (air.core.c_1 row 0).val, (air.core.c_2 row 0).val, (air.core.c_3 row 0).val]
    simp_all [BitVec.ofNat]
    obtain ⟨ lm, um ⟩ := Int.tmod_range_32 range_b range_c
    obtain ⟨ ld, ud ⟩ := Int.tdiv_range_32 (by simp [U32.toInt, U32.negative, U32.toNat]; clear *- ub_c0 ub_c1 ub_c2 ub_c3 eq_zero_divisor; split_ifs <;> omega) h_scase range_b range_c
    rw [Int.bmod_eq_of_le (by simp; omega) (by simp; omega)]
    rw [Int.bmod_eq_of_le (by simp; omega) (by simp; omega)]
    simp

  . have b_sign_is_bsgn
    :
      U32.ext #v[(air.core.b_0 row 0).val,
                (air.core.b_1 row 0).val,
                (air.core.b_2 row 0).val,
                (air.core.b_3 row 0).val] true =
      air.core.b_ext row 0
    := by
      rw [← DivRemCoreAir_4_8.b_ext_def]
      clear *- b_bsgn ub_b0 ub_b1 ub_b2 ub_b3 h_signed_msb
      simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
      rw [Nat.mod_eq_of_lt (by omega)]
      grind

    have c_sign_is_csgn
    :
      U32.ext #v[(air.core.c_0 row 0).val,
                (air.core.c_1 row 0).val,
                (air.core.c_2 row 0).val,
                (air.core.c_3 row 0).val] true =
      air.core.c_ext row 0
    := by
      rw [← DivRemCoreAir_4_8.c_ext_def]
      clear *- b_csgn ub_c0 ub_c1 ub_c2 ub_c3 h_signed_msb
      simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
      rw [Nat.mod_eq_of_lt (by omega)]
      grind

    simp [← DivRemCoreAir_4_8.carry_0,
          ← DivRemCoreAir_4_8.carry_1,
          ← DivRemCoreAir_4_8.carry_2,
          ← DivRemCoreAir_4_8.carry_3,
          ← DivRemCoreAir_4_8.carry_ext_0_def,
          ← DivRemCoreAir_4_8.carry_ext_1_def,
          ← DivRemCoreAir_4_8.carry_ext_2_def,
          ← DivRemCoreAir_4_8.carry_ext_3_def
          ] at *

    repeat rw [mul_comm (b := 2005401601)] at *

    simp_all

    have h_bv_eq :=
      @divrem_split
        (air.core.b_0 row 0) (air.core.b_1 row 0) (air.core.b_2 row 0) (air.core.b_3 row 0) (air.core.b_ext row 0) (air.core.b_ext row 0) (air.core.b_ext row 0) (air.core.b_ext row 0)
        (air.core.c_0 row 0) (air.core.c_1 row 0) (air.core.c_2 row 0) (air.core.c_3 row 0)
        (air.core.q_0 row 0) (air.core.q_1 row 0) (air.core.q_2 row 0) (air.core.q_3 row 0)
        0 0 0 0
        (air.core.c_ext row 0) (air.core.q_ext row 0) 0
        ub_b0 ub_b1 ub_b2 ub_b3 ub_be ub_be ub_be ub_be
        ub_c0 ub_c1 ub_c2 ub_c3 ub_q0 ub_q1 ub_q2 ub_q3
        (by simp) (by simp) (by simp) (by simp)
        ub_ce ub_qe (by simp)
        (by clear *- ub_cq0; simp; assumption)
        (by clear *- ub_cq1; simp; assumption)
        (by clear *- ub_cq2; simp; assumption)
        (by clear *- ub_cq3; simp; assumption)
        (by clear *- ub_cr0; simp; grind)
        (by clear *- ub_cr1; simp; grind)
        (by clear *- ub_cr2; simp; grind)
        (by clear *- ub_cr3; simp; grind)

    clear ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cr0 ub_cr1 ub_cr2 ub_cr3
    simp [← BitVec.toInt_inj] at h_bv_eq
    have h_b_ext :
      U64.toInt
        #v[BitVec.ofNat 8 (air.core.b_0 row 0), BitVec.ofNat 8 (air.core.b_1 row 0), BitVec.ofNat 8  (air.core.b_2 row 0), BitVec.ofNat 8 (air.core.b_3 row 0),
           BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0)] =
      U32.toInt
        #v[BitVec.ofNat 8 (air.core.b_0 row 0), BitVec.ofNat 8 (air.core.b_1 row 0), BitVec.ofNat 8 (air.core.b_2 row 0), BitVec.ofNat 8 (air.core.b_3 row 0)]
    := by
      rw [← U32.extend_toInt, U32.extend]
      simp [b_sign_is_bsgn]
    have h_c_ext :
      U64.toInt
        #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8  (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0),
           BitVec.ofNat 8 (air.core.c_ext row 0), BitVec.ofNat 8 (air.core.c_ext row 0), BitVec.ofNat 8 (air.core.c_ext row 0), BitVec.ofNat 8 (air.core.c_ext row 0)] =
      U32.toInt
        #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)]
    := by
      rw [← U32.extend_toInt, U32.extend]
      simp [c_sign_is_csgn]
    rw [h_b_ext, h_c_ext] at h_bv_eq
    conv at h_bv_eq =>
      rhs; arg 1; arg 2
      simp [U64.toInt, U64.negative, U64.toNat]
    simp at h_bv_eq

    have q_sign_is_qsgn
    :
      U32.ext #v[(air.core.q_0 row 0).val,
                 (air.core.q_1 row 0).val,
                 (air.core.q_2 row 0).val,
                 (air.core.q_3 row 0).val] true =
      air.core.q_ext row 0
    := by
      obtain ⟨ msb_b, msb_c ⟩ := h_signed_msb
      have ⟨ hlb, hub ⟩ := U32.toInt_range #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0), BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0)]
      rw [h_bv_eq] at hlb hub
      clear h_r'_0 b_lt_0 h_r'inv_0 h_lt_0
            h_r'_1 b_lt_1 h_r'inv_1 h_lt_1
            h_r'_2 b_lt_2 h_r'inv_2 h_lt_2
            h_r'_3 b_lt_3 h_r'inv_3 h_lt_3
            b_ltm_3 h_prod_3 h_diff_3 b_ltm_2 h_prod_2 h_diff_2
            b_ltm_1 h_prod_1 h_diff_1 b_ltm_0 h_diff_0
            b_rz_r0 b_rz_r1 b_rz_r2 b_rz_r3
            h_sum_sc_ltm h_vnzd
      clear b_rz_r0 b_rz_r1 b_rz_r2 b_rz_r3
      have ⟨ hlc, huc ⟩ := U32.toInt_range #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)]
      have hnzc : ¬(U32.toInt #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] = 0)
      := by
        simp [U32.toInt, U32.negative, U32.toNat]
        clear *- ub_c0 ub_c1 ub_c2 ub_c3 eq_zero_divisor
        split_ifs <;> omega
      obtain ⟨ c, eq_c ⟩ : exists c, U32.toInt #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] = c := by simp
      rw [eq_c] at h_scase h_bv_eq hlb hub hnzc hlc huc
      have h_c_sign : air.core.c_sign row 0 = if 0 ≤ c then 0 else 1
      := by
        rw [← eq_c]
        simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide]
        split_ifs with hif1 hif2 hif2
        . simp [U32.toNat] at hif2; omega
        . clear *- ub_c3 msb_c hif1 b_csgn
          rw [Nat.mod_eq_of_lt (by omega)] at hif1
          grind
        . clear *- ub_c3 msb_c hif1 b_csgn
          rw [Nat.mod_eq_of_lt (by omega)] at hif1
          grind
        . simp [U32.toNat] at hif2; omega
      clear msb_c h_c_ext eq_zero_divisor c_sign_is_csgn eq_c ub_c0 ub_c1 ub_c2 ub_c3
      obtain ⟨ b, eq_b ⟩ : exists c, U32.toInt #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0), BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0)] = c := by simp
      rw [eq_b] at h_scase h_bv_eq
      have h_b_sign : air.core.b_sign row 0 = if 0 ≤ b then 0 else 1
      := by
        rw [← eq_b]
        simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide]
        split_ifs with hif1 hif2 hif2
        . simp [U32.toNat] at hif2; omega
        . clear *- ub_b3 msb_b hif1 b_bsgn
          rw [Nat.mod_eq_of_lt (by omega)] at hif1
          grind
        . clear *- ub_b3 msb_b hif1 b_bsgn
          rw [Nat.mod_eq_of_lt (by omega)] at hif1
          grind
        . simp [U32.toNat] at hif2; omega
      clear msb_b h_b_ext b_sign_is_bsgn eq_b ub_b0 ub_b1 ub_b2 ub_b3
      simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
      have b_qext : air.core.q_ext row 0 = 0 ∨ air.core.q_ext row 0 = 255
      := by
        clear *- b_qsgn
        rw [← DivRemCoreAir_4_8.q_ext_def]
        grind
      by_cases h_nzq : air.core.nonzero_q row 0 = 0
      . obtain ⟨ zq0, zq1, zq2, zq3 ⟩ : air.core.q_0 row 0 = 0 ∧ air.core.q_1 row 0 = 0 ∧ air.core.q_2 row 0 = 0 ∧ air.core.q_3 row 0 = 0
        := by
          clear *- ub_q0 ub_q1 ub_q2 ub_q3 h_nzq
          rw [← DivRemCoreAir_4_8.nonzero_q_def] at h_nzq
          omega
        simp [zq0, zq1, zq2, zq3] at hub hlb h_bv_eq ⊢
        rcases b_qext with h_qext | h_qext
        . grind
        . exfalso
          simp [h_qext] at hub hlb h_bv_eq
          simp [U64.toInt, U64.negative, U64.toNat] at hub hlb h_bv_eq
          clear *- huc hlc hub hlb h_scase h_bv_eq h_xor_qsgn_z h_xor_eq h_qext b_qsgn h_b_sign h_c_sign
          rw [← DivRemCoreAir_4_8.q_ext_def] at h_qext
          rcases b_qsgn with h_qsgn | h_qsgn
          . omega
          . simp [h_qsgn] at *; clear h_qsgn
            rw [← h_xor_qsgn_z] at h_xor_eq; clear h_xor_qsgn_z
            by_cases h_c : c = -2147483648
            . simp_all
            . simp [Int.bmod_def] at hub hlb h_bv_eq
              by_cases h_bz : 0 ≤ b
              . by_cases h_cz : 0 ≤ c
                . simp [h_bz] at h_b_sign; simp [h_cz] at h_c_sign
                  simp [h_b_sign, h_c_sign] at h_xor_eq
                . simp [h_bz] at h_b_sign; simp [h_cz] at h_c_sign
                  simp [h_b_sign, h_c_sign] at h_xor_eq
                  omega
              . by_cases h_cz : 0 ≤ c
                . simp [h_bz] at h_b_sign; simp [h_cz] at h_c_sign
                  simp [h_b_sign, h_c_sign] at h_xor_eq
                  omega
                . simp [h_bz] at h_b_sign; simp [h_cz] at h_c_sign
                  simp [h_b_sign, h_c_sign] at h_xor_eq
      . simp [h_nzq] at h_xor_qsgn_eq
        simp [← h_xor_eq] at h_xor_qsgn_eq
        clear h_xor_eq h_xor_qsgn_z
        rw [← DivRemCoreAir_4_8.q_ext_def,
            ← DivRemCoreAir_4_8.nonzero_q_def] at *
        by_cases h_bz : 0 ≤ b
        . by_cases h_cz : 0 ≤ c
          . simp [h_bz] at h_b_sign; simp [h_cz] at h_c_sign
            simp [h_b_sign, h_c_sign] at h_xor_qsgn_eq
            simp [h_xor_qsgn_eq] at hub hlb h_bv_eq ⊢
            rw [Nat.mod_eq_of_lt (by omega)]
            rw [U64.toInt] at hub hlb h_bv_eq
            rw [if_neg (by simp [U64.negative, U64.toNat]; omega)] at hub hlb h_bv_eq
            simp [U64.toNat] at hub hlb h_bv_eq
            repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at hub hlb h_bv_eq
            ring_nf at hub hlb h_bv_eq
            clear hlb h_bv_eq
            by_contra hq3; simp at hq3
            have hc0 : 0 ≤ c * (air.core.q_0 row 0) ∧ c * (air.core.q_0 row 0) ≤ 2147483648 * 255 := by split_ands <;> nlinarith
            have hc1 : 0 ≤ c * (air.core.q_1 row 0) ∧ c * (air.core.q_1 row 0) ≤ 2147483648 * 255 := by split_ands <;> nlinarith
            have hc2 : 0 ≤ c * (air.core.q_2 row 0) ∧ c * (air.core.q_2 row 0) ≤ 2147483648 * 255 := by split_ands <;> nlinarith
            have hc3 : 1 * 128 ≤ c * (air.core.q_3 row 0) ∧ c * (air.core.q_3 row 0) ≤ 2147483648 * 255 := by split_ands <;> [ skip; nlinarith ]; apply mul_le_mul <;> omega
            clear *- ub_q0 ub_q1 ub_q2 ub_q3 hub hc0 hc1 hc2 hc3 hnzc h_cz
            rw [Int.bmod_eq_of_le (by simp; omega) (by simp; omega)] at hub
            omega
          . simp [h_bz] at h_b_sign; simp [h_cz] at h_c_sign
            simp [h_b_sign, h_c_sign] at h_xor_qsgn_eq
            simp [h_xor_qsgn_eq] at hub hlb h_bv_eq ⊢
            rw [Nat.mod_eq_of_lt (by omega)]
            rw [U64.toInt] at hub hlb h_bv_eq
            rw [if_pos (by simp [U64.negative, U64.toNat]; omega)] at hub hlb h_bv_eq
            simp [U64.toNat] at hub hlb h_bv_eq
            repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at hub hlb h_bv_eq
            ring_nf at hub hlb h_bv_eq
            by_contra hq3; simp at hq3
            have hc0 : -2147483648 * 255 ≤ c * (air.core.q_0 row 0) ∧ c * (air.core.q_0 row 0) ≤ 0 := by split_ands <;> nlinarith
            have hc1 : -2147483648 * 255 ≤ c * (air.core.q_1 row 0) ∧ c * (air.core.q_1 row 0) ≤ 0 := by split_ands <;> nlinarith
            have hc2 : -2147483648 * 255 ≤ c * (air.core.q_2 row 0) ∧ c * (air.core.q_2 row 0) ≤ 0 := by split_ands <;> nlinarith
            have hc3 : -2147483648 * 127 ≤ c * (air.core.q_3 row 0) ∧ c * (air.core.q_3 row 0) ≤ 0 := by split_ands <;> nlinarith
            simp at hc0 hc1 hc2 hc3
            simp [h_bv_eq, Int.bmod_def] at hub hlb h_bz
            rw [if_pos (by omega)] at hub hlb h_bz
            clear hlb h_bz
            have h_eq :
              -(c * 4294967296) + c * ↑↑(air.core.q_0 row 0) + c * ↑↑(air.core.q_1 row 0) * 256 + c * ↑↑(air.core.q_2 row 0) * 65536 + c * ↑↑(air.core.q_3 row 0) * 16777216
                =
              (-c) * (4294967296 - ((air.core.q_0 row 0) + (air.core.q_1 row 0) * 256 + (air.core.q_2 row 0) * 65536 + (air.core.q_3 row 0) * 16777216))
                := by ring_nf
            rw [h_eq] at hub; clear h_eq h_bv_eq
            have lb : 1 * 2147483649 ≤ -c * (4294967296 - (↑↑(air.core.q_0 row 0) + ↑↑(air.core.q_1 row 0) * 256 + ↑↑(air.core.q_2 row 0) * 65536 + ↑↑(air.core.q_3 row 0) * 16777216))
              := by apply mul_le_mul <;> omega
            have ub : -c * (4294967296 - (↑↑(air.core.q_0 row 0) + ↑↑(air.core.q_1 row 0) * 256 + ↑↑(air.core.q_2 row 0) * 65536 + ↑↑(air.core.q_3 row 0) * 16777216)) ≤ 2147483648 * (4294967296 - 1)
            := by
              apply mul_le_mul <;> try omega
              clear *- ub_q0 ub_q1 ub_q2 ub_q3 h_nzq
              suffices : 1 ≤ ((air.core.q_0 row 0) : ℤ) + ↑↑(air.core.q_1 row 0) * 256 + ↑↑(air.core.q_2 row 0) * 65536 + ↑↑(air.core.q_3 row 0) * 16777216
              . omega
              . grind
            rw [Int.emod_eq_of_lt (by omega) (by omega)] at hub
            omega
        . by_cases h_cz : 0 ≤ c
          . simp [h_bz] at h_b_sign; simp [h_cz] at h_c_sign
            simp [h_b_sign, h_c_sign] at h_xor_qsgn_eq
            simp [h_xor_qsgn_eq] at hub hlb h_bv_eq ⊢
            rw [Nat.mod_eq_of_lt (by omega)]
            rw [U64.toInt] at hub hlb h_bv_eq
            rw [if_pos (by simp [U64.negative, U64.toNat]; omega)] at hub hlb h_bv_eq
            simp [U64.toNat] at hub hlb h_bv_eq
            repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at hub hlb h_bv_eq
            iterate 3 (rw [add_assoc] at hub hlb h_bv_eq; simp at hub hlb h_bv_eq)
            rw [add_sub_assoc] at hub hlb h_bv_eq; simp at hub hlb h_bv_eq
            by_contra hq3; simp at hq3
            have ⟨ lb_q, ub_q ⟩ :
              1 ≤ ((air.core.q_0 row 0) : ℤ) + ↑↑(air.core.q_1 row 0) * 256 + ↑↑(air.core.q_2 row 0) * 65536 + ↑↑(air.core.q_3 row 0) * 16777216 ∧
              ((air.core.q_0 row 0) : ℤ) + ↑↑(air.core.q_1 row 0) * 256 + ↑↑(air.core.q_2 row 0) * 65536 + ↑↑(air.core.q_3 row 0) * 16777216 ≤ 2147483647
              := by clear *- ub_q0 ub_q1 ub_q2 hq3 h_nzq; grind
            obtain ⟨ q, eq_q ⟩ : exists q, q = ((air.core.q_0 row 0) : ℤ) + ↑↑(air.core.q_1 row 0) * 256 + ↑↑(air.core.q_2 row 0) * 65536 + ↑↑(air.core.q_3 row 0) * 16777216 := by simp
            rw [← eq_q] at hub hlb h_bv_eq lb_q ub_q
            clear eq_q
            have ⟨ lb, ub ⟩ :
              2147483648 * (1 + -4294967296) ≤ c * (q + -4294967296) ∧
              c * (q + -4294967296) ≤ 1 * (2147483647 + -4294967296)
            := by
              split_ands
              . trans 2147483648 * (q + -4294967296)
                . simp; omega
                . rw [Int.mul_le_mul_right_of_neg (by omega)]
                  omega
              . trans 1 * (q + -4294967296)
                . rw [Int.mul_le_mul_right_of_neg (by omega)]
                  omega
                . simp; omega
            simp at lb ub
            rw [Int.bmod_eq_of_le (by omega) (by omega)] at hlb
            omega
          . simp [h_bz] at h_b_sign; simp [h_cz] at h_c_sign
            simp [h_b_sign, h_c_sign] at h_xor_qsgn_eq
            simp [h_xor_qsgn_eq] at hub hlb h_bv_eq ⊢
            rw [Nat.mod_eq_of_lt (by omega)]
            rw [U64.toInt] at hub hlb h_bv_eq
            rw [if_neg (by simp [U64.negative, U64.toNat]; omega)] at hub hlb h_bv_eq
            simp [U64.toNat] at hub hlb h_bv_eq
            repeat rw [Int.emod_eq_of_lt (by omega) (by omega)] at hub hlb h_bv_eq
            simp at h_bz h_cz
            clear hnzc huc
            by_contra hq3; simp at hq3
            have ⟨ lb_q, ub_q ⟩ :
              2147483648 ≤ ((air.core.q_0 row 0) : ℤ) + ↑↑(air.core.q_1 row 0) * 256 + ↑↑(air.core.q_2 row 0) * 65536 + ↑↑(air.core.q_3 row 0) * 16777216 ∧
              ((air.core.q_0 row 0) : ℤ) + ↑↑(air.core.q_1 row 0) * 256 + ↑↑(air.core.q_2 row 0) * 65536 + ↑↑(air.core.q_3 row 0) * 16777216 ≤ 4294967295
              := by clear *- ub_q0 ub_q1 ub_q2 ub_q3 hq3 h_nzq; split_ands <;> omega
            obtain ⟨ q, eq_q ⟩ : exists q, q = ((air.core.q_0 row 0) : ℤ) + ↑↑(air.core.q_1 row 0) * 256 + ↑↑(air.core.q_2 row 0) * 65536 + ↑↑(air.core.q_3 row 0) * 16777216 := by simp
            rw [← eq_q] at hub hlb h_bv_eq lb_q ub_q
            clear *- hlc ub_q lb_q hlb h_cz h_bv_eq h_scase
            have ⟨ lb, ub ⟩ :
              (-2147483648) * 4294967295 ≤ c * q ∧ c * q ≤ (-1) * 2147483648
              := by split_ands <;> nlinarith
            simp at lb ub
            rw [Int.bmod_eq_of_le (by omega) (by omega)] at hlb h_bv_eq
            subst b
            have h_eq : c * q = -2147483648 := by omega
            clear lb ub hlb
            simp [h_eq] at h_scase
            have ub_c : c ≤ -2 := by omega
            clear h_cz h_scase
            have : c * q ≤ (-2) * 2147483648 := by nlinarith
            omega

    simp at q_sign_is_qsgn

    have h_q_ext :
      U64.toInt
        #v[BitVec.ofNat 8 (air.core.q_0 row 0), BitVec.ofNat 8 (air.core.q_1 row 0), BitVec.ofNat 8  (air.core.q_2 row 0), BitVec.ofNat 8 (air.core.q_3 row 0),
           BitVec.ofNat 8 (air.core.q_ext row 0), BitVec.ofNat 8 (air.core.q_ext row 0), BitVec.ofNat 8 (air.core.q_ext row 0), BitVec.ofNat 8 (air.core.q_ext row 0)] =
      U32.toInt
        #v[BitVec.ofNat 8 (air.core.q_0 row 0), BitVec.ofNat 8 (air.core.q_1 row 0), BitVec.ofNat 8 (air.core.q_2 row 0), BitVec.ofNat 8 (air.core.q_3 row 0)]
    := by
      rw [← U32.extend_toInt, U32.extend]
      simp [q_sign_is_qsgn]
    rw [h_q_ext] at h_bv_eq

    rw [Int.bmod_eq_of_le] at h_bv_eq
    . rw [h_bv_eq]
      rw [Int.mul_tdiv_cancel_left]
      . simp [U32.toInt, U32.negative, U32.toNat]
      . clear *- eq_zero_divisor ub_c0 ub_c1 ub_c2 ub_c3
        simp [U32.toInt, U32.negative, U32.toNat]
        split_ifs <;> omega
    . simp
      have rc := U32.toInt_range #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)]
      have rq := U32.toInt_range #v[BitVec.ofNat 8 ↑(air.core.q_0 row 0), BitVec.ofNat 8 ↑(air.core.q_1 row 0), BitVec.ofNat 8 ↑(air.core.q_2 row 0), BitVec.ofNat 8 ↑(air.core.q_3 row 0)]
      clear *- rc rq
      nlinarith
    . simp
      have rc := U32.toInt_range #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)]
      have rq := U32.toInt_range #v[BitVec.ofNat 8 ↑(air.core.q_0 row 0), BitVec.ofNat 8 ↑(air.core.q_1 row 0), BitVec.ofNat 8 ↑(air.core.q_2 row 0), BitVec.ofNat 8 ↑(air.core.q_3 row 0)]
      clear *- rc rq
      nlinarith

set_option maxRecDepth 1_000_000 in
include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the DIV/REM opcode, Part 4 --/
theorem spec_DIVREM_nczero_nsc_nrzero
  (h_divrem :
    (air.core.ctx row 0).instruction.opcode = 596 ∨
    (air.core.ctx row 0).instruction.opcode = 598)
  (h_c_zero : air.core.zero_divisor row 0 = 0)
  (h_scase : ¬ (U32.toInt
                  #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0),
                    BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0)] = -2147483648 ∧
                U32.toInt
                  #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0),
                    BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] = -1))
  (h_r_zero : air.core.r_zero row 0 = 0)
:
  (U32.toBV #v[(air.core.q_0 row 0).val,
               (air.core.q_1 row 0).val,
               (air.core.q_2 row 0).val,
               (air.core.q_3 row 0).val],
   U32.toBV #v[(air.core.r_0 row 0).val,
               (air.core.r_1 row 0).val,
               (air.core.r_2 row 0).val,
               (air.core.r_3 row 0).val])
    =
  (execute_DIV_REM_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .DRS)
:= by
  obtain ⟨ sop0, sop1, sop2, sop3 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2, op3 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  have ⟨ op_sum, op_divu, op_remu ⟩ :
    (air.core.opcode_div_flag row 0 + air.core.opcode_rem_flag row 0 = 1) ∧
    air.core.opcode_divu_flag row 0 = 0 ∧
    air.core.opcode_remu_flag row 0 = 0
    := by grind

  clear h_divrem sop0 sop1 sop2 sop3 op0 op1 op2 op3

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_divrem_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ub_q0, ub_cq0, ub_q1, ub_cq1, ub_q2, ub_cq2, ub_q3, ub_cq3,
           ub_r0, ub_cr0, ub_r1, ub_cr1, ub_r2, ub_cr2, ub_r3, ub_cr3 ⟩ := pa_rtc
  obtain ⟨ h_signed_msb, h_diff ⟩ := pa_bit
  clear pa_range pa_read

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
           b_zd, h_zd_c0, h_zd_q0, h_zd_c1, h_zd_q1, h_zd_c2, h_zd_q2, h_zd_c3, h_zd_q3,
           b_vnzd, h_vnzd,
           b_rz, b_rz_r0, b_rz_r1, b_rz_r2, b_rz_r3,
           b_vnsc, h_vnsc,
           b_bsgn, b_csgn, h_bsgn, h_csgn, h_xor_eq,
           b_qsgn, h_xor_qsgn_eq, h_xor_qsgn_z,
           h_r'_0, b_lt_0, h_r'inv_0, h_lt_0,
           h_r'_1, b_lt_1, h_r'inv_1, h_lt_1,
           h_r'_2, b_lt_2, h_r'inv_2, h_lt_2,
           h_r'_3, b_lt_3, h_r'inv_3, h_lt_3,
           b_ltm_3, h_prod_3, h_diff_3,
           b_ltm_2, h_prod_2, h_diff_2,
           b_ltm_1, h_prod_1, h_diff_1,
           b_ltm_0, h_prod_0, h_diff_0,
           h_sum_sc_ltm,
           rest ⟩ := constraints
  clear constrain_interactions rest

  have eq_sgn : air.core.signed row 0 = 1
    := by simpa [← DivRemCoreAir_4_8.signed_def]
  simp [eq_sgn] at *; clear h_bsgn h_csgn eq_sgn

  clear b_vnzd
  simp [← DivRemCoreAir_4_8.valid_and_not_zero_divisor_def] at h_vnzd
  simp [row_valid] at h_vnzd

  have ub_be : (air.core.b_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.b_ext_def]; clear *- b_bsgn; grind

  have ub_ce : (air.core.c_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.c_ext_def]; clear *- b_csgn; grind

  have ub_qe : (air.core.q_ext row 0) < 256
    := by rw [← DivRemCoreAir_4_8.q_ext_def]; clear *- b_qsgn; grind

  have eq_zero_divisor :
    air.core.zero_divisor row 0 = 1 ↔
      air.core.c_0 row 0 = 0 ∧ air.core.c_1 row 0 = 0 ∧ air.core.c_2 row 0 = 0 ∧ air.core.c_3 row 0 = 0
  := by
    constructor
    . intro h_div; simp_all
    . intro ⟨ z_c0, z_c1, z_c2, z_c3 ⟩
      clear *- b_zd h_vnzd z_c0 z_c1 z_c2 z_c3
      simp [← DivRemCoreAir_4_8.c_sum_def] at h_vnzd
      grind

  suffices h_toInt :
    U32.toInt #v[(air.core.q_0 row 0).val,
                 (air.core.q_1 row 0).val,
                 (air.core.q_2 row 0).val,
                 (air.core.q_3 row 0).val]
      =
    (U32.toInt #v[(air.core.b_0 row 0).val,
                  (air.core.b_1 row 0).val,
                  (air.core.b_2 row 0).val,
                  (air.core.b_3 row 0).val]).tdiv
    (U32.toInt #v[(air.core.c_0 row 0).val,
                  (air.core.c_1 row 0).val,
                  (air.core.c_2 row 0).val,
                  (air.core.c_3 row 0).val]) ∧
    U32.toInt #v[(air.core.r_0 row 0).val,
                 (air.core.r_1 row 0).val,
                 (air.core.r_2 row 0).val,
                 (air.core.r_3 row 0).val]
      =
    (U32.toInt #v[(air.core.b_0 row 0).val,
                  (air.core.b_1 row 0).val,
                  (air.core.b_2 row 0).val,
                  (air.core.b_3 row 0).val]).tmod
    (U32.toInt #v[(air.core.c_0 row 0).val,
                  (air.core.c_1 row 0).val,
                  (air.core.c_2 row 0).val,
                  (air.core.c_3 row 0).val])
  . simp [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
    simp [BabyBear.toInt_0_inv ub_c0 ub_c1 ub_c2 ub_c3]
    simp_all
    clear *- ub_b0 ub_b1 ub_b2 ub_b3
             ub_c0 ub_c1 ub_c2 ub_c3
             ub_q0 ub_q1 ub_q2 ub_q3
             h_toInt h_scase eq_zero_divisor
    simp [← BitVec.toInt_inj]
    have range_b := U32.toInt_range #v[(air.core.b_0 row 0).val, (air.core.b_1 row 0).val, (air.core.b_2 row 0).val, (air.core.b_3 row 0).val]
    have range_c := U32.toInt_range #v[(air.core.c_0 row 0).val, (air.core.c_1 row 0).val, (air.core.c_2 row 0).val, (air.core.c_3 row 0).val]
    simp_all [BitVec.ofNat]
    obtain ⟨ lm, um ⟩ := Int.tmod_range_32 range_b range_c
    obtain ⟨ ld, ud ⟩ := Int.tdiv_range_32 (by simp [U32.toInt, U32.negative, U32.toNat]; clear *- ub_c0 ub_c1 ub_c2 ub_c3 eq_zero_divisor; split_ifs <;> omega) h_scase range_b range_c
    rw [Int.bmod_eq_of_le (by simp; omega) (by simp; omega)]
    rw [Int.bmod_eq_of_le (by simp; omega) (by simp; omega)]
    simp

  . have b_sign_is_bsgn
    :
      U32.ext #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val] true =
      air.core.b_ext row 0
    := by
      rw [← DivRemCoreAir_4_8.b_ext_def]
      clear *- b_bsgn ub_b0 ub_b1 ub_b2 ub_b3 h_signed_msb
      simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
      rw [Nat.mod_eq_of_lt (by omega)]
      grind

    have c_sign_is_csgn
    :
      U32.ext #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val] true =
      air.core.c_ext row 0
    := by
      rw [← DivRemCoreAir_4_8.c_ext_def]
      clear *- b_csgn ub_c0 ub_c1 ub_c2 ub_c3 h_signed_msb
      simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
      rw [Nat.mod_eq_of_lt (by omega)]
      grind

    simp [← DivRemCoreAir_4_8.carry_0,
          ← DivRemCoreAir_4_8.carry_1,
          ← DivRemCoreAir_4_8.carry_2,
          ← DivRemCoreAir_4_8.carry_3,
          ← DivRemCoreAir_4_8.carry_ext_0_def,
          ← DivRemCoreAir_4_8.carry_ext_1_def,
          ← DivRemCoreAir_4_8.carry_ext_2_def,
          ← DivRemCoreAir_4_8.carry_ext_3_def
          ] at *

    repeat rw [mul_comm (b := 2005401601)] at *

    simp [← DivRemCoreAir_4_8.valid_and_not_special_case_def,
          ← DivRemCoreAir_4_8.special_case_def] at *

    simp_all

    have h_bv_eq :=
      @divrem_split
        (air.core.b_0 row 0) (air.core.b_1 row 0) (air.core.b_2 row 0) (air.core.b_3 row 0) (air.core.b_ext row 0) (air.core.b_ext row 0) (air.core.b_ext row 0) (air.core.b_ext row 0)
        (air.core.c_0 row 0) (air.core.c_1 row 0) (air.core.c_2 row 0) (air.core.c_3 row 0)
        (air.core.q_0 row 0) (air.core.q_1 row 0) (air.core.q_2 row 0) (air.core.q_3 row 0)
        (air.core.r_0 row 0) (air.core.r_1 row 0) (air.core.r_2 row 0) (air.core.r_3 row 0)
        (air.core.c_ext row 0) (air.core.q_ext row 0) (air.core.b_ext row 0)
        ub_b0 ub_b1 ub_b2 ub_b3 ub_be ub_be ub_be ub_be
        ub_c0 ub_c1 ub_c2 ub_c3 ub_q0 ub_q1 ub_q2 ub_q3
        ub_r0 ub_r1 ub_r2 ub_r3
        ub_ce ub_qe ub_be
        (by clear *- ub_cq0; assumption)
        (by clear *- ub_cq1; assumption)
        (by clear *- ub_cq2; assumption)
        (by clear *- ub_cq3; assumption)
        (by clear *- ub_cr0; grind)
        (by clear *- ub_cr1; grind)
        (by clear *- ub_cr2; grind)
        (by clear *- ub_cr3; grind)

    have aux_c_nzero :
      ¬U32.toInt #v[(air.core.c_0 row 0), (air.core.c_1 row 0), (air.core.c_2 row 0), (air.core.c_3 row 0)] = 0
    := by
      clear *- eq_zero_divisor ub_c0 ub_c1 ub_c2 ub_c3
      simp [U32.toInt, U32.negative, U32.toNat]
      split_ifs <;> grind

    have aux_r_nzero :
      ¬U32.toInt #v[(air.core.r_0 row 0), (air.core.r_1 row 0), (air.core.r_2 row 0), (air.core.r_3 row 0)] = 0
    := by
      clear *- ub_r0 ub_r1 ub_r2 ub_r3 h_vnsc
      have : ¬ air.core.r_sum row 0 = 0
        := by intro hz; grind
      rw [← DivRemCoreAir_4_8.r_sum_def] at this
      simp [U32.toInt, U32.negative, U32.toNat]
      split_ifs <;> grind

    have aux_q_ext :
      air.core.q_ext row 0 =
        if U32.toInt #v[(air.core.q_0 row 0).val, (air.core.q_1 row 0).val, (air.core.q_2 row 0).val, (air.core.q_3 row 0).val] = 0
        then 0
        else if air.core.b_ext row 0 = air.core.c_ext row 0 then 0 else 255
    := by
      clear ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cr0 ub_cr1 ub_cr2 ub_cr3
      by_cases hqz : air.core.nonzero_q row 0 = 0 <;> simp [hqz] at h_xor_qsgn_eq
      . rw [if_pos]
        rotate_left
        . simp [← DivRemCoreAir_4_8.nonzero_q_def] at *
          simp [U32.toInt, U32.negative, U32.toNat]
          split_ifs <;> grind
        . rcases b_qsgn with hqs | hqs
          . rw [← DivRemCoreAir_4_8.q_ext_def]; simp [hqs]
          . exfalso
            simp [← DivRemCoreAir_4_8.q_ext_def,
                  ← DivRemCoreAir_4_8.nonzero_q_def] at *
            obtain ⟨ zq0, zq1, zq2, zq3 ⟩ :
              air.core.q_0 row 0 = 0 ∧ air.core.q_1 row 0 = 0 ∧
              air.core.q_2 row 0 = 0 ∧ air.core.q_3 row 0 = 0
              := by clear *- ub_q0 ub_q1 ub_q2 ub_q3 hqz; grind
            simp [hqs] at *
            simp [← h_xor_qsgn_z] at *
            simp_all

            have : U64.toBV #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0), BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0),
                               BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0)] =
                   U64.toBV (U32.extend #v[BitVec.ofNat 8 (air.core.b_0 row 0), BitVec.ofNat 8 (air.core.b_1 row 0), BitVec.ofNat 8 (air.core.b_2 row 0), BitVec.ofNat 8 (air.core.b_3 row 0)] true)
            := by
              simp [U32.extend, ← b_sign_is_bsgn, U32.ext, U32.negative, U32.toNat, BitVec.ofNat]
              split_ifs <;> congr
            rw [this] at h_bv_eq; clear this
            have : U64.toBV #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0),
                               BitVec.ofNat 8 (air.core.c_ext row 0), BitVec.ofNat 8 (air.core.c_ext row 0), BitVec.ofNat 8 (air.core.c_ext row 0), BitVec.ofNat 8 (air.core.c_ext row 0)] =
                   U64.toBV (U32.extend #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)] true)
            := by
              simp [U32.extend, ← c_sign_is_csgn, U32.ext, U32.negative, U32.toNat, BitVec.ofNat]
              split_ifs <;> congr
            rw [this] at h_bv_eq; clear this

            simp [← BitVec.toInt_inj] at h_bv_eq
            simp [← DivRemCoreAir_4_8.b_ext_def,
                  ← DivRemCoreAir_4_8.c_ext_def] at *

            rcases b_bsgn with b_sgn | b_sgn <;>
            rcases b_csgn with c_sgn | c_sgn <;>
            simp_all

            . have ⟨ lb_b, ub_b ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.b_0 row 0), BitVec.ofNat 8 (air.core.b_1 row 0), BitVec.ofNat 8 (air.core.b_2 row 0), BitVec.ofNat 8 (air.core.b_3 row 0)]
              have ⟨ lb_c, ub_c ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)]

              obtain ⟨ b, eq_b ⟩ : exists b, U32.toInt #v[BitVec.ofNat 8 (air.core.b_0 row 0), BitVec.ofNat 8 (air.core.b_1 row 0), BitVec.ofNat 8 (air.core.b_2 row 0), BitVec.ofNat 8 (air.core.b_3 row 0)] = b := by simp
              rw [eq_b] at h_bv_eq ub_b lb_b
              obtain ⟨ c, eq_c ⟩ : exists c, U32.toInt #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)] = c := by simp
              rw [eq_c] at h_bv_eq ub_c lb_c

              have ub_c' : ¬ 0 ≤ c
              := by
                rw [← eq_c, ← U32.negative_toInt]
                simp [U32.ext] at c_sign_is_csgn
                assumption
              simp at ub_c'

              simp [U64.toInt, U64.negative, U64.toNat] at h_bv_eq
              rw [if_neg (by omega)] at h_bv_eq
              rw [h_bv_eq] at lb_b ub_b
              rw [Int.bmod_def] at lb_b ub_b
              split_ifs at ub_b with h_if
              . clear *- ub_r0 ub_r1 ub_r2 ub_r3 h_if lb_b ub_b ub_c' lb_c
                simp_all
                omega
              . clear *- ub_r0 ub_r1 ub_r2 ub_r3 h_if lb_b ub_b ub_c' lb_c
                simp_all
                omega
            . have ⟨ lb_b, ub_b ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.b_0 row 0), BitVec.ofNat 8 (air.core.b_1 row 0), BitVec.ofNat 8 (air.core.b_2 row 0), BitVec.ofNat 8 (air.core.b_3 row 0)]
              have ⟨ lb_c, ub_c ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)]

              obtain ⟨ b, eq_b ⟩ : exists b, U32.toInt #v[BitVec.ofNat 8 (air.core.b_0 row 0), BitVec.ofNat 8 (air.core.b_1 row 0), BitVec.ofNat 8 (air.core.b_2 row 0), BitVec.ofNat 8 (air.core.b_3 row 0)] = b := by simp
              rw [eq_b] at h_bv_eq ub_b lb_b
              obtain ⟨ c, eq_c ⟩ : exists c, U32.toInt #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)] = c := by simp
              rw [eq_c] at h_bv_eq ub_c lb_c

              have lb_c'' : ¬ ¬ 0 ≤ c
              := by
                rw [← eq_c, ← U32.negative_toInt]
                simp [U32.ext] at c_sign_is_csgn
                assumption
              simp at lb_c''; clear lb_c

              have lb_c' : 0 < c
              := by
                suffices : ¬ (c = 0)
                . clear *- lb_c'' this; omega
                . clear *- eq_zero_divisor ub_c0 ub_c1 ub_c2 ub_c3 eq_c
                  rw [← eq_c]; intro hz
                  simp [U32.toInt, U32.negative, U32.toNat] at hz
                  split_ifs at hz <;> grind
              clear lb_c''

              have ub_b' : ¬ 0 ≤ b
              := by
                rw [← eq_b, ← U32.negative_toInt]
                simp [U32.ext] at b_sign_is_bsgn
                assumption
              simp at ub_b'; clear ub_b

              simp [U64.toInt, U64.negative, U64.toNat] at h_bv_eq
              rw [if_pos (by omega)] at h_bv_eq
              iterate 3 (rw [add_assoc] at h_bv_eq; simp at h_bv_eq)
              rw [add_sub_assoc] at h_bv_eq; simp at h_bv_eq
              repeat rw [Int.emod_eq_of_lt (b := 256) (by omega) (by omega)] at h_bv_eq
              simp [Int.bmod_def] at h_bv_eq
              rw [if_neg] at h_bv_eq
              . simp [h_bv_eq] at lb_b
                clear *- ub_r0 ub_r1 ub_r2 ub_r3 lb_b lb_c' ub_c
                omega
              . clear *- ub_r0 ub_r1 ub_r2 ub_r3 lb_b lb_c' ub_c
                omega

      . rw [← h_xor_eq] at h_xor_qsgn_eq
        simp [← DivRemCoreAir_4_8.q_ext_def,
              ← DivRemCoreAir_4_8.b_ext_def,
              ← DivRemCoreAir_4_8.c_ext_def,
              ← DivRemCoreAir_4_8.nonzero_q_def] at *
        clear *- b_bsgn b_csgn h_xor_qsgn_eq b_sign_is_bsgn c_sign_is_csgn hqz ub_q0 ub_q1 ub_q2 ub_q3
        rw [if_neg]
        . grind
        . simp [U32.toInt, U32.negative, U32.toNat]
          split_ifs <;> grind

    have ⟨ q_sign_is_qsgn, r_sign_is_rsgn ⟩  :=
      @divrem_quot_rem_sign
        (air.core.b_0 row 0) (air.core.b_1 row 0) (air.core.b_2 row 0) (air.core.b_3 row 0)
        (air.core.c_0 row 0) (air.core.c_1 row 0) (air.core.c_2 row 0) (air.core.c_3 row 0)
        (air.core.q_0 row 0) (air.core.q_1 row 0) (air.core.q_2 row 0) (air.core.q_3 row 0)
        (air.core.r_0 row 0) (air.core.r_1 row 0) (air.core.r_2 row 0) (air.core.r_3 row 0)
        (air.core.b_ext row 0) (air.core.c_ext row 0) (air.core.q_ext row 0)
        ub_b0 ub_b1 ub_b2 ub_b3
        ub_c0 ub_c1 ub_c2 ub_c3
        ub_q0 ub_q1 ub_q2 ub_q3
        ub_r0 ub_r1 ub_r2 ub_r3
        ub_be ub_ce ub_qe
        ub_cq0 ub_cq1 ub_cq2 ub_cq3
        (by clear *- ub_cr0; grind)
        (by clear *- ub_cr1; grind)
        (by clear *- ub_cr2; grind)
        (by clear *- ub_cr3; grind)
        aux_c_nzero aux_r_nzero
        (by simp [b_sign_is_bsgn])
        (by simp [c_sign_is_csgn])
        aux_q_ext

    clear ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cr0 ub_cr1 ub_cr2 ub_cr3
    symm at q_sign_is_qsgn r_sign_is_rsgn
    simp [Fin.ext_iff] at q_sign_is_qsgn r_sign_is_rsgn
    rw [Nat.mod_eq_of_lt (by simp [U32.ext, U32.negative]; split_ifs <;> simp)] at q_sign_is_qsgn r_sign_is_rsgn

    have eb : U64.toBV #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0), BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0),
                          BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0)] =
              U64.toBV (U32.extend #v[BitVec.ofNat 8 (air.core.b_0 row 0), BitVec.ofNat 8 (air.core.b_1 row 0), BitVec.ofNat 8 (air.core.b_2 row 0), BitVec.ofNat 8 (air.core.b_3 row 0)] true)
    := by
      simp [U32.extend, ← b_sign_is_bsgn, U32.ext, U32.negative, U32.toNat, BitVec.ofNat]
      split_ifs <;> congr
    have ec : U64.toBV #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0),
                          BitVec.ofNat 8 (air.core.c_ext row 0), BitVec.ofNat 8 (air.core.c_ext row 0), BitVec.ofNat 8 (air.core.c_ext row 0), BitVec.ofNat 8 (air.core.c_ext row 0)] =
              U64.toBV (U32.extend #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)] true)
    := by
      simp [U32.extend, ← c_sign_is_csgn, U32.ext, U32.negative, U32.toNat, BitVec.ofNat]
      split_ifs <;> congr
    have eq : U64.toBV #v[BitVec.ofNat 8 ↑(air.core.q_0 row 0), BitVec.ofNat 8 ↑(air.core.q_1 row 0), BitVec.ofNat 8 ↑(air.core.q_2 row 0), BitVec.ofNat 8 ↑(air.core.q_3 row 0),
                         BitVec.ofNat 8 (air.core.q_ext row 0), BitVec.ofNat 8 (air.core.q_ext row 0), BitVec.ofNat 8 (air.core.q_ext row 0), BitVec.ofNat 8 (air.core.q_ext row 0)] =
              U64.toBV (U32.extend #v[BitVec.ofNat 8 (air.core.q_0 row 0), BitVec.ofNat 8 (air.core.q_1 row 0), BitVec.ofNat 8 (air.core.q_2 row 0), BitVec.ofNat 8 (air.core.q_3 row 0)] true)
    := by
      simp [U32.extend, ← q_sign_is_qsgn, U32.ext, U32.negative, U32.toNat, BitVec.ofNat]
      split_ifs <;> congr
    have er : U64.toBV #v[BitVec.ofNat 8 ↑(air.core.r_0 row 0), BitVec.ofNat 8 ↑(air.core.r_1 row 0), BitVec.ofNat 8 ↑(air.core.r_2 row 0), BitVec.ofNat 8 ↑(air.core.r_3 row 0),
                          BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0), BitVec.ofNat 8 (air.core.b_ext row 0)] =
              U64.toBV (U32.extend #v[BitVec.ofNat 8 (air.core.r_0 row 0), BitVec.ofNat 8 (air.core.r_1 row 0), BitVec.ofNat 8 (air.core.r_2 row 0), BitVec.ofNat 8 (air.core.r_3 row 0)] true)
    := by
      simp [U32.extend, ← r_sign_is_rsgn, U32.ext, U32.negative, U32.toNat, BitVec.ofNat]
      split_ifs <;> congr

    simp [eb, ec, eq, er] at h_bv_eq
    simp [← BitVec.toInt_inj] at h_bv_eq

    rw [Int.tdiv_tmod_unique_full]
    rotate_left
    . intro hz
      simp [U32.toInt, U32.negative, U32.toNat] at hz
      clear *- hz ub_c0 ub_c1 ub_c2 ub_c3 eq_zero_divisor
      omega

    . -- First condition
      have cond1 :
        U32.toInt
          #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0),
            BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0)] =
        U32.toInt
          #v[BitVec.ofNat 8 ↑(air.core.q_0 row 0), BitVec.ofNat 8 ↑(air.core.q_1 row 0),
            BitVec.ofNat 8 ↑(air.core.q_2 row 0), BitVec.ofNat 8 ↑(air.core.q_3 row 0)] *
        U32.toInt
          #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0),
            BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] +
        U32.toInt
          #v[BitVec.ofNat 8 ↑(air.core.r_0 row 0), BitVec.ofNat 8 ↑(air.core.r_1 row 0),
            BitVec.ofNat 8 ↑(air.core.r_2 row 0), BitVec.ofNat 8 ↑(air.core.r_3 row 0)]
      := by
        have ⟨ lb_b, ub_b ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.b_0 row 0), BitVec.ofNat 8 (air.core.b_1 row 0), BitVec.ofNat 8 (air.core.b_2 row 0), BitVec.ofNat 8 (air.core.b_3 row 0)]
        have ⟨ lb_c, ub_c ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)]
        have ⟨ lb_q, ub_q ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.q_0 row 0), BitVec.ofNat 8 (air.core.q_1 row 0), BitVec.ofNat 8 (air.core.q_2 row 0), BitVec.ofNat 8 (air.core.q_3 row 0)]
        have ⟨ lb_r, ub_r ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.r_0 row 0), BitVec.ofNat 8 (air.core.r_1 row 0), BitVec.ofNat 8 (air.core.r_2 row 0), BitVec.ofNat 8 (air.core.r_3 row 0)]
        obtain ⟨ b, eq_b ⟩ : exists b, U32.toInt #v[BitVec.ofNat 8 (air.core.b_0 row 0), BitVec.ofNat 8 (air.core.b_1 row 0), BitVec.ofNat 8 (air.core.b_2 row 0), BitVec.ofNat 8 (air.core.b_3 row 0)] = b := by simp
        rw [eq_b] at h_bv_eq lb_b ub_b h_scase ⊢
        obtain ⟨ c, eq_c ⟩ : exists c, U32.toInt #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)] = c := by simp
        rw [eq_c] at h_bv_eq lb_c ub_c h_scase ⊢
        obtain ⟨ q, eq_q ⟩ : exists q, U32.toInt #v[BitVec.ofNat 8 (air.core.q_0 row 0), BitVec.ofNat 8 (air.core.q_1 row 0), BitVec.ofNat 8 (air.core.q_2 row 0), BitVec.ofNat 8 (air.core.q_3 row 0)] = q := by simp
        rw [eq_q] at h_bv_eq lb_q ub_q ⊢
        obtain ⟨ r, eq_r ⟩ : exists r, U32.toInt #v[BitVec.ofNat 8 (air.core.r_0 row 0), BitVec.ofNat 8 (air.core.r_1 row 0), BitVec.ofNat 8 (air.core.r_2 row 0), BitVec.ofNat 8 (air.core.r_3 row 0)] = r := by simp
        rw [eq_r] at h_bv_eq lb_r ub_r ⊢
        have h_c_nz : ¬ c = 0
        := by
          rw [← eq_c]; clear *- aux_c_nzero ub_c0 ub_c1 ub_c2 ub_c3
          intro hz; apply aux_c_nzero
          simp [U32.toInt, U32.negative, U32.toNat] at *
          split_ifs <;> simp_all
        have h_r_nz : ¬ r = 0
        := by
          rw [← eq_r]; clear *- aux_r_nzero ub_r0 ub_r1 ub_r2 ub_r3
          intro hz; apply aux_r_nzero
          simp [U32.toInt, U32.negative, U32.toNat] at *
          split_ifs <;> simp_all
        -- h_scase
        clear *- h_scase lb_b lb_c lb_q lb_r ub_b ub_c ub_q ub_r h_c_nz h_r_nz h_bv_eq
        rw [mul_comm]; subst b
        have ⟨ lb_prod, ub_prod ⟩ :
          -2147483648 * 2147483647 ≤ c * q ∧ c * q ≤ (-2147483648) * (-2147483648)
          := by split_ands <;> nlinarith
        simp at lb_prod ub_prod
        rw [Int.bmod_eq_of_le (by omega) (by omega)]

      simp [cond1]; rw [← cond1]
      clear h_bv_eq eb ec eq er

      have cond2 :
        |U32.toInt
          #v[BitVec.ofNat 8 ↑(air.core.r_0 row 0), BitVec.ofNat 8 ↑(air.core.r_1 row 0),
             BitVec.ofNat 8 ↑(air.core.r_2 row 0), BitVec.ofNat 8 ↑(air.core.r_3 row 0)]| <
        |U32.toInt
          #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0),
             BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)]|
      := by
        have ⟨ hlm0, hlm1, hlm2, hlm3 ⟩ :
          ((air.core.lt_marker_0 row 0) = 1 → (air.core.lt_marker_1 row 0) = 0 ∧ (air.core.lt_marker_2 row 0) = 0 ∧ (air.core.lt_marker_3 row 0) = 0) ∧
          ((air.core.lt_marker_1 row 0) = 1 → (air.core.lt_marker_0 row 0) = 0 ∧ (air.core.lt_marker_2 row 0) = 0 ∧ (air.core.lt_marker_3 row 0) = 0) ∧
          ((air.core.lt_marker_2 row 0) = 1 → (air.core.lt_marker_0 row 0) = 0 ∧ (air.core.lt_marker_1 row 0) = 0 ∧ (air.core.lt_marker_3 row 0) = 0) ∧
          ((air.core.lt_marker_3 row 0) = 1 → (air.core.lt_marker_0 row 0) = 0 ∧ (air.core.lt_marker_1 row 0) = 0 ∧ (air.core.lt_marker_2 row 0) = 0)
        := by
          clear *- b_ltm_0 b_ltm_1 b_ltm_2 b_ltm_3 h_sum_sc_ltm
          grind (splits := 14)

        have ⟨ ub_r'0, ub_r'1, ub_r'2, ub_r'3 ⟩ :
          (air.core.r_prime_0 row 0).val < 256 ∧ (air.core.r_prime_1 row 0).val < 256 ∧
          (air.core.r_prime_2 row 0).val < 256 ∧ (air.core.r_prime_3 row 0).val < 256
        := by
          have h_xor : air.core.sign_xor row 0 = 0 ∨ air.core.sign_xor row 0 = 1
            := by clear *- b_bsgn b_csgn h_xor_eq; grind
          rcases h_xor with h_xor | h_xor <;> simp [h_xor] at *
          . rw [← h_r'_0, ← h_r'_1, ← h_r'_2, ← h_r'_3]
            clear *- ub_r0 ub_r1 ub_r2 ub_r3
            simp_all
          . clear *- b_lt_0 b_lt_1 b_lt_2 b_lt_3
                     h_r'inv_0 h_r'inv_1 h_r'inv_2 h_r'inv_3
                     h_lt_0 h_lt_1 h_lt_2 h_lt_3
                     ub_r0 ub_r1 ub_r2 ub_r3
            simp [← DivRemCoreAir_4_8.carry_lt_0_def,
                  ← DivRemCoreAir_4_8.carry_lt_1_def,
                  ← DivRemCoreAir_4_8.carry_lt_2_def,
                  ← DivRemCoreAir_4_8.carry_lt_3_def] at *
            have ub0 : ¬ (air.core.r_prime_0 row 0 - 256 = 0)  := by intro hz; simp_all
            have ub1 : ¬ (air.core.r_prime_1 row 0 - 256 = 0)  := by intro hz; simp_all
            have ub2 : ¬ (air.core.r_prime_2 row 0 - 256 = 0)  := by intro hz; simp_all
            have ub3 : ¬ (air.core.r_prime_3 row 0 - 256 = 0)  := by intro hz; simp_all
            rw [sub_eq_zero] at ub0 ub1 ub2 ub3
            clear h_r'inv_0 h_r'inv_1 h_r'inv_2 h_r'inv_3
            rcases h_lt_0 <;> rcases h_lt_1 <;>
            rcases h_lt_2 <;> rcases h_lt_3 <;>
            simp_all <;> omega

        have h_nonono_r : ¬ (air.core.r_0 row 0 = 0 ∧ air.core.r_1 row 0 = 0 ∧ air.core.r_2 row 0 = 0 ∧ air.core.r_3 row 0 = 128)
        := by
          intro h_yesyessyes_r
          simp_all
          replace r_sign_is_rsgn : air.core.b_sign row 0 = 1
          := by
            clear *- r_sign_is_rsgn
            simp [U32.ext, U32.negative, U32.toNat] at r_sign_is_rsgn
            rw [← DivRemCoreAir_4_8.b_ext_def] at r_sign_is_rsgn
            grind
          simp_all
          symm at h_xor_eq
          rcases b_csgn with b_csgn | b_csgn
          . simp [b_csgn] at h_xor_eq
            simp [← DivRemCoreAir_4_8.carry_lt_0_def,
                  ← DivRemCoreAir_4_8.carry_lt_1_def,
                  ← DivRemCoreAir_4_8.carry_lt_2_def,
                  ← DivRemCoreAir_4_8.carry_lt_3_def] at *
            simp_all
            have : air.core.r_prime_0 row 0 = 0 := by clear *- ub_r'0 h_lt_0; grind
            simp [this] at *
            have : air.core.r_prime_1 row 0 = 0 := by clear *- ub_r'1 h_lt_1; grind
            simp [this] at *
            have : air.core.r_prime_2 row 0 = 0 := by clear *- ub_r'2 h_lt_2; grind
            simp [this] at *
            have : air.core.r_prime_3 row 0 = 128 := by clear *- ub_r'3 b_lt_3; grind
            simp [this] at *
            simp_all
            rcases b_ltm_0 with hlt0 | hlt0
            . rcases b_ltm_1 with hlt1 | hlt1
              . rcases b_ltm_2 with hlt2 | hlt2
                . simp_all
                  clear *- c_sign_is_csgn h_diff b_csgn ub_c3
                  simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide] at c_sign_is_csgn
                  rw [← DivRemCoreAir_4_8.c_ext_def] at c_sign_is_csgn
                  simp_all
                  grind
                . simp_all
                  have : air.core.c_3 row 0 = 128 := by clear *- ub_c3 h_prod_3; grind
                  simp_all
              . simp_all
                have : air.core.c_3 row 0 = 128 := by clear *- ub_c3 h_prod_3; grind
                simp_all
            . simp_all
              have : air.core.c_3 row 0 = 128 := by clear *- ub_c3 h_prod_3; grind
              simp_all
          . have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := by decide
            simp [b_csgn] at h_xor_eq
            simp [h_xor_eq] at h_r'_0 h_r'_1 h_r'_2 h_r'_3
            symm at h_r'_0 h_r'_1 h_r'_2 h_r'_3
            simp [← DivRemCoreAir_4_8.carry_lt_0_def,
                  ← DivRemCoreAir_4_8.carry_lt_1_def,
                  ← DivRemCoreAir_4_8.carry_lt_2_def,
                  ← DivRemCoreAir_4_8.carry_lt_3_def] at *
            clear h_r'inv_0 h_r'inv_1 h_r'inv_2 h_r'inv_3
                  b_lt_0 b_lt_1 b_lt_2 b_lt_3
                  h_lt_0 h_lt_1 h_lt_2 h_lt_3
            simp_all
            rcases b_ltm_0 with hlt0 | hlt0
            . rcases b_ltm_1 with hlt1 | hlt1
              . rcases b_ltm_2 with hlt2 | hlt2
                . simp_all
                  clear *- c_sign_is_csgn h_diff b_csgn ub_c3
                  simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide] at c_sign_is_csgn
                  rw [← DivRemCoreAir_4_8.c_ext_def] at c_sign_is_csgn
                  simp_all
                  grind
                . simp_all
                  have : air.core.c_3 row 0 = 128 := by clear *- ub_c3 h_prod_3; grind
                  simp_all
                  clear *- ub_c2 h_diff
                  grind
              . simp_all
                have : air.core.c_3 row 0 = 128 := by clear *- ub_c3 h_prod_3; grind
                simp_all
                clear *- ub_c1 h_diff
                grind
            . simp_all
              have : air.core.c_3 row 0 = 128 := by clear *- ub_c3 h_prod_3; grind
              simp_all
              clear *- ub_c0 h_diff
              grind

        obtain ⟨ msb_b, msb_c ⟩ := h_signed_msb
        have h_c_sign : air.core.c_sign row 0 = if 0 ≤ U32.toInt #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0), BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] then 0 else 1
        := by
          simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide]
          split_ifs with hif1 hif2 hif2
          . simp [U32.toNat] at hif2; omega
          . clear *- ub_c3 msb_c hif1 b_csgn
            rw [Nat.mod_eq_of_lt (by omega)] at hif1
            grind
          . clear *- ub_c3 msb_c hif1 b_csgn
            rw [Nat.mod_eq_of_lt (by omega)] at hif1
            grind
          . simp [U32.toNat] at hif2; omega

        have h_r_sign : air.core.b_sign row 0 = if 0 ≤ U32.toInt #v[BitVec.ofNat 8 ↑(air.core.r_0 row 0), BitVec.ofNat 8 ↑(air.core.r_1 row 0), BitVec.ofNat 8 ↑(air.core.r_2 row 0), BitVec.ofNat 8 ↑(air.core.r_3 row 0)] then 0 else 1
        := by
          clear *- r_sign_is_rsgn
          simp [U32.ext, ← DivRemCoreAir_4_8.b_ext_def, U32.negative_toInt] at r_sign_is_rsgn
          split_ifs with h_if
          . rw [if_neg (by omega)] at r_sign_is_rsgn
            omega
          . rw [if_pos (by omega)] at r_sign_is_rsgn
            omega

        split_ifs at h_c_sign with sgn_c <;>
        split_ifs at h_r_sign with sgn_r
        . rw [abs_of_nonneg sgn_c, abs_of_nonneg sgn_r]
          simp [h_c_sign, h_r_sign] at *
          simp [← h_xor_eq] at *
          symm at h_r'_0 h_r'_1 h_r'_2 h_r'_3
          simp_all

          have h_lt :=
            @BabyBear.Circuits.less_than
              (air.core.r_0 row 0) (air.core.r_1 row 0) (air.core.r_2 row 0) (air.core.r_3 row 0)
              (air.core.c_0 row 0) (air.core.c_1 row 0) (air.core.c_2 row 0) (air.core.c_3 row 0)
              (air.core.lt_marker_0 row 0) (air.core.lt_marker_1 row 0) (air.core.lt_marker_2 row 0) (air.core.lt_marker_3 row 0)
              (air.core.lt_diff row 0)
              (air.core.r_3 row 0) (air.core.c_3 row 0)
              0
              ((air.core.lt_marker_3 row 0) + (air.core.lt_marker_2 row 0) + (air.core.lt_marker_1 row 0) + (air.core.lt_marker_0 row 0))
              ub_r0 ub_r1 ub_r2 ub_r3
              ub_c0 ub_c1 ub_c2 ub_c3
              (by right; assumption)
              (by simp) (by simp)
              b_ltm_0 b_ltm_1 b_ltm_2 b_ltm_3
              (by right; assumption)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_3; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_2; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_1; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_0; grind)
              (by left; assumption)
              (by clear *- h_prod_3; grind)
              (by clear *- h_prod_2; grind)
              (by clear *- h_prod_1; grind)
              (by left; assumption)
              (by simpa) (by simpa)
              (by simp [h_diff])

          simp [h_sum_sc_ltm] at h_lt
          simp [U32.toInt]
          rw [if_neg (by rw [U32.negative_toInt]; simpa)]
          rw [if_neg (by rw [U32.negative_toInt]; simpa)]
          clear *- h_lt; simp [U32.toNat] at *; omega

        . simp at sgn_r
          rw [abs_of_nonneg sgn_c, abs_of_neg sgn_r]
          simp [h_c_sign, h_r_sign] at *
          simp [← h_xor_eq] at *

          have h_opp :
            -U32.toInt #v[BitVec.ofNat 8 ↑(air.core.r_0 row 0), BitVec.ofNat 8 ↑(air.core.r_1 row 0), BitVec.ofNat 8 ↑(air.core.r_2 row 0), BitVec.ofNat 8 ↑(air.core.r_3 row 0)] =
             U32.toInt #v[BitVec.ofNat 8 ↑(air.core.r_prime_0 row 0), BitVec.ofNat 8 ↑(air.core.r_prime_1 row 0), BitVec.ofNat 8 ↑(air.core.r_prime_2 row 0), BitVec.ofNat 8 ↑(air.core.r_prime_3 row 0)]
          := by
            clear *- b_lt_0 b_lt_1 b_lt_2 b_lt_3
                     h_lt_0 h_lt_1 h_lt_2 h_lt_3
                     ub_r0 ub_r1 ub_r2 ub_r3
                     ub_r'0 ub_r'1 ub_r'2 ub_r'3
                     h_nonono_r
            simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide]
            simp [← DivRemCoreAir_4_8.carry_lt_0_def,
                  ← DivRemCoreAir_4_8.carry_lt_1_def,
                  ← DivRemCoreAir_4_8.carry_lt_2_def,
                  ← DivRemCoreAir_4_8.carry_lt_3_def] at *
            rcases h_lt_0 with h0 | h0
            . simp_all
              by_cases hr3 : 128 ≤ (air.core.r_3 row 0).val
              . rw [if_pos (by omega)]
                rw [if_neg (by omega)]
                simp [U32.toNat]
                repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                omega
              . rw [if_neg (by omega)]
                rw [if_pos (by omega)]
                simp [U32.toNat]
                repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                omega
            . have hr0 : air.core.r_0 row 0 = 0 := by clear *- ub_r0 b_lt_0 h0; grind
              rcases h_lt_1 with h1 | h1
              . simp_all
                by_cases hr3 : 128 ≤ (air.core.r_3 row 0).val
                . rw [if_pos (by omega)]
                  rw [if_neg (by omega)]
                  simp [U32.toNat]
                  repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                  omega
                . rw [if_neg (by omega)]
                  rw [if_pos (by omega)]
                  simp [U32.toNat]
                  repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                  omega
              . have hr1 : air.core.r_1 row 0 = 0 := by clear *- ub_r1 b_lt_1 hr0 h0 h1; grind
                rcases h_lt_2 with h2 | h2
                . simp_all
                  by_cases hr3 : 128 ≤ (air.core.r_3 row 0).val
                  . rw [if_pos (by omega)]
                    rw [if_neg (by omega)]
                    simp [U32.toNat]
                    repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                    omega
                  . rw [if_neg (by omega)]
                    rw [if_pos (by omega)]
                    simp [U32.toNat]
                    repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                    omega
                . have hr2 : air.core.r_2 row 0 = 0 := by clear *- ub_r2 b_lt_2 hr0 hr1 h0 h1 h2; grind
                  rcases h_lt_3 with h3 | h3
                  . simp_all
                    by_cases hr3 : 128 ≤ (air.core.r_3 row 0).val
                    . rw [if_pos (by omega)]
                      by_cases hr'3 : 128 ≤ (air.core.r_prime_3 row 0).val
                      . rw [if_pos (by omega)]
                        simp [U32.toNat]
                        repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                        have : air.core.r_3 row 0 = 128 ∧ air.core.r_prime_3 row 0 = 128 := by omega
                        simp_all
                      . rw [if_neg (by omega)]
                        simp [U32.toNat]
                        repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                        omega
                    . rw [if_neg (by omega)]
                      rw [if_pos (by omega)]
                      simp [U32.toNat]
                      repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                      omega
                  . simp [U32.toNat]
                    repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                    simp_all
                    grind

          have h_lt :=
            @BabyBear.Circuits.less_than
              (air.core.r_prime_0 row 0) (air.core.r_prime_1 row 0) (air.core.r_prime_2 row 0) (air.core.r_prime_3 row 0)
              (air.core.c_0 row 0) (air.core.c_1 row 0) (air.core.c_2 row 0) (air.core.c_3 row 0)
              (air.core.lt_marker_0 row 0) (air.core.lt_marker_1 row 0) (air.core.lt_marker_2 row 0) (air.core.lt_marker_3 row 0)
              (air.core.lt_diff row 0)
              (air.core.r_prime_3 row 0) (air.core.c_3 row 0)
              0
              ((air.core.lt_marker_3 row 0) + (air.core.lt_marker_2 row 0) + (air.core.lt_marker_1 row 0) + (air.core.lt_marker_0 row 0))
              ub_r'0 ub_r'1 ub_r'2 ub_r'3
              ub_c0 ub_c1 ub_c2 ub_c3
              (by right; assumption)
              (by simp) (by simp)
              b_ltm_0 b_ltm_1 b_ltm_2 b_ltm_3
              (by right; assumption)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_3; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_2; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_1; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_0; grind)
              (by left; assumption)
              (by clear *- h_prod_3; grind)
              (by clear *- h_prod_2; grind)
              (by clear *- h_prod_1; grind)
              (by left; assumption)
              (by simpa) (by simpa)
              (by simp [h_diff])

          simp [h_sum_sc_ltm] at h_lt
          rw [h_opp]
          simp [U32.toInt]
          rw [if_neg (by rw [U32.negative_toInt]; clear *- sgn_r h_opp; omega)]
          rw [if_neg (by rw [U32.negative_toInt]; simpa)]
          clear *- h_lt; simp [U32.toNat] at *; omega

        . simp at sgn_c
          rw [abs_of_neg sgn_c, abs_of_nonneg sgn_r]
          simp [h_c_sign, h_r_sign] at *
          simp [← h_xor_eq] at *

          have h_opp :
            -U32.toInt #v[BitVec.ofNat 8 ↑(air.core.r_0 row 0), BitVec.ofNat 8 ↑(air.core.r_1 row 0), BitVec.ofNat 8 ↑(air.core.r_2 row 0), BitVec.ofNat 8 ↑(air.core.r_3 row 0)] =
             U32.toInt #v[BitVec.ofNat 8 ↑(air.core.r_prime_0 row 0), BitVec.ofNat 8 ↑(air.core.r_prime_1 row 0), BitVec.ofNat 8 ↑(air.core.r_prime_2 row 0), BitVec.ofNat 8 ↑(air.core.r_prime_3 row 0)]
          := by
            clear *- b_lt_0 b_lt_1 b_lt_2 b_lt_3
                     h_lt_0 h_lt_1 h_lt_2 h_lt_3
                     ub_r0 ub_r1 ub_r2 ub_r3
                     ub_r'0 ub_r'1 ub_r'2 ub_r'3
                     h_nonono_r
            simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide]
            simp [← DivRemCoreAir_4_8.carry_lt_0_def,
                  ← DivRemCoreAir_4_8.carry_lt_1_def,
                  ← DivRemCoreAir_4_8.carry_lt_2_def,
                  ← DivRemCoreAir_4_8.carry_lt_3_def] at *
            rcases h_lt_0 with h0 | h0
            . simp_all
              by_cases hr3 : 128 ≤ (air.core.r_3 row 0).val
              . rw [if_pos (by omega)]
                rw [if_neg (by omega)]
                simp [U32.toNat]
                repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                omega
              . rw [if_neg (by omega)]
                rw [if_pos (by omega)]
                simp [U32.toNat]
                repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                omega
            . have hr0 : air.core.r_0 row 0 = 0 := by clear *- ub_r0 b_lt_0 h0; grind
              rcases h_lt_1 with h1 | h1
              . simp_all
                by_cases hr3 : 128 ≤ (air.core.r_3 row 0).val
                . rw [if_pos (by omega)]
                  rw [if_neg (by omega)]
                  simp [U32.toNat]
                  repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                  omega
                . rw [if_neg (by omega)]
                  rw [if_pos (by omega)]
                  simp [U32.toNat]
                  repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                  omega
              . have hr1 : air.core.r_1 row 0 = 0 := by clear *- ub_r1 b_lt_1 hr0 h0 h1; grind
                rcases h_lt_2 with h2 | h2
                . simp_all
                  by_cases hr3 : 128 ≤ (air.core.r_3 row 0).val
                  . rw [if_pos (by omega)]
                    rw [if_neg (by omega)]
                    simp [U32.toNat]
                    repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                    omega
                  . rw [if_neg (by omega)]
                    rw [if_pos (by omega)]
                    simp [U32.toNat]
                    repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                    omega
                . have hr2 : air.core.r_2 row 0 = 0 := by clear *- ub_r2 b_lt_2 hr0 hr1 h0 h1 h2; grind
                  rcases h_lt_3 with h3 | h3
                  . simp_all
                    by_cases hr3 : 128 ≤ (air.core.r_3 row 0).val
                    . rw [if_pos (by omega)]
                      by_cases hr'3 : 128 ≤ (air.core.r_prime_3 row 0).val
                      . rw [if_pos (by omega)]
                        simp [U32.toNat]
                        repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                        have : air.core.r_3 row 0 = 128 ∧ air.core.r_prime_3 row 0 = 128 := by omega
                        simp_all
                      . rw [if_neg (by omega)]
                        simp [U32.toNat]
                        repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                        omega
                    . rw [if_neg (by omega)]
                      rw [if_pos (by omega)]
                      simp [U32.toNat]
                      repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                      omega
                  . simp [U32.toNat]
                    repeat rw [Int.emod_eq_of_lt (by omega) (by omega)]
                    simp_all
                    grind

          have h_lt :=
            @BabyBear.Circuits.less_than
              (air.core.c_0 row 0) (air.core.c_1 row 0) (air.core.c_2 row 0) (air.core.c_3 row 0)
              (air.core.r_prime_0 row 0) (air.core.r_prime_1 row 0) (air.core.r_prime_2 row 0) (air.core.r_prime_3 row 0)
              (air.core.lt_marker_0 row 0) (air.core.lt_marker_1 row 0) (air.core.lt_marker_2 row 0) (air.core.lt_marker_3 row 0)
              (air.core.lt_diff row 0)
              (air.core.c_3 row 0) (air.core.r_prime_3 row 0)
              0
              ((air.core.lt_marker_3 row 0) + (air.core.lt_marker_2 row 0) + (air.core.lt_marker_1 row 0) + (air.core.lt_marker_0 row 0))
              ub_c0 ub_c1 ub_c2 ub_c3
              ub_r'0 ub_r'1 ub_r'2 ub_r'3
              (by right; assumption)
              (by simp) (by simp)
              b_ltm_0 b_ltm_1 b_ltm_2 b_ltm_3
              (by right; assumption)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_3; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_2; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_1; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_0; grind)
              (by left; assumption)
              (by clear *- h_prod_3; grind)
              (by clear *- h_prod_2; grind)
              (by clear *- h_prod_1; grind)
              (by left; assumption)
              (by simpa) (by simpa)
              (by simp [h_diff])

          simp [h_sum_sc_ltm] at h_lt
          apply lt_neg_of_lt_neg
          rw [h_opp]
          simp [U32.toInt]
          rw [if_pos (by rw [U32.negative_toInt]; simpa)]
          rw [if_pos]
          . clear *- h_lt; simp [U32.toNat] at *; omega
          . rw [U32.negative_toInt]
            clear *- sgn_r h_opp aux_r_nzero ub_r0 ub_r1 ub_r2 ub_r3
            simp [← h_opp]
            by_contra hz; simp at hz
            have : U32.toInt #v[BitVec.ofNat 8 ↑(air.core.r_0 row 0), BitVec.ofNat 8 ↑(air.core.r_1 row 0), BitVec.ofNat 8 ↑(air.core.r_2 row 0), BitVec.ofNat 8 ↑(air.core.r_3 row 0)] = 0
              := by omega
            rw [BabyBear.toInt_0_inv ub_r0 ub_r1 ub_r2 ub_r3] at this
            simp_all; apply aux_r_nzero; clear *-
            simp [U32.toInt, U32.negative, U32.toNat]

        . simp at sgn_c sgn_r
          rw [abs_of_neg sgn_c, abs_of_neg sgn_r]
          simp [h_c_sign, h_r_sign] at *
          simp [← h_xor_eq] at *
          symm at h_r'_0 h_r'_1 h_r'_2 h_r'_3
          simp_all

          have h_lt :=
            @BabyBear.Circuits.less_than
              (air.core.c_0 row 0) (air.core.c_1 row 0) (air.core.c_2 row 0) (air.core.c_3 row 0)
              (air.core.r_0 row 0) (air.core.r_1 row 0) (air.core.r_2 row 0) (air.core.r_3 row 0)
              (air.core.lt_marker_0 row 0) (air.core.lt_marker_1 row 0) (air.core.lt_marker_2 row 0) (air.core.lt_marker_3 row 0)
              (air.core.lt_diff row 0)
              (air.core.c_3 row 0) (air.core.r_3 row 0)
              0
              ((air.core.lt_marker_3 row 0) + (air.core.lt_marker_2 row 0) + (air.core.lt_marker_1 row 0) + (air.core.lt_marker_0 row 0))
              ub_c0 ub_c1 ub_c2 ub_c3
              ub_r0 ub_r1 ub_r2 ub_r3
              (by right; assumption)
              (by simp) (by simp)
              b_ltm_0 b_ltm_1 b_ltm_2 b_ltm_3
              (by right; assumption)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_3; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_2; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_1; grind)
              (by simp [h_sum_sc_ltm]; clear *- h_diff_0; grind)
              (by left; assumption)
              (by clear *- h_prod_3; grind)
              (by clear *- h_prod_2; grind)
              (by clear *- h_prod_1; grind)
              (by left; assumption)
              (by simpa) (by simpa)
              (by simp [h_diff])

          simp [h_sum_sc_ltm] at h_lt
          simp [U32.toInt]
          rw [if_pos (by rw [U32.negative_toInt]; simpa)]
          rw [if_pos (by rw [U32.negative_toInt]; simpa)]
          clear *- h_lt; simp [U32.toNat] at *; omega

      simp [cond2]
      clear b_ltm_0 b_ltm_1 b_ltm_2 b_ltm_3
            h_prod_1 h_prod_2 h_prod_3
            h_diff_0 h_diff_1 h_diff_2 h_diff_3 h_diff
            h_lt_0 h_lt_1 h_lt_2 h_lt_3
            h_r'inv_0 h_r'inv_1 h_r'inv_2 h_r'inv_3
            b_lt_0 b_lt_1 b_lt_2 b_lt_3
            h_r'_0 h_r'_1 h_r'_2 h_r'_3

      apply Int.split_nzp (U32.toInt #v[BitVec.ofNat 8 ↑(air.core.r_0 row 0), BitVec.ofNat 8 ↑(air.core.r_1 row 0),
                                          BitVec.ofNat 8 ↑(air.core.r_2 row 0), BitVec.ofNat 8 ↑(air.core.r_3 row 0)]) <;> intro h_r_sgn
      . right
        simp [Int.sign_cases, h_r_sgn]
        intro hb; exfalso
        rw [← b_sign_is_bsgn] at r_sign_is_rsgn
        simp [U32.ext, U32.negative_toInt] at r_sign_is_rsgn
        clear *- h_r_sgn hb r_sign_is_rsgn
        simp_all
      . left; assumption
      . right
        simp [Int.sign_cases]
        rw [← b_sign_is_bsgn] at r_sign_is_rsgn
        simp [U32.ext, U32.negative_toInt] at r_sign_is_rsgn
        iterate 2 rw [if_neg (by clear *- h_r_sgn r_sign_is_rsgn; omega)]
        rw [if_neg (by clear *- h_r_sgn r_sign_is_rsgn; omega)] at r_sign_is_rsgn
        split_ifs at r_sign_is_rsgn with hb
        . simp [hb]; intro hzb
          rw [BabyBear.toInt_0_inv] at hzb <;> [ skip; assumption; assumption; assumption; assumption ]
          simp [hzb] at cond1
          conv at cond1 =>
            lhs; simp [U32.toInt, U32.negative, U32.toNat]
          have ⟨ lb_c, ub_c ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)]
          obtain ⟨ c, eq_c ⟩ : exists c, U32.toInt #v[BitVec.ofNat 8 (air.core.c_0 row 0), BitVec.ofNat 8 (air.core.c_1 row 0), BitVec.ofNat 8 (air.core.c_2 row 0), BitVec.ofNat 8 (air.core.c_3 row 0)] = c := by simp
          rw [eq_c] at cond1 cond2 lb_c ub_c
          have ⟨ lb_q, ub_q ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.q_0 row 0), BitVec.ofNat 8 (air.core.q_1 row 0), BitVec.ofNat 8 (air.core.q_2 row 0), BitVec.ofNat 8 (air.core.q_3 row 0)]
          obtain ⟨ q, eq_q ⟩ : exists q, U32.toInt #v[BitVec.ofNat 8 (air.core.q_0 row 0), BitVec.ofNat 8 (air.core.q_1 row 0), BitVec.ofNat 8 (air.core.q_2 row 0), BitVec.ofNat 8 (air.core.q_3 row 0)] = q := by simp
          rw [eq_q] at cond1 lb_q ub_q
          have ⟨ lb_r, ub_r ⟩ := U32.toInt_range #v[BitVec.ofNat 8 (air.core.r_0 row 0), BitVec.ofNat 8 (air.core.r_1 row 0), BitVec.ofNat 8 (air.core.r_2 row 0), BitVec.ofNat 8 (air.core.r_3 row 0)]
          obtain ⟨ r, eq_r ⟩ : exists r, U32.toInt #v[BitVec.ofNat 8 (air.core.r_0 row 0), BitVec.ofNat 8 (air.core.r_1 row 0), BitVec.ofNat 8 (air.core.r_2 row 0), BitVec.ofNat 8 (air.core.r_3 row 0)] = r := by simp
          rw [eq_r] at cond1 cond2 lb_r ub_r
          have h_c_nz : ¬ c = 0
          := by
            rw [← eq_c]; clear *- aux_c_nzero ub_c0 ub_c1 ub_c2 ub_c3
            intro hz; apply aux_c_nzero
            simp [U32.toInt, U32.negative, U32.toNat] at *
            split_ifs <;> simp_all
          have h_r_nz : ¬ r = 0
          := by
            rw [← eq_r]; clear *- aux_r_nzero ub_r0 ub_r1 ub_r2 ub_r3
            intro hz; apply aux_r_nzero
            simp [U32.toInt, U32.negative, U32.toNat] at *
            split_ifs <;> simp_all
          clear *- lb_c lb_q lb_r ub_c ub_q ub_r h_c_nz h_r_nz cond1 cond2
          (have eq_r : r = -(q * c) := by omega); subst r
          apply Int.split_nzp c <;> intro hc
          . rw [abs_of_neg hc] at cond2
            clear ub_c h_c_nz cond1
            apply Int.split_nzp q <;> intro hq
            . rw [abs_of_nonpos (by nlinarith)] at cond2
              nlinarith
            . simp_all
            . rw [abs_of_nonneg (by nlinarith)] at cond2
              nlinarith
          . apply h_c_nz; exact hc
          . rw [abs_of_pos hc] at cond2
            clear ub_c h_c_nz cond1
            apply Int.split_nzp q <;> intro hq
            . rw [abs_of_nonneg (by nlinarith)] at cond2
              nlinarith
            . simp_all
            . rw [abs_of_nonpos (by nlinarith)] at cond2
              nlinarith

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the DIV/REM opcode, gathered --/
theorem spec_DIVREM
  (h_divrem :
    (air.core.ctx row 0).instruction.opcode = 596 ∨
    (air.core.ctx row 0).instruction.opcode = 598)
:
  (U32.toBV #v[(air.core.q_0 row 0).val,
               (air.core.q_1 row 0).val,
               (air.core.q_2 row 0).val,
               (air.core.q_3 row 0).val],
   U32.toBV #v[(air.core.r_0 row 0).val,
               (air.core.r_1 row 0).val,
               (air.core.r_2 row 0).val,
               (air.core.r_3 row 0).val])
    =
  (execute_DIV_REM_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .DRS)
:= by
  by_cases h_c_zero : air.core.zero_divisor row 0 = 1
  . apply spec_DIVREM_czero <;> assumption
  . have : air.core.zero_divisor row 0 = 0 := by
      rw [allHold_simplified_of_allHold] at constraints
      simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
      obtain ⟨ constrain_interactions,
              b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
              b_zd, rest ⟩ := constraints
      clear *- b_zd h_c_zero
      simp_all
    by_cases h_scase :
      (U32.toInt
        #v[BitVec.ofNat 8 ↑(air.core.b_0 row 0), BitVec.ofNat 8 ↑(air.core.b_1 row 0),
           BitVec.ofNat 8 ↑(air.core.b_2 row 0), BitVec.ofNat 8 ↑(air.core.b_3 row 0)] = -2147483648 ∧
       U32.toInt
        #v[BitVec.ofNat 8 ↑(air.core.c_0 row 0), BitVec.ofNat 8 ↑(air.core.c_1 row 0),
           BitVec.ofNat 8 ↑(air.core.c_2 row 0), BitVec.ofNat 8 ↑(air.core.c_3 row 0)] = -1)
    . apply spec_DIVREM_nczero_sc <;> assumption
    . by_cases h_r_zero : air.core.r_zero row 0 = 1
      . apply spec_DIVREM_nczero_nsc_rzero <;> assumption
      . apply spec_DIVREM_nczero_nsc_nrzero <;> try assumption
        rw [allHold_simplified_of_allHold] at constraints
        simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
        obtain ⟨ constrain_interactions,
                b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
                b_zd, h_zd_c0, h_zd_q0, h_zd_c1, h_zd_q1, h_zd_c2, h_zd_q2, h_zd_c3, h_zd_q3,
                b_vnzd, h_vnzd,
                b_rz, rest ⟩ := constraints
        clear *- b_rz h_r_zero
        simp_all

end signed

section unsigned

attribute [-simp]
  BabyBear.to_the_right_FBB_0
  BabyBear.to_the_right_FBB_1
  BabyBear.to_the_right_FBB_255
  to_the_right_nat_0
  to_the_right_nat_1
  to_the_right_nat_255
  to_the_right_nat_256
  not_and

set_option maxRecDepth 1_000_000 in
include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the DIVU/REMU opcode, Part 1 --/
theorem spec_DIVUREMU_czero
  (h_divuremu :
    (air.core.ctx row 0).instruction.opcode = 597 ∨
    (air.core.ctx row 0).instruction.opcode = 599)
  (h_c_zero : air.core.zero_divisor row 0 = 1)
:
  (U32.toBV #v[(air.core.q_0 row 0).val,
               (air.core.q_1 row 0).val,
               (air.core.q_2 row 0).val,
               (air.core.q_3 row 0).val],
   U32.toBV #v[(air.core.r_0 row 0).val,
               (air.core.r_1 row 0).val,
               (air.core.r_2 row 0).val,
               (air.core.r_3 row 0).val])
    =
  (execute_DIV_REM_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .DRU)
:= by
  obtain ⟨ sop0, sop1, sop2, sop3 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2, op3 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  have ⟨ op_sum, op_div, op_rem ⟩ :
    (air.core.opcode_divu_flag row 0 + air.core.opcode_remu_flag row 0 = 1) ∧
    air.core.opcode_div_flag row 0 = 0 ∧
    air.core.opcode_rem_flag row 0 = 0
    := by grind

  clear h_divuremu sop0 sop1 sop2 sop3 op0 op1 op2 op3

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_divrem_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ub_q0, ub_cq0, ub_q1, ub_cq1, ub_q2, ub_cq2, ub_q3, ub_cq3,
           ub_r0, ub_cr0, ub_r1, ub_cr1, ub_r2, ub_cr2, ub_r3, ub_cr3 ⟩ := pa_rtc
  obtain ⟨ h_signed_msb, h_diff ⟩ := pa_bit
  clear pa_range pa_read

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
           b_zd, h_zd_c0, h_zd_q0, h_zd_c1, h_zd_q1, h_zd_c2, h_zd_q2, h_zd_c3, h_zd_q3,
           b_vnzd, h_vnzd,
           b_rz, b_rz_r0, b_rz_r1, b_rz_r2, b_rz_r3,
           b_vnsc, h_vnsc,
           b_bsgn, b_csgn, h_bsgn, h_csgn, h_xor_eq,
           b_qsgn, h_xor_qsgn_eq, h_xor_qsgn_z,
           h_r'_0, b_lt_0, h_r'inv_0, h_lt_0,
           h_r'_1, b_lt_1, h_r'inv_1, h_lt_1,
           h_r'_2, b_lt_2, h_r'inv_2, h_lt_2,
           h_r'_3, b_lt_3, h_r'inv_3, h_lt_3,
           b_ltm_3, h_prod_3, h_diff_3,
           b_ltm_2, h_prod_2, h_diff_2,
           b_ltm_1, h_prod_1, h_diff_1,
           b_ltm_0, h_prod_0, h_diff_0,
           h_sum_sc_ltm,
           rest ⟩ := constraints
  clear constrain_interactions rest

  have eq_sgn : air.core.signed row 0 = 0
    := by simp [← DivRemCoreAir_4_8.signed_def, op_div, op_rem]
  symm at h_xor_eq
  simp_all
  symm at h_r'_0 h_r'_1 h_r'_2 h_r'_3
  simp_all
  clear h_r'_0 h_r'_1 h_r'_2 h_r'_3

  clear b_vnzd
  simp [← DivRemCoreAir_4_8.valid_and_not_zero_divisor_def] at h_vnzd
  simp [row_valid] at h_vnzd

  have eq_zero_divisor :
    air.core.zero_divisor row 0 = 1 ↔
      air.core.c_0 row 0 = 0 ∧ air.core.c_1 row 0 = 0 ∧ air.core.c_2 row 0 = 0 ∧ air.core.c_3 row 0 = 0
  := by
    constructor
    . intro h_div; simp_all
    . intro ⟨ z_c0, z_c1, z_c2, z_c3 ⟩
      clear *- h_vnzd z_c0 z_c1 z_c2 z_c3
      simp [← DivRemCoreAir_4_8.c_sum_def] at h_vnzd
      grind

  simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
  rw [if_pos (by simp [U32.toNat])]
  split_ands
  . simp [← BitVec.toNat_inj, U32.toNat]
  . rw [← Int.ofNat_tmod, Int.toNat_natCast]
    simp [← BitVec.toNat_inj, U32.toNat]
    repeat rw [Nat.mod_eq_of_lt (by omega)]
    simp [← DivRemCoreAir_4_8.carry_0,
          ← DivRemCoreAir_4_8.carry_1,
          ← DivRemCoreAir_4_8.carry_2,
          ← DivRemCoreAir_4_8.carry_3] at *
    repeat rw [mul_comm (b := 2005401601)] at *
    simp_all
    have : air.core.r_0 row 0 = air.core.b_0 row 0
    := by
      have ⟨ h_eq, _ ⟩ :=
        @BabyBear.inv256_prod_diff_div_mod (air.core.b_0 row 0) (air.core.r_0 row 0) ub_b0 (by omega)
      clear *- ub_r0 h_eq
      simp_all [Fin.ext_iff]; omega
    simp_all
    have : air.core.r_1 row 0 = air.core.b_1 row 0
    := by
      have ⟨ h_eq, _ ⟩ :=
        @BabyBear.inv256_prod_diff_div_mod (air.core.b_1 row 0) (air.core.r_1 row 0) ub_b1 (by omega)
      clear *- ub_r1 h_eq
      simp_all [Fin.ext_iff]; omega
    simp_all
    have : air.core.r_2 row 0 = air.core.b_2 row 0
    := by
      have ⟨ h_eq, _ ⟩ :=
        @BabyBear.inv256_prod_diff_div_mod (air.core.b_2 row 0) (air.core.r_2 row 0) ub_b2 (by omega)
      clear *- ub_r2 h_eq
      simp_all [Fin.ext_iff]; omega
    simp_all
    have : air.core.r_3 row 0 = air.core.b_3 row 0
    := by
      have ⟨ h_eq, _ ⟩ :=
        @BabyBear.inv256_prod_diff_div_mod (air.core.b_3 row 0) (air.core.r_3 row 0) ub_b3 (by omega)
      clear *- ub_r3 h_eq
      simp_all [Fin.ext_iff]; omega
    simp_all

set_option maxRecDepth 1_000_000 in
include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the DIVU/REMU opcode, Part 2 --/
theorem spec_DIVUREMU_nczero_rzero
  (h_divuremu :
    (air.core.ctx row 0).instruction.opcode = 597 ∨
    (air.core.ctx row 0).instruction.opcode = 599)
  (h_c_zero : air.core.zero_divisor row 0 = 0)
  (h_r_zero : air.core.r_zero row 0 = 1)
:
  (U32.toBV #v[(air.core.q_0 row 0).val,
               (air.core.q_1 row 0).val,
               (air.core.q_2 row 0).val,
               (air.core.q_3 row 0).val],
   U32.toBV #v[(air.core.r_0 row 0).val,
               (air.core.r_1 row 0).val,
               (air.core.r_2 row 0).val,
               (air.core.r_3 row 0).val])
    =
  (execute_DIV_REM_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .DRU)
:= by
  obtain ⟨ sop0, sop1, sop2, sop3 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2, op3 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  have ⟨ op_sum, op_div, op_rem ⟩ :
    (air.core.opcode_divu_flag row 0 + air.core.opcode_remu_flag row 0 = 1) ∧
    air.core.opcode_div_flag row 0 = 0 ∧
    air.core.opcode_rem_flag row 0 = 0
    := by grind

  clear h_divuremu sop0 sop1 sop2 sop3 op0 op1 op2 op3

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_divrem_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ub_q0, ub_cq0, ub_q1, ub_cq1, ub_q2, ub_cq2, ub_q3, ub_cq3,
           ub_r0, ub_cr0, ub_r1, ub_cr1, ub_r2, ub_cr2, ub_r3, ub_cr3 ⟩ := pa_rtc
  obtain ⟨ h_signed_msb, h_diff ⟩ := pa_bit
  clear pa_range pa_read

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
           b_zd, h_zd_c0, h_zd_q0, h_zd_c1, h_zd_q1, h_zd_c2, h_zd_q2, h_zd_c3, h_zd_q3,
           b_vnzd, h_vnzd,
           b_rz, b_rz_r0, b_rz_r1, b_rz_r2, b_rz_r3,
           b_vnsc, h_vnsc,
           b_bsgn, b_csgn, h_bsgn, h_csgn, h_xor_eq,
           b_qsgn, h_xor_qsgn_eq, h_xor_qsgn_z,
           h_r'_0, b_lt_0, h_r'inv_0, h_lt_0,
           h_r'_1, b_lt_1, h_r'inv_1, h_lt_1,
           h_r'_2, b_lt_2, h_r'inv_2, h_lt_2,
           h_r'_3, b_lt_3, h_r'inv_3, h_lt_3,
           b_ltm_3, h_prod_3, h_diff_3,
           b_ltm_2, h_prod_2, h_diff_2,
           b_ltm_1, h_prod_1, h_diff_1,
           b_ltm_0, h_prod_0, h_diff_0,
           h_sum_sc_ltm,
           rest ⟩ := constraints
  clear constrain_interactions rest

  simp [← DivRemCoreAir_4_8.carry_0,
        ← DivRemCoreAir_4_8.carry_1,
        ← DivRemCoreAir_4_8.carry_2,
        ← DivRemCoreAir_4_8.carry_3,
        ← DivRemCoreAir_4_8.carry_ext_0_def,
        ← DivRemCoreAir_4_8.carry_ext_1_def,
        ← DivRemCoreAir_4_8.carry_ext_2_def,
        ← DivRemCoreAir_4_8.carry_ext_3_def,
        ← DivRemCoreAir_4_8.b_ext_def,
        ← DivRemCoreAir_4_8.c_ext_def,
        ← DivRemCoreAir_4_8.q_ext_def
        ] at *
  repeat rw [mul_comm (b := 2005401601)] at *

  have eq_sgn : air.core.signed row 0 = 0
    := by simp [← DivRemCoreAir_4_8.signed_def, op_div, op_rem]
  simp [eq_sgn] at *
  symm at h_xor_eq
  simp_all
  symm at h_r'_0; simp [h_r'_0] at *
  symm at h_r'_1 h_r'_2 h_r'_3
  simp_all

  clear b_vnzd
  simp [← DivRemCoreAir_4_8.valid_and_not_zero_divisor_def] at h_vnzd
  simp [row_valid] at h_vnzd

  have eq_zero_divisor :
    air.core.zero_divisor row 0 = 1 ↔
      air.core.c_0 row 0 = 0 ∧ air.core.c_1 row 0 = 0 ∧ air.core.c_2 row 0 = 0 ∧ air.core.c_3 row 0 = 0
  := by
    constructor
    . intro h_div; simp_all
    . intro ⟨ z_c0, z_c1, z_c2, z_c3 ⟩
      clear *- h_vnzd z_c0 z_c1 z_c2 z_c3
      simp [← DivRemCoreAir_4_8.c_sum_def] at h_vnzd
      grind
  simp [h_c_zero] at eq_zero_divisor

  have h_bv_eq :=
    @divrem_split
      (air.core.b_0 row 0) (air.core.b_1 row 0) (air.core.b_2 row 0) (air.core.b_3 row 0) 0 0 0 0
      (air.core.c_0 row 0) (air.core.c_1 row 0) (air.core.c_2 row 0) (air.core.c_3 row 0)
      (air.core.q_0 row 0) (air.core.q_1 row 0) (air.core.q_2 row 0) (air.core.q_3 row 0)
      0 0 0 0
      0 0 0
      ub_b0 ub_b1 ub_b2 ub_b3 (by simp) (by simp) (by simp) (by simp)
      ub_c0 ub_c1 ub_c2 ub_c3 ub_q0 ub_q1 ub_q2 ub_q3
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp)
      (by clear *- ub_cq0; simp; assumption)
      (by clear *- ub_cq1; simp; assumption)
      (by clear *- ub_cq2; simp; assumption)
      (by clear *- ub_cq3; simp; assumption)
      (by clear *- ub_cr0; simp; assumption)
      (by clear *- ub_cr1; simp; assumption)
      (by clear *- ub_cr2; simp; assumption)
      (by clear *- ub_cr3; simp; assumption)
  clear ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cr0 ub_cr1 ub_cr2 ub_cr3

  simp [← BitVec.toNat_inj, U64.toNat] at h_bv_eq
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at h_bv_eq
  rw [Nat.mod_eq_of_lt] at h_bv_eq
  rotate_left
  . apply lt_of_le_of_lt (b := 4294967295 * 4294967295)
    . apply mul_le_mul <;> omega
    . simp
  . simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
    rw [if_neg (by simp [U32.toNat]; clear *- ub_c0 ub_c1 ub_c2 ub_c3 eq_zero_divisor h_c_zero; grind)]
    rw [← Int.ofNat_tmod, ← Int.ofNat_tdiv, Int.toNat_natCast, Int.toNat_natCast]
    simp [← BitVec.toNat_inj, U32.toNat]
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
    rw [Nat.mod_eq_of_lt (b := 4294967296)]
    rw [Nat.mod_eq_of_lt (b := 4294967296)]
    simp [h_bv_eq]
    clear *- ub_c0 ub_c1 ub_c2 ub_c3 ub_q0 ub_q1 ub_q2 ub_q3 eq_zero_divisor
    . rw [Nat.mul_div_cancel_left]
      omega
    . trans (((air.core.c_0 row 0) : ℕ) + ↑(air.core.c_1 row 0) * 256 + ↑(air.core.c_2 row 0) * 65536 + ↑(air.core.c_3 row 0) * 16777216)
      . apply Nat.mod_lt
        clear *- ub_c0 ub_c1 ub_c2 ub_c3 eq_zero_divisor
        omega
      . omega
    . apply lt_of_le_of_lt
      . apply Nat.div_le_self
      . omega

set_option maxRecDepth 1_000_000 in
include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the DIV/REM opcode, Part 3 --/
theorem spec_DIVUREMU_nczero_nrzero
  (h_divuremu :
    (air.core.ctx row 0).instruction.opcode = 597 ∨
    (air.core.ctx row 0).instruction.opcode = 599)
  (h_c_zero : air.core.zero_divisor row 0 = 0)
  (h_r_zero : air.core.r_zero row 0 = 0)
:
  (U32.toBV #v[(air.core.q_0 row 0).val,
               (air.core.q_1 row 0).val,
               (air.core.q_2 row 0).val,
               (air.core.q_3 row 0).val],
   U32.toBV #v[(air.core.r_0 row 0).val,
               (air.core.r_1 row 0).val,
               (air.core.r_2 row 0).val,
               (air.core.r_3 row 0).val])
    =
  (execute_DIV_REM_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .DRU)
:= by
  obtain ⟨ sop0, sop1, sop2, sop3 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2, op3 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  have ⟨ op_sum, op_div, op_rem ⟩ :
    (air.core.opcode_divu_flag row 0 + air.core.opcode_remu_flag row 0 = 1) ∧
    air.core.opcode_div_flag row 0 = 0 ∧
    air.core.opcode_rem_flag row 0 = 0
    := by grind

  clear h_divuremu sop0 sop1 sop2 sop3 op0 op1 op2 op3

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_divrem_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ub_q0, ub_cq0, ub_q1, ub_cq1, ub_q2, ub_cq2, ub_q3, ub_cq3,
           ub_r0, ub_cr0, ub_r1, ub_cr1, ub_r2, ub_cr2, ub_r3, ub_cr3 ⟩ := pa_rtc
  obtain ⟨ h_signed_msb, h_diff ⟩ := pa_bit
  clear pa_range pa_read

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
           b_zd, h_zd_c0, h_zd_q0, h_zd_c1, h_zd_q1, h_zd_c2, h_zd_q2, h_zd_c3, h_zd_q3,
           b_vnzd, h_vnzd,
           b_rz, b_rz_r0, b_rz_r1, b_rz_r2, b_rz_r3,
           b_vnsc, h_vnsc,
           b_bsgn, b_csgn, h_bsgn, h_csgn, h_xor_eq,
           b_qsgn, h_xor_qsgn_eq, h_xor_qsgn_z,
           h_r'_0, b_lt_0, h_r'inv_0, h_lt_0,
           h_r'_1, b_lt_1, h_r'inv_1, h_lt_1,
           h_r'_2, b_lt_2, h_r'inv_2, h_lt_2,
           h_r'_3, b_lt_3, h_r'inv_3, h_lt_3,
           b_ltm_3, h_prod_3, h_diff_3,
           b_ltm_2, h_prod_2, h_diff_2,
           b_ltm_1, h_prod_1, h_diff_1,
           b_ltm_0, h_prod_0, h_diff_0,
           h_sum_sc_ltm,
           rest ⟩ := constraints
  clear constrain_interactions rest

  simp [← DivRemCoreAir_4_8.carry_0,
        ← DivRemCoreAir_4_8.carry_1,
        ← DivRemCoreAir_4_8.carry_2,
        ← DivRemCoreAir_4_8.carry_3,
        ← DivRemCoreAir_4_8.carry_ext_0_def,
        ← DivRemCoreAir_4_8.carry_ext_1_def,
        ← DivRemCoreAir_4_8.carry_ext_2_def,
        ← DivRemCoreAir_4_8.carry_ext_3_def,
        ← DivRemCoreAir_4_8.b_ext_def,
        ← DivRemCoreAir_4_8.c_ext_def,
        ← DivRemCoreAir_4_8.q_ext_def
        ] at *
  repeat rw [mul_comm (b := 2005401601)] at *

  have eq_sgn : air.core.signed row 0 = 0
    := by simp [← DivRemCoreAir_4_8.signed_def, op_div, op_rem]
  simp [eq_sgn] at *
  symm at h_xor_eq
  simp_all
  symm at h_r'_0; simp [h_r'_0] at *
  symm at h_r'_1 h_r'_2 h_r'_3
  simp_all

  clear b_vnzd
  simp [← DivRemCoreAir_4_8.valid_and_not_zero_divisor_def] at h_vnzd
  simp [row_valid] at h_vnzd

  have eq_zero_divisor :
    air.core.zero_divisor row 0 = 1 ↔
      air.core.c_0 row 0 = 0 ∧ air.core.c_1 row 0 = 0 ∧ air.core.c_2 row 0 = 0 ∧ air.core.c_3 row 0 = 0
  := by
    constructor
    . intro h_div; simp_all
    . intro ⟨ z_c0, z_c1, z_c2, z_c3 ⟩
      clear *- h_vnzd z_c0 z_c1 z_c2 z_c3
      simp [← DivRemCoreAir_4_8.c_sum_def] at h_vnzd
      grind
  simp [h_c_zero] at eq_zero_divisor

  have h_bv_eq :=
    @divrem_split
      (air.core.b_0 row 0) (air.core.b_1 row 0) (air.core.b_2 row 0) (air.core.b_3 row 0) 0 0 0 0
      (air.core.c_0 row 0) (air.core.c_1 row 0) (air.core.c_2 row 0) (air.core.c_3 row 0)
      (air.core.q_0 row 0) (air.core.q_1 row 0) (air.core.q_2 row 0) (air.core.q_3 row 0)
      (air.core.r_0 row 0) (air.core.r_1 row 0) (air.core.r_2 row 0) (air.core.r_3 row 0)
      0 0 0
      ub_b0 ub_b1 ub_b2 ub_b3 (by simp) (by simp) (by simp) (by simp)
      ub_c0 ub_c1 ub_c2 ub_c3 ub_q0 ub_q1 ub_q2 ub_q3 ub_r0 ub_r1 ub_r2 ub_r3
      (by simp) (by simp) (by simp)
      ub_cq0 ub_cq1 ub_cq2 ub_cq3
      (by clear *- ub_cr0; simp; assumption)
      (by clear *- ub_cr1; simp; assumption)
      (by clear *- ub_cr2; simp; assumption)
      (by clear *- ub_cr3; simp; assumption)
  clear ub_cq0 ub_cq1 ub_cq2 ub_cq3 ub_cr0 ub_cr1 ub_cr2 ub_cr3

  simp [← BitVec.toNat_inj, U64.toNat] at h_bv_eq
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at h_bv_eq
  rw [Nat.mod_eq_of_lt] at h_bv_eq
  rotate_left
  . apply lt_of_le_of_lt (b := 4294967295 * 4294967295 + 4294967295)
    . apply add_le_add
      . apply mul_le_mul <;> omega
      . omega
    . simp

  simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int]
  rw [if_neg (by simp [U32.toNat]; clear *- ub_c0 ub_c1 ub_c2 ub_c3 eq_zero_divisor h_c_zero; grind)]
  rw [← Int.ofNat_tmod, ← Int.ofNat_tdiv, Int.toNat_natCast, Int.toNat_natCast]
  simp [← BitVec.toNat_inj, U32.toNat]
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
  rw [Nat.mod_eq_of_lt (b := 4294967296)]
  rw [Nat.mod_eq_of_lt (b := 4294967296)]
  . rw [eq_comm, eq_comm (b := _ % _)]
    rw [Nat.div_mod_unique (by omega)]
    split_ands
    . omega
    . rw [← DivRemCoreAir_4_8.valid_and_not_special_case_def,
          ← DivRemCoreAir_4_8.special_case_def] at *
      simp_all

      have h_lt :=
        @BabyBear.Circuits.less_than
          (air.core.r_0 row 0) (air.core.r_1 row 0) (air.core.r_2 row 0) (air.core.r_3 row 0)
          (air.core.c_0 row 0) (air.core.c_1 row 0) (air.core.c_2 row 0) (air.core.c_3 row 0)
          (air.core.lt_marker_0 row 0) (air.core.lt_marker_1 row 0) (air.core.lt_marker_2 row 0) (air.core.lt_marker_3 row 0)
          (air.core.lt_diff row 0)
          (air.core.r_3 row 0) (air.core.c_3 row 0)
          0
          ((air.core.lt_marker_3 row 0) + (air.core.lt_marker_2 row 0) + (air.core.lt_marker_1 row 0) + (air.core.lt_marker_0 row 0))
          ub_r0 ub_r1 ub_r2 ub_r3
          ub_c0 ub_c1 ub_c2 ub_c3
          (by right; assumption)
          (by simp) (by simp)
          b_ltm_0 b_ltm_1 b_ltm_2 b_ltm_3
          (by right; assumption)
          (by simp [h_sum_sc_ltm]; clear *- h_diff_3; grind)
          (by simp [h_sum_sc_ltm]; clear *- h_diff_2; grind)
          (by simp [h_sum_sc_ltm]; clear *- h_diff_1; grind)
          (by simp [h_sum_sc_ltm]; clear *- h_diff_0; grind)
          (by left; assumption)
          (by clear *- h_prod_3; grind)
          (by clear *- h_prod_2; grind)
          (by clear *- h_prod_1; grind)
          (by left; assumption)
          (by simpa) (by simpa)
          (by simp [h_diff])
      simp_all

      simp [U32.toNat] at h_lt
      omega
  . trans (((air.core.c_0 row 0) : ℕ) + ↑(air.core.c_1 row 0) * 256 + ↑(air.core.c_2 row 0) * 65536 + ↑(air.core.c_3 row 0) * 16777216)
    . apply Nat.mod_lt
      clear *- ub_c0 ub_c1 ub_c2 ub_c3 eq_zero_divisor
      omega
    . omega
  . apply lt_of_le_of_lt
    . apply Nat.div_le_self
    . omega

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the DIV/REM opcode, gathered --/
theorem spec_DIVUREMU
  (h_divrem :
    (air.core.ctx row 0).instruction.opcode = 597 ∨
    (air.core.ctx row 0).instruction.opcode = 599)
:
  (U32.toBV #v[(air.core.q_0 row 0).val,
               (air.core.q_1 row 0).val,
               (air.core.q_2 row 0).val,
               (air.core.q_3 row 0).val],
   U32.toBV #v[(air.core.r_0 row 0).val,
               (air.core.r_1 row 0).val,
               (air.core.r_2 row 0).val,
               (air.core.r_3 row 0).val])
    =
  (execute_DIV_REM_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    .DRU)
:= by
  by_cases h_c_zero : air.core.zero_divisor row 0 = 1
  . apply spec_DIVUREMU_czero <;> assumption
  . have : air.core.zero_divisor row 0 = 0 := by
      rw [allHold_simplified_of_allHold] at constraints
      simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
      obtain ⟨ constrain_interactions,
              b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
              b_zd, rest ⟩ := constraints
      clear *- b_zd h_c_zero
      simp_all
    . by_cases h_r_zero : air.core.r_zero row 0 = 1
      . apply spec_DIVUREMU_nczero_rzero <;> assumption
      . apply spec_DIVUREMU_nczero_nrzero <;> try assumption
        rw [allHold_simplified_of_allHold] at constraints
        simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at constraints
        obtain ⟨ constrain_interactions,
                b_div, b_divu, b_rem, b_remu, b_valid, b_sc,
                b_zd, h_zd_c0, h_zd_q0, h_zd_c1, h_zd_q1, h_zd_c2, h_zd_q2, h_zd_c3, h_zd_q3,
                b_vnzd, h_vnzd,
                b_rz, rest ⟩ := constraints
        clear *- b_rz h_r_zero
        simp_all

end unsigned

end General

end DivRem.ValidRows
