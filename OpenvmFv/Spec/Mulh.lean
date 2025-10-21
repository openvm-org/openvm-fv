import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_mulh
import OpenvmFv.Constraints.VmAirWrapper_mulh
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000
set_option synthInstance.maxHeartbeats 1_000_000

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_mulh FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_mulh.constraints.allHold air row row_in_range)

namespace Mulh.NonValidRows

open VmAirWrapper_mulh.constraints

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
  air.core.a_mul_0 row 0 = 0 ∧
  air.core.a_mul_1 row 0 = 0 ∧
  air.core.a_mul_2 row 0 = 0 ∧
  air.core.a_mul_3 row 0 = 0 ∧
  air.core.b_ext row 0 = 0 ∧
  air.core.c_ext row 0 = 0 ∧
  air.core.opcode_mulh_flag row 0 = 0 ∧
  air.core.opcode_mulhsu_flag row 0 = 0 ∧
  air.core.opcode_mulhu_flag row 0 = 0
    → air.core.is_valid row 0 = 0 ∧
      allHold air row row_in_range
:= by
  rw [allHold_simplified_of_allHold]
  intro h_zeros
  simp [VmAirWrapper_mulh_constraint_and_interaction_simplification,
        Valid_MulHCoreAir_4_8.is_valid,
        ← MulHCoreAir_4_8.b_sign_def,
        ← MulHCoreAir_4_8.c_sign_def]
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
          readInstructionBus_row air row ++
          rangeTupleCheckerBus_row air row ++
          bitwiseBus_row air row → entry.1 = 0
:= by
  obtain ⟨ hint, constraints ⟩ := constraints
  clear hint; unfold extracted_row_constraint_list at constraints
  simp only [VmAirWrapper_mulh_air_simplification,
             VmAirWrapper_mulh_constraint_and_interaction_simplification] at constraints
  simp at constraints
  simp_all [Valid_MulHCoreAir_4_8.is_valid,
            VmAirWrapper_mulh_constraint_and_interaction_simplification]
  grind (splits := 28)

end Mulh.NonValidRows

open VmAirWrapper_mulh.constraints

namespace Mulh.ValidRows

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
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_mulh_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2 ⟩ := pa_read
  obtain ⟨ ub_am0, ub_cm0, ub_am1, ub_cm1, ub_am2, ub_cm2, ub_am3, ub_cm3,
           ub_a0, ub_cry0, ub_a1, ub_cry1, ub_a2, ub_cry2, ub_a3, ub_cry3 ⟩ := pa_rtc
  clear pa_range pa_bit

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_mulh_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_mulh, b_mulhsu, rest ⟩ := constraints
  clear constrain_interactions
  simp_all [VmAirWrapper_mulh_constraint_and_interaction_simplification,
            wf_propertiesToAssertPerRow,
            propertiesToAssert]
  clear *- b_mulh b_mulhsu
  grind

/-- From Mulh opcode to RISC-V opcode -/
def rop_of_Mulh_opcode (opcode : FBB) : mop :=
  if opcode = 593 then .MULH else
  if opcode = 594 then .MULHSU else
  if opcode = 595 then .MULHU else .MULHUS

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the MULH opcode --/
theorem spec_MULH
  (h_mulh : (air.core.ctx row 0).instruction.opcode = 593)
:
  (U32.toBV #v[(air.core.a_0 row 0).val,
               (air.core.a_1 row 0).val,
               (air.core.a_2 row 0).val,
               (air.core.a_3 row 0).val])
    =
  execute_MUL_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    (rop_of_Mulh_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  obtain ⟨ sop0, sop1, sop2 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_mulh_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2 ⟩ := pa_read
  obtain ⟨ ub_a0, ub_cm0, ub_a1, ub_cm1, ub_a2, ub_cm2, ub_a3, ub_cm3,
           ub_a4, ub_cry0, ub_a5, ub_cry1, ub_a6, ub_cry2, ub_a7, ub_cry3 ⟩ := pa_rtc
  clear pa_exec pa_range

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_mulh_constraint_and_interaction_simplification] at constraints

  obtain ⟨ hint, b_mulh, b_mulhsu, b_mulhu, b_is_valid, b_b_sign, b_c_sign, mulh_b_sign, mulu_c_sign, rest ⟩ := constraints
  clear hint rest

  simp_all [← MulHCoreAir_4_8.b_sign_def,
            ← MulHCoreAir_4_8.c_sign_def,
            ← MulHCoreAir_4_8.carry_mul_0,
            ← MulHCoreAir_4_8.carry_mul_1,
            ← MulHCoreAir_4_8.carry_mul_2,
            ← MulHCoreAir_4_8.carry_mul_3]

  simp [execute_MUL_pure, rop_of_Mulh_opcode, ← U32.extend_BitVec_extend, U32.extend]
  simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
  simp [@Nat.mod_eq_of_lt (air.core.b_3 row 0).val 256 (by omega)]
  simp [@Nat.mod_eq_of_lt (air.core.c_3 row 0).val 256 (by omega)]

  set a4 := air.core.a_0 row 0; set a5 := air.core.a_1 row 0; set a6 := air.core.a_2 row 0; set a7 := air.core.a_3 row 0
  set b0 := air.core.b_0 row 0; set b1 := air.core.b_1 row 0; set b2 := air.core.b_2 row 0; set b3 := air.core.b_3 row 0
  set c0 := air.core.c_0 row 0; set c1 := air.core.c_1 row 0; set c2 := air.core.c_2 row 0; set c3 := air.core.c_3 row 0
  set a0 := air.core.a_mul_0 row 0; set a1 := air.core.a_mul_1 row 0; set a2 := air.core.a_mul_2 row 0; set a3 := air.core.a_mul_3 row
  set b_ext := air.core.b_ext row 0; set c_ext := air.core.c_ext row 0

  obtain ⟨ msb_b, msb_c ⟩ := pa_bit
  have h_msb_b :
    b_ext = if 128 ≤ (air.core.b_3 row 0).val then 255 else 0
    := by
      clear *- ub_b3 b_b_sign msb_b
      split_ifs <;> grind
  have h_msb_c :
    c_ext = if 128 ≤ (air.core.c_3 row 0).val then 255 else 0
    := by
      clear *- ub_c3 b_c_sign msb_c
      split_ifs <;> grind
  clear msb_b msb_c

  have msb_b_val : (if 128 ≤ (air.core.b_3 row 0).val then 255 else 0) = b_ext.val
    := by rw [h_msb_b]; clear *-; split_ifs <;> simp
  simp [msb_b_val]
  have msb_c_val : (if 128 ≤ (air.core.c_3 row 0).val then 255 else 0) = c_ext.val
    := by rw [h_msb_c]; clear *-; split_ifs <;> simp
  simp [msb_c_val]

  have ub_cry4 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry0; simp]
  have ub_cry5 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry1; simp]
  have ub_cry6 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry2; simp]
  have ub_cry7 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry3; simp]
  clear ub_cry0 ub_cry1 ub_cry2 ub_cry3
  have ub_cry0 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm0; simp]
  have ub_cry1 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm1; simp]
  have ub_cry2 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm2; simp]
  have ub_cry3 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm3; simp]

  have ub_p00 : b0.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  clear ub_cm0 ub_cm1 ub_cm2 ub_cm3

  have ⟨ eq_a0, eq_cry0 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a0 ub_cry0
  simp [Fin.ext_iff, Fin.val_mul] at eq_a0
  rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a0
  rw [eq_cry0] at ub_cry1 ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry0 eq_cry0

  have ub_p01 : b0.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p10 : b1.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a1, eq_cry1 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a1 ub_cry1
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a1
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a1
  rw [eq_cry1] at ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry1 eq_cry1

  have ub_p02 : b0.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p11 : b1.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p20 : b2.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a2, eq_cry2 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a2 ub_cry2
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a2
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a2
  rw [eq_cry2] at ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry2 eq_cry2

  have ub_p03 : b0.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p12 : b1.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p21 : b2.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p30 : b3.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a3, eq_cry3 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a3 ub_cry3
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a3
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a3
  rw [eq_cry3] at ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry3 eq_cry3

  have ub_p13 : b1.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p22 : b2.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p31 : b3.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_be0 : b0.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_ce0 : c0.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a4, eq_cry4 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a4 ub_cry4
  rw [  add_assoc (b := (b1 * c3 + b2 * c2 + b3 * c1)),
      ← add_assoc (a := (b1 * c3 + b2 * c2 + b3 * c1))] at *
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a4
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a4
  rw [eq_cry4] at ub_cry5 ub_cry6 ub_cry7
  clear ub_cry4 eq_cry4

  have ub_p23 : b2.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p32 : b3.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_be1 : b1.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_ce1 : c1.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a5, eq_cry5 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a5 ub_cry5
  rw [add_assoc (b := (b2 * c3 + b3 * c2))] at *
  iterate 3 rw [← add_assoc (a := (b2 * c3 + b3 * c2))] at *
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a5
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a5
  rw [eq_cry5] at ub_cry6 ub_cry7
  clear ub_cry5 eq_cry5

  have ub_p33 : b3.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_be2 : b2.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_ce2 : c2.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a6, eq_cry6 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a6 ub_cry6
  rw [add_assoc (b := (b3 * c3))] at *
  iterate 5 rw [← add_assoc (a := (b3 * c3))] at *
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a6
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a6
  rw [eq_cry6] at ub_cry7
  clear ub_cry6 eq_cry6

  have ub_be3 : b3.val * c_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_ce3 : c3.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a7, eq_cry7 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a7 ub_cry7
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a7
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a7
  clear ub_cry7 eq_cry7

  rw [eq_a4, eq_a5, eq_a6, eq_a7]
  clear eq_a0 eq_a1 eq_a2 eq_a3 eq_a4 eq_a5 eq_a6 eq_a7

  simp [← BitVec.toNat_inj, U32.toNat]
  rw [Nat.DivMod.div_8 (a := _ * _), Nat.DivMod.div_16, Nat.DivMod.div_24]
  rw [Nat.DivMod.join_8, Nat.DivMod.div_8,
      Nat.DivMod.join_16, Nat.DivMod.div_16,
      Nat.DivMod.join_24]

  simp [U64.toNat, Nat.shiftRight_eq_div_pow]
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
  subst b3 c3
  ring_nf
  omega

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the MULHSU opcode --/
theorem spec_MULHSU
  (h_mulhsu : (air.core.ctx row 0).instruction.opcode = 594)
:
  (U32.toBV #v[(air.core.a_0 row 0).val,
               (air.core.a_1 row 0).val,
               (air.core.a_2 row 0).val,
               (air.core.a_3 row 0).val])
    =
  execute_MUL_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    (rop_of_Mulh_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  obtain ⟨ sop0, sop1, sop2 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_mulh_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2 ⟩ := pa_read
  obtain ⟨ ub_a0, ub_cm0, ub_a1, ub_cm1, ub_a2, ub_cm2, ub_a3, ub_cm3,
           ub_a4, ub_cry0, ub_a5, ub_cry1, ub_a6, ub_cry2, ub_a7, ub_cry3 ⟩ := pa_rtc
  clear pa_exec pa_range

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_mulh_constraint_and_interaction_simplification] at constraints

  obtain ⟨ hint, b_mulh, b_mulhsu, b_mulhu, b_is_valid, b_b_sign, b_c_sign, mulh_b_sign, mulu_c_sign, rest ⟩ := constraints
  clear hint rest

  specialize op1 h_mulhsu; simp [op1] at *
  obtain ⟨ z_mulh, z_mulhu ⟩ := sop1
  simp [z_mulh, z_mulhu] at *
  simp_all
  simp_all [← MulHCoreAir_4_8.b_sign_def,
            ← MulHCoreAir_4_8.c_sign_def,
            ← MulHCoreAir_4_8.carry_mul_0,
            ← MulHCoreAir_4_8.carry_mul_1,
            ← MulHCoreAir_4_8.carry_mul_2,
            ← MulHCoreAir_4_8.carry_mul_3]

  simp [execute_MUL_pure, rop_of_Mulh_opcode, ← U32.extend_BitVec_extend, U32.extend]
  simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]
  simp [@Nat.mod_eq_of_lt (air.core.b_3 row 0).val 256 (by omega)]

  set a4 := air.core.a_0 row 0; set a5 := air.core.a_1 row 0; set a6 := air.core.a_2 row 0; set a7 := air.core.a_3 row 0
  set b0 := air.core.b_0 row 0; set b1 := air.core.b_1 row 0; set b2 := air.core.b_2 row 0; set b3 := air.core.b_3 row 0
  set c0 := air.core.c_0 row 0; set c1 := air.core.c_1 row 0; set c2 := air.core.c_2 row 0; set c3 := air.core.c_3 row 0
  set a0 := air.core.a_mul_0 row 0; set a1 := air.core.a_mul_1 row 0; set a2 := air.core.a_mul_2 row 0; set a3 := air.core.a_mul_3 row
  set b_ext := air.core.b_ext row 0

  have h_msb_b :
    b_ext = if 128 ≤ (air.core.b_3 row 0).val then 255 else 0
    := by
      clear *- ub_b3 b_b_sign pa_bit
      split_ifs <;> grind
  clear pa_bit

  have msb_b_val : (if 128 ≤ (air.core.b_3 row 0).val then 255 else 0) = b_ext.val
    := by rw [h_msb_b]; clear *-; split_ifs <;> simp
  simp [msb_b_val]

  have ub_cry4 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry0; simp]
  have ub_cry5 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry1; simp]
  have ub_cry6 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry2; simp]
  have ub_cry7 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry3; simp]
  clear ub_cry0 ub_cry1 ub_cry2 ub_cry3
  have ub_cry0 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm0; simp]
  have ub_cry1 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm1; simp]
  have ub_cry2 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm2; simp]
  have ub_cry3 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm3; simp]

  have ub_p00 : b0.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  clear ub_cm0 ub_cm1 ub_cm2 ub_cm3

  have ⟨ eq_a0, eq_cry0 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a0 ub_cry0
  simp [Fin.ext_iff, Fin.val_mul] at eq_a0
  rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a0
  rw [eq_cry0] at ub_cry1 ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry0 eq_cry0

  have ub_p01 : b0.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p10 : b1.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a1, eq_cry1 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a1 ub_cry1
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a1
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a1
  rw [eq_cry1] at ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry1 eq_cry1

  have ub_p02 : b0.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p11 : b1.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p20 : b2.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a2, eq_cry2 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a2 ub_cry2
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a2
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a2
  rw [eq_cry2] at ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry2 eq_cry2

  have ub_p03 : b0.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p12 : b1.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p21 : b2.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p30 : b3.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a3, eq_cry3 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a3 ub_cry3
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a3
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a3
  rw [eq_cry3] at ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry3 eq_cry3

  have ub_p13 : b1.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p22 : b2.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p31 : b3.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_ce0 : c0.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a4, eq_cry4 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a4 ub_cry4
  rw [add_assoc (b := (b1 * c3 + b2 * c2 + b3 * c1))] at *
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a4
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a4
  rw [eq_cry4] at ub_cry5 ub_cry6 ub_cry7
  clear ub_cry4 eq_cry4

  have ub_p23 : b2.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p32 : b3.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_ce1 : c1.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a5, eq_cry5 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a5 ub_cry5
  rw [add_assoc (b := (b2 * c3 + b3 * c2))] at *
  rw [← add_assoc (a := (b2 * c3 + b3 * c2))] at *
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a5
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a5
  rw [eq_cry5] at ub_cry6 ub_cry7
  clear ub_cry5 eq_cry5

  have ub_p33 : b3.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_ce2 : c2.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a6, eq_cry6 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a6 ub_cry6
  rw [add_assoc (b := (b3 * c3))] at *
  iterate 2 rw [← add_assoc (a := (b3 * c3))] at *
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a6
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a6
  rw [eq_cry6] at ub_cry7
  clear ub_cry6 eq_cry6

  have ub_ce3 : c3.val * b_ext.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a7, eq_cry7 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a7 ub_cry7
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a7
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a7
  clear ub_cry7 eq_cry7

  rw [eq_a4, eq_a5, eq_a6, eq_a7]
  clear eq_a0 eq_a1 eq_a2 eq_a3 eq_a4 eq_a5 eq_a6 eq_a7

  simp [← BitVec.toNat_inj, U32.toNat]
  rw [Nat.DivMod.div_8 (a := _ * _), Nat.DivMod.div_16, Nat.DivMod.div_24]
  rw [Nat.DivMod.join_8, Nat.DivMod.div_8,
      Nat.DivMod.join_16, Nat.DivMod.div_16,
      Nat.DivMod.join_24]

  simp [U64.toNat, Nat.shiftRight_eq_div_pow]
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
  subst b3 c3
  ring_nf
  omega

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the MULHU opcode --/
theorem spec_MULHU
  (h_mulhu : (air.core.ctx row 0).instruction.opcode = 595)
:
  (U32.toBV #v[(air.core.a_0 row 0).val,
               (air.core.a_1 row 0).val,
               (air.core.a_2 row 0).val,
               (air.core.a_3 row 0).val])
    =
  execute_MUL_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    (rop_of_Mulh_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  obtain ⟨ sop0, sop1, sop2 ⟩ := single_op air row row_in_range constraints
  have ⟨ op0, op1, op2 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_rtc, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_mulh_constraint_and_interaction_simplification, propertiesToAssume] at pa_exec pa_mem pa_range pa_read pa_rtc pa_bit
  repeat rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read pa_rtc
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2, ub_c0, ub_c1, ub_c2, ub_c3, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2 ⟩ := pa_read
  obtain ⟨ ub_a0, ub_cm0, ub_a1, ub_cm1, ub_a2, ub_cm2, ub_a3, ub_cm3,
           ub_a4, ub_cry0, ub_a5, ub_cry1, ub_a6, ub_cry2, ub_a7, ub_cry3 ⟩ := pa_rtc
  clear pa_exec pa_range pa_bit

  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_mulh_constraint_and_interaction_simplification] at constraints

  obtain ⟨ hint, b_mulh, b_mulhsu, b_mulhu, b_is_valid, b_b_sign, b_c_sign, mulh_b_sign, mulu_c_sign, rest ⟩ := constraints
  clear hint rest

  specialize op2 h_mulhu; simp [op2] at *
  obtain ⟨ z_mulh, z_mulhsu ⟩ := sop2
  simp [z_mulh, z_mulhsu] at *
  simp_all
  simp_all [← MulHCoreAir_4_8.b_sign_def,
            ← MulHCoreAir_4_8.c_sign_def,
            ← MulHCoreAir_4_8.carry_mul_0,
            ← MulHCoreAir_4_8.carry_mul_1,
            ← MulHCoreAir_4_8.carry_mul_2,
            ← MulHCoreAir_4_8.carry_mul_3]

  simp [execute_MUL_pure, rop_of_Mulh_opcode, ← U32.extend_BitVec_extend, U32.extend]
  simp [U32.ext, ← U32.msb_3_negative, BitVec.msb_eq_decide]

  set a4 := air.core.a_0 row 0; set a5 := air.core.a_1 row 0; set a6 := air.core.a_2 row 0; set a7 := air.core.a_3 row 0
  set b0 := air.core.b_0 row 0; set b1 := air.core.b_1 row 0; set b2 := air.core.b_2 row 0; set b3 := air.core.b_3 row 0
  set c0 := air.core.c_0 row 0; set c1 := air.core.c_1 row 0; set c2 := air.core.c_2 row 0; set c3 := air.core.c_3 row 0
  set a0 := air.core.a_mul_0 row 0; set a1 := air.core.a_mul_1 row 0; set a2 := air.core.a_mul_2 row 0; set a3 := air.core.a_mul_3 row

  have ub_cry4 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry0; simp]
  have ub_cry5 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry1; simp]
  have ub_cry6 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry2; simp]
  have ub_cry7 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cry3; simp]
  clear ub_cry0 ub_cry1 ub_cry2 ub_cry3
  have ub_cry0 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm0; simp]
  have ub_cry1 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm1; simp]
  have ub_cry2 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm2; simp]
  have ub_cry3 : ?_ < 7864320 := by trans 2048 <;> [exact ub_cm3; simp]

  have ub_p00 : b0.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  clear ub_cm0 ub_cm1 ub_cm2 ub_cm3

  have ⟨ eq_a0, eq_cry0 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a0 ub_cry0
  simp [Fin.ext_iff, Fin.val_mul] at eq_a0
  rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a0
  rw [eq_cry0] at ub_cry1 ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry0 eq_cry0

  have ub_p01 : b0.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p10 : b1.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a1, eq_cry1 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a1 ub_cry1
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a1
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a1
  rw [eq_cry1] at ub_cry2 ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry1 eq_cry1

  have ub_p02 : b0.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p11 : b1.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p20 : b2.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a2, eq_cry2 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a2 ub_cry2
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a2
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a2
  rw [eq_cry2] at ub_cry3 ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry2 eq_cry2

  have ub_p03 : b0.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p12 : b1.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p21 : b2.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p30 : b3.val * c0.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a3, eq_cry3 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a3 ub_cry3
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a3
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a3
  rw [eq_cry3] at ub_cry4 ub_cry5 ub_cry6 ub_cry7
  clear ub_cry3 eq_cry3

  have ub_p13 : b1.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p22 : b2.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p31 : b3.val * c1.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a4, eq_cry4 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a4 ub_cry4
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a4
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a4
  rw [eq_cry4] at ub_cry5 ub_cry6 ub_cry7
  clear ub_cry4 eq_cry4

  have ub_p23 : b2.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega
  have ub_p32 : b3.val * c2.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a5, eq_cry5 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a5 ub_cry5
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a5
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a5
  rw [eq_cry5] at ub_cry6 ub_cry7
  clear ub_cry5 eq_cry5

  have ub_p33 : b3.val * c3.val ≤ 255 * 255 := by apply mul_le_mul <;> omega

  have ⟨ eq_a6, eq_cry6 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a6 ub_cry6
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a6
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a6
  rw [eq_cry6] at ub_cry7
  clear ub_cry6 eq_cry6

  have ⟨ eq_a7, eq_cry7 ⟩ := BabyBear.inv256_prod_diff_div_mod ub_a7 ub_cry7
  simp [Fin.ext_iff, Fin.val_add, Fin.val_mul] at eq_a7
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] at eq_a7
  clear ub_cry7 eq_cry7

  rw [eq_a4, eq_a5, eq_a6, eq_a7]
  clear eq_a0 eq_a1 eq_a2 eq_a3 eq_a4 eq_a5 eq_a6 eq_a7

  simp [← BitVec.toNat_inj, U32.toNat]
  rw [Nat.DivMod.div_8 (a := _ * _), Nat.DivMod.div_16, Nat.DivMod.div_24]
  rw [Nat.DivMod.join_8, Nat.DivMod.div_8,
      Nat.DivMod.join_16, Nat.DivMod.div_16,
      Nat.DivMod.join_24']

  simp [U64.toNat, Nat.shiftRight_eq_div_pow]
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
  subst b3 c3
  ring_nf
  omega

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the MULH opcodes:
    - the `b` operand read from memory; and
    - the `c` operand as per the circuit
--/
theorem spec_mulh
:
  (U32.toBV #v[(air.core.a_0 row 0).val,
               (air.core.a_1 row 0).val,
               (air.core.a_2 row 0).val,
               (air.core.a_3 row 0).val])
    =
  execute_MUL_pure
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (U32.toBV #v[(air.core.c_0 row 0).val,
                 (air.core.c_1 row 0).val,
                 (air.core.c_2 row 0).val,
                 (air.core.c_3 row 0).val])
    (rop_of_Mulh_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  have := opcode_bounds air row row_in_range constraints row_valid
  rcases this with mulh | mulhsu | mulhu
  . apply spec_MULH <;> assumption
  . apply spec_MULHSU <;> assumption
  . apply spec_MULHU <;> assumption

end General

end Mulh.ValidRows
