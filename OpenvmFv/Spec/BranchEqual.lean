import Mathlib

import OpenvmFv.Airs.Branch.VmAirWrapper_branch_eq
import OpenvmFv.Constraints.VmAirWrapper_branch_eq
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

attribute [-simp]
  EuclideanDomain.mod_eq_zero
  neg_le_sub_iff_le_add

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
  air.core.imm row 0 = 0 ∧
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
  obtain ⟨ lb_imm, ub_imm ⟩ := pa_read
  clear pa_range

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
  (air.adapter.from_state.pc row 0) % 4 = 0 ∧
  (air.to_pc row 0).val < 1073741824 ∧
  (air.to_pc row 0) % 4 = 0 ∧
  List.Forall (fun x => x.val < 256)
    [air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0,
     air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0] ∧
  (air.core.expected_opcode row 0 = 544 ∨
   air.core.expected_opcode row 0 = 545) ∧
  (-2^12 ≤ BabyBear.toInt (air.core.imm row 0) ∧ BabyBear.toInt (air.core.imm row 0) < 2^12)
:= by
  have assertions := wf_propertiesToAssert ExtF air row row_in_range constraints row_valid propertiesToAssume

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read

  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := readInstructionBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at pa_read

  rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read
  obtain ⟨ ub_rs1, ub_a0, ub_a1, ub_a2, ub_a3, ub_rs2, ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := pa_mem
  obtain ⟨ lb_imm, ub_imm ⟩ := pa_read
  clear pa_exec pa_range

  simp [row_valid, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at assumptions assertions
  clear constraints; simp_all
  split_ands <;> omega

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail the correct change
    of the `pc` for BEQ/BNE, in FBB terms
--/
theorem spec_BEQ_BNE_pc_FBB
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
  obtain ⟨ lb_imm, ub_imm ⟩ := pa_read
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

include
  row_valid
  constraints
  assumptions
  propertiesToAssume in
/-- The constraints entail the correct change
    of the `pc` for BEQ/BNE, in BitVec terms
--/
theorem spec_BEQ_BNE_pc
:
  (air.core.expected_opcode row 0 = 544 →
    BitVec.ofNat 32 (air.to_pc row 0) =
      if U32.toBV #v[(air.core.a_0 row 0).val,
                    (air.core.a_1 row 0).val,
                    (air.core.a_2 row 0).val,
                    (air.core.a_3 row 0).val]
          ==
        U32.toBV #v[(air.core.b_0 row 0).val,
                    (air.core.b_1 row 0).val,
                    (air.core.b_2 row 0).val,
                    (air.core.b_3 row 0).val]
      then BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val +
           BitVec.signExtend 32 (BitVec.ofInt 13 (BabyBear.toInt (air.core.imm row 0)))
      else BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32) ∧
  (air.core.expected_opcode row 0 = 545 →
    BitVec.ofNat 32 (air.to_pc row 0) =
      if U32.toBV #v[(air.core.a_0 row 0).val,
                    (air.core.a_1 row 0).val,
                    (air.core.a_2 row 0).val,
                    (air.core.a_3 row 0).val]
          !=
        U32.toBV #v[(air.core.b_0 row 0).val,
                    (air.core.b_1 row 0).val,
                    (air.core.b_2 row 0).val,
                    (air.core.b_3 row 0).val]
      then BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val +
           BitVec.signExtend 32 (BitVec.ofInt 13 (BabyBear.toInt (air.core.imm row 0)))
      else BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32)
:= by
  obtain ⟨ spec_beq, spec_bne ⟩ :=
    spec_BEQ_BNE_pc_FBB _ air row row_in_range constraints row_valid propertiesToAssume

  have ⟨
    h_pc_range, h_pc_alignment,
    h_next_pc_range, h_next_pc_alignment,
    rest
  ⟩ := BranchEqual.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        constraints
        row_valid
        assumptions
        propertiesToAssume
  clear rest

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
  obtain ⟨ lb_imm, ub_imm ⟩ := pa_read
  clear pa_exec pa_range

  clear constraints

  split_ands <;> intro h_opcode
  . clear spec_bne
    simp [h_opcode, ← BitVec.toNat_inj, U32.toNat] at spec_beq
    simp [← BitVec.toNat_inj, U32.toNat, -BitVec.toNat_ofNat]
    rewrite [
      Nat.mod_eq_of_lt ub_a0,
      Nat.mod_eq_of_lt ub_a1,
      Nat.mod_eq_of_lt ub_a2,
      Nat.mod_eq_of_lt ub_a3,
      Nat.mod_eq_of_lt ub_b0,
      Nat.mod_eq_of_lt ub_b1,
      Nat.mod_eq_of_lt ub_b2,
      Nat.mod_eq_of_lt ub_b3,
    ] at spec_beq
    rw [BitVec.toNat_inj]
    simp
    rewrite [
      Nat.mod_eq_of_lt ub_a0,
      Nat.mod_eq_of_lt ub_a1,
      Nat.mod_eq_of_lt ub_a2,
      Nat.mod_eq_of_lt ub_a3,
      Nat.mod_eq_of_lt ub_b0,
      Nat.mod_eq_of_lt ub_b1,
      Nat.mod_eq_of_lt ub_b2,
      Nat.mod_eq_of_lt ub_b3,
    ]
    split_ifs with h_eq
    . rw [if_pos (by omega)] at spec_beq
      rw [spec_beq] at h_next_pc_range ⊢
      unfold BabyBear.toInt at *
      split_ifs with sgn_imm
      . simp_all
        rw [Fin.val_add]
        rw [Nat.mod_eq_of_lt (by omega)]
        rw [BitVec.signExtend_eq_setWidth_of_msb_false]
        . simp [← BitVec.toNat_inj]
          omega
        . simp [BitVec.msb_eq_decide]; omega
      . simp_all
        trans (BitVec.ofInt 32 ↑(air.adapter.from_state.pc row 0 + air.core.imm row 0))
        . grind
        . have : BitVec.ofNat 32 ↑(air.adapter.from_state.pc row 0) = BitVec.ofInt 32 ↑(air.adapter.from_state.pc row 0) := by grind
          rw [this]; clear this
          have : (air.adapter.from_state.pc row 0 + air.core.imm row 0).val = (air.adapter.from_state.pc row 0).val + (air.core.imm row 0).val - 2013265921
            := by omega
          rw [this]; clear this
          rw [Int.natCast_sub (by omega), Int.natCast_add]
          rw [Nat.cast_ofNat, Int.add_sub_assoc]
          simp [BitVec.ofInt_add]
          obtain ⟨ x, eq_x ⟩ : exists x : ℤ, ↑↑(air.core.imm row 0) - 2013265921 = x := by simp
          simp_all; clear *- lb_imm ub_imm
          simp [← BitVec.toInt_inj, BitVec.signExtend]
          simp [Int.bmod_def]
          omega
    . rw [if_neg (by omega)] at spec_beq
      rw [spec_beq] at h_next_pc_range ⊢
      simp [← BitVec.toNat_inj, Fin.val_add]
      omega

  . clear spec_beq
    simp [h_opcode, ← BitVec.toNat_inj, U32.toNat] at spec_bne
    simp [← BitVec.toNat_inj, U32.toNat, -BitVec.toNat_ofNat]
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)] at spec_bne
    rw [BitVec.toNat_inj]
    simp
    split_ifs with h_eq
    . rw [if_pos (by omega)] at spec_bne
      rw [spec_bne] at h_next_pc_range ⊢
      simp [← BitVec.toNat_inj, Fin.val_add]
      omega
    . rw [if_neg (by omega)] at spec_bne
      rw [spec_bne] at h_next_pc_range ⊢
      unfold BabyBear.toInt at *
      split_ifs with sgn_imm
      . simp_all
        rw [Fin.val_add]
        rw [Nat.mod_eq_of_lt (by omega)]
        rw [BitVec.signExtend_eq_setWidth_of_msb_false]
        . simp [← BitVec.toNat_inj]
          omega
        . simp [BitVec.msb_eq_decide]; omega
      . simp_all
        trans (BitVec.ofInt 32 ↑(air.adapter.from_state.pc row 0 + air.core.imm row 0))
        . grind
        . have : BitVec.ofNat 32 ↑(air.adapter.from_state.pc row 0) = BitVec.ofInt 32 ↑(air.adapter.from_state.pc row 0) := by grind
          rw [this]; clear this
          have : (air.adapter.from_state.pc row 0 + air.core.imm row 0).val = (air.adapter.from_state.pc row 0).val + (air.core.imm row 0).val - 2013265921
            := by omega
          rw [this]; clear this
          rw [Int.natCast_sub (by omega), Int.natCast_add]
          rw [Nat.cast_ofNat, Int.add_sub_assoc]
          simp [BitVec.ofInt_add]
          obtain ⟨ x, eq_x ⟩ : exists x : ℤ, ↑↑(air.core.imm row 0) - 2013265921 = x := by simp
          simp_all; clear *- lb_imm ub_imm
          simp [← BitVec.toInt_inj, BitVec.signExtend]
          simp [Int.bmod_def]
          omega

end General

end BranchEqual.ValidRows
