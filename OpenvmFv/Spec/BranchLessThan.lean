import Mathlib

import OpenvmFv.Airs.Branch.VmAirWrapper_branch_lt
import OpenvmFv.Constraints.VmAirWrapper_branch_lt
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

attribute [-simp]
  EuclideanDomain.mod_eq_zero
  neg_le_sub_iff_le_add

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_branch_lt.constraints.allHold air row row_in_range)

namespace BranchLessThan.NonValidRows

open VmAirWrapper_branch_lt.constraints

variable (row_not_valid : air.core.is_valid row 0 = 0)

include
  row_in_range
in
/-- Zeros required to form a non-valid row -/
lemma non_valid_row_BranchLessThan_allZeros_allHold
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
  air.core.opcode_blt_flag row 0 = 0 ∧
  air.core.opcode_bltu_flag row 0 = 0 ∧
  air.core.opcode_bge_flag row 0 = 0 ∧
  air.core.opcode_bgeu_flag row 0 = 0 ∧
  air.core.a_msb_f row 0 = 0 ∧
  air.core.b_msb_f row 0 = 0 ∧
  air.core.cmp_lt row 0 = 0 ∧
  air.core.diff_marker_0 row 0 = 0 ∧
  air.core.diff_marker_1 row 0 = 0 ∧
  air.core.diff_marker_2 row 0 = 0 ∧
  air.core.diff_marker_3 row 0 = 0 ∧
  air.core.diff_val row 0 = 0
    → air.core.is_valid row 0 = 0 ∧
      allHold air row row_in_range
:= by
  rw [allHold_simplified_of_allHold]
  simp_all; intros
  simp_all [VmAirWrapper_branch_lt_constraint_and_interaction_simplification,
            Valid_BranchLessThanCoreAir_4_8.is_valid,
            ← BranchLessThanCoreAir_4_8.prefix_sum_3_def,
            ← BranchLessThanCoreAir_4_8.prefix_sum_2_def,
            ← BranchLessThanCoreAir_4_8.prefix_sum_1_def,
            ← BranchLessThanCoreAir_4_8.prefix_sum_0_def,
            ← BranchLessThanCoreAir_4_8.diff_3_def,
            ← BranchLessThanCoreAir_4_8.diff_2_def,
            ← BranchLessThanCoreAir_4_8.diff_1_def,
            ← BranchLessThanCoreAir_4_8.diff_0_def,
            ← BranchLessThanCoreAir_4_8.a_diff_def,
            ← BranchLessThanCoreAir_4_8.b_diff_def,
            Valid_BranchLessThanCoreAir_4_8.ge]

include
  row_in_range
  row_not_valid
  constraints
in
/-- On non-valid rows, all interactin multiplicities equal zero -/
lemma non_valid_row_BranchLessThan_all_interaction_multiplicities_zero
:
  (entry ∈ executionBus_row air row ++
           memoryBus_row air row ++
           rangeCheckerBus_row air row ++
           readInstructionBus_row air row → entry.1 = 0) ∧
  (entry ∈ bitwiseBus_row air row →
    entry.1 = 0 ∨
    (air.core.prefix_sum row 0 0 = 1 ∧
     entry = (1, [air.core.diff_val row 0 - 1, 0, 0, 0])))
:= by
  obtain ⟨ hint, constraints ⟩ := constraints
  clear hint; unfold extracted_row_constraint_list at constraints
  simp only [VmAirWrapper_branch_lt_air_simplification,
             VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at constraints
  simp at constraints
  simp_all [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
  simp_all [← BranchLessThanCoreAir_4_8.prefix_sum_0_def,
            ← BranchLessThanCoreAir_4_8.prefix_sum_1_def,
            ← BranchLessThanCoreAir_4_8.prefix_sum_2_def]
  grind (splits := 11)

end BranchLessThan.NonValidRows

open VmAirWrapper_branch_lt.constraints

namespace BranchLessThan.ValidRows

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
  simp [row_valid, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read pa_bit

  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := readInstructionBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at pa_read

  rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read
  obtain ⟨ ub_rs1, ub_a0, ub_a1, ub_a2, ub_a3, ub_rs2, ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := pa_mem
  obtain ⟨ ri_rs1, ri_rs2, lb_imm, ub_imm, imm_mod ⟩ := pa_read
  clear pa_range

  have ⟨ sop0, sop1, sop2, sop3 ⟩ := single_op air row row_in_range constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp_all [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
  grind

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
  (air.to_pc row 0) % 4 = 0 ∧
  List.Forall (fun x => x.val < 256)
    [air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0,
     air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0] ∧
  (air.core.expected_opcode row 0 = 549 ∨
   air.core.expected_opcode row 0 = 550 ∨
   air.core.expected_opcode row 0 = 551 ∨
   air.core.expected_opcode row 0 = 552) ∧
  (-2^12 ≤ BabyBear.toInt (air.core.imm row 0) ∧ BabyBear.toInt (air.core.imm row 0) < 2^12)
:= by
  have assertions := wf_propertiesToAssert ExtF air row row_in_range constraints row_valid propertiesToAssume

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read

  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := readInstructionBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at pa_read

  rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read
  obtain ⟨ ub_rs1, ub_a0, ub_a1, ub_a2, ub_a3, ub_rs2, ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := pa_mem
  obtain ⟨ ri_rs1, ri_rs2, lb_imm, ub_imm ⟩ := pa_read
  clear pa_exec pa_range

  simp [row_valid, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at assumptions assertions
  clear constraints; simp_all
  split_ands <;> omega

include
  row_valid
  constraints
  assumptions
  propertiesToAssume in
lemma next_pc_two_last_bits_zero
:
  (BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val +
    BitVec.signExtend 32 (BitVec.ofInt 13 (BabyBear.toInt (air.core.imm row 0))))[0] = false ∧
  (BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val +
    BitVec.signExtend 32 (BitVec.ofInt 13 (BabyBear.toInt (air.core.imm row 0))))[1] = false
:= by
  have assertions := wf_propertiesToAssert ExtF air row row_in_range constraints row_valid propertiesToAssume

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read

  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := readInstructionBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at pa_read

  rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read
  obtain ⟨ ub_rs1, ub_a0, ub_a1, ub_a2, ub_a3, ub_rs2, ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := pa_mem
  obtain ⟨ ri_rs1, ri_rs2, lb_imm, ub_imm, aligned_imm ⟩ := pa_read
  clear pa_exec pa_range

  simp [row_valid, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at assumptions assertions
  have pa_exec := assumptions.1.1.2
  rw [BabyBear.mod_4_zero_bits_zero] at pa_exec
  obtain ⟨ pc0, pc1 ⟩ := pa_exec
  suffices :
    (BitVec.ofInt 13 (BabyBear.toInt (air.core.imm row 0)))[0] = false ∧
    (BitVec.ofInt 13 (BabyBear.toInt (air.core.imm row 0)))[1] = false
  . obtain ⟨ npc0, npc1 ⟩ := this
    bv_decide
  . obtain ⟨ x, eq_x ⟩ : exists x, BabyBear.toInt (air.core.imm row 0) = x := by simp
    simp [eq_x] at lb_imm ub_imm aligned_imm ⊢
    clear *- lb_imm ub_imm aligned_imm
    have : x % (4 : ℤ) = (1 : ℤ) * ((BitVec.ofInt 13 x)[0]).toNat + (2 : ℤ) * (BitVec.ofInt 13 x)[1].toNat
    := by
      simp only [BitVec.getElem_eq_testBit_toNat]
      simp [Nat.testBit_eq_decide_div_mod_eq]
      by_cases h_sgn : 0 ≤ x
      . rw [Int.emod_eq_of_lt (b := 8192) (by omega) (by omega)]
        by_cases (x.toNat % 2 = 1) <;>
        by_cases (x.toNat / 2 % 2 = 1) <;>
        simp_all <;>
        omega
      . simp at h_sgn
        by_cases ((x % 8192).toNat % 2 = 1) <;>
        simp_all <;> omega

    rw [this] at aligned_imm; clear this
    by_cases (BitVec.ofInt 13 x)[0] <;>
    by_cases (BitVec.ofInt 13 x)[1] <;> simp_all

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail the correct change
    of the `pc` for BLT/BLTU/BGE/BGEU, in FBB terms
--/
theorem spec_BLT_BLTU_BGE_BGEU_pc_FBB
:
  (air.core.expected_opcode row 0 = 549 →
    air.to_pc row 0 =
      if (U32.toBV #v[(air.core.a_0 row 0).val,
                      (air.core.a_1 row 0).val,
                      (air.core.a_2 row 0).val,
                      (air.core.a_3 row 0).val]).toInt
           <b
         (U32.toBV #v[(air.core.b_0 row 0).val,
                     (air.core.b_1 row 0).val,
                     (air.core.b_2 row 0).val,
                     (air.core.b_3 row 0).val]).toInt
      then air.adapter.from_state.pc row 0 + air.core.imm row 0
      else air.adapter.from_state.pc row 0 + 4) ∧
  (air.core.expected_opcode row 0 = 550 →
    air.to_pc row 0 =
      if (U32.toBV #v[(air.core.a_0 row 0).val,
                      (air.core.a_1 row 0).val,
                      (air.core.a_2 row 0).val,
                      (air.core.a_3 row 0).val]).toNat
           <b
         (U32.toBV #v[(air.core.b_0 row 0).val,
                     (air.core.b_1 row 0).val,
                     (air.core.b_2 row 0).val,
                     (air.core.b_3 row 0).val]).toNat
      then air.adapter.from_state.pc row 0 + air.core.imm row 0
      else air.adapter.from_state.pc row 0 + 4) ∧
  (air.core.expected_opcode row 0 = 551 →
    air.to_pc row 0 =
      if (U32.toBV #v[(air.core.a_0 row 0).val,
                      (air.core.a_1 row 0).val,
                      (air.core.a_2 row 0).val,
                      (air.core.a_3 row 0).val]).toInt
           ≥b
         (U32.toBV #v[(air.core.b_0 row 0).val,
                     (air.core.b_1 row 0).val,
                     (air.core.b_2 row 0).val,
                     (air.core.b_3 row 0).val]).toInt
      then air.adapter.from_state.pc row 0 + air.core.imm row 0
      else air.adapter.from_state.pc row 0 + 4) ∧
  (air.core.expected_opcode row 0 = 552 →
    air.to_pc row 0 =
      if (U32.toBV #v[(air.core.a_0 row 0).val,
                      (air.core.a_1 row 0).val,
                      (air.core.a_2 row 0).val,
                      (air.core.a_3 row 0).val]).toNat
           ≥b
         (U32.toBV #v[(air.core.b_0 row 0).val,
                     (air.core.b_1 row 0).val,
                     (air.core.b_2 row 0).val,
                     (air.core.b_3 row 0).val]).toNat
      then air.adapter.from_state.pc row 0 + air.core.imm row 0
      else air.adapter.from_state.pc row 0 + 4)
:= by
  sorry
  -- obtain ⟨ pa_exec, pa_mem, pa_range, pa_read ⟩ := propertiesToAssume
  -- simp [row_valid, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read

  -- -- Get all opcode properties
  -- obtain ⟨ sop0, sop1 ⟩ := single_op air row row_in_range constraints
  -- obtain ⟨ op0, op1 ⟩ := op_from_opcode air row row_in_range constraints row_valid
  -- have opcodes := opcode_bounds air row row_in_range constraints row_valid
  -- replace pa_read := readInstructionBus_properties_of_opcode_bounds _ opcodes pa_read
  -- simp [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at pa_read

  -- rw [Fin.ext_iff] at pa_mem
  -- simp [and_assoc] at pa_mem pa_range pa_read
  -- obtain ⟨ ub_rs1, ub_a0, ub_a1, ub_a2, ub_a3, ub_rs2, ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := pa_mem
  -- obtain ⟨ ri_rs1, ri_rs2, lb_imm, ub_imm ⟩ := pa_read
  -- clear pa_exec pa_range

  -- -- Prepare constraints
  -- rw [allHold_simplified_of_allHold] at constraints
  -- simp [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at *
  -- obtain ⟨ constrain_interactions,
  --          b_beq, b_bne, b_is_valid, b_cmp,
  --          cmp_0, cmp_1, cmp_2, cmp_3, sum, rest ⟩ := constraints
  -- clear constrain_interactions rest

  -- rw [← VmAirWrapper_branch_lt.to_pc_def] at *
  -- rw [← BranchLessThanCoreAir_4.sum_def] at *
  -- rw [← BranchLessThanCoreAir_4.cmp_eq_def] at *

  -- split_ands <;> intro h_opcode <;> simp_all

  -- all_goals
  --   rcases b_cmp with h_cmp | h_cmp <;> simp_all
  --   . intro h_eq
  --     have : air.core.a_0 row 0 = air.core.b_0 row 0 ∧
  --           air.core.a_1 row 0 = air.core.b_1 row 0 ∧
  --           air.core.a_2 row 0 = air.core.b_2 row 0 ∧
  --           air.core.a_3 row 0 = air.core.b_3 row 0
  --     := by
  --       simp [← BitVec.toNat_inj, U32.toNat] at h_eq
  --       grind
  --     simp_all

include
  row_valid
  constraints
  assumptions
  propertiesToAssume in
/-- The constraints entail the correct change
    of the `pc` for BLT/BLTU/BGE/BGEU, in BitVec terms
--/
theorem spec_BLT_BLTU_BGE_BGEU_pc
:
  (air.core.expected_opcode row 0 = 549 →
    BitVec.ofNat 32 (air.to_pc row 0) =
      if (U32.toBV #v[(air.core.a_0 row 0).val,
                      (air.core.a_1 row 0).val,
                      (air.core.a_2 row 0).val,
                      (air.core.a_3 row 0).val]).toInt
           <b
         (U32.toBV #v[(air.core.b_0 row 0).val,
                     (air.core.b_1 row 0).val,
                     (air.core.b_2 row 0).val,
                     (air.core.b_3 row 0).val]).toInt
      then BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val +
           BitVec.signExtend 32 (BitVec.ofInt 13 (BabyBear.toInt (air.core.imm row 0)))
      else BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32) ∧
  (air.core.expected_opcode row 0 = 550 →
    BitVec.ofNat 32 (air.to_pc row 0) =
      if (U32.toBV #v[(air.core.a_0 row 0).val,
                      (air.core.a_1 row 0).val,
                      (air.core.a_2 row 0).val,
                      (air.core.a_3 row 0).val]).toNat
           <b
         (U32.toBV #v[(air.core.b_0 row 0).val,
                     (air.core.b_1 row 0).val,
                     (air.core.b_2 row 0).val,
                     (air.core.b_3 row 0).val]).toNat
      then BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val +
           BitVec.signExtend 32 (BitVec.ofInt 13 (BabyBear.toInt (air.core.imm row 0)))
      else BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32) ∧
  (air.core.expected_opcode row 0 = 551 →
    BitVec.ofNat 32 (air.to_pc row 0) =
      if (U32.toBV #v[(air.core.a_0 row 0).val,
                      (air.core.a_1 row 0).val,
                      (air.core.a_2 row 0).val,
                      (air.core.a_3 row 0).val]).toInt
           ≥b
         (U32.toBV #v[(air.core.b_0 row 0).val,
                     (air.core.b_1 row 0).val,
                     (air.core.b_2 row 0).val,
                     (air.core.b_3 row 0).val]).toInt
      then BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val +
           BitVec.signExtend 32 (BitVec.ofInt 13 (BabyBear.toInt (air.core.imm row 0)))
      else BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32) ∧
  (air.core.expected_opcode row 0 = 552 →
    BitVec.ofNat 32 (air.to_pc row 0) =
      if (U32.toBV #v[(air.core.a_0 row 0).val,
                      (air.core.a_1 row 0).val,
                      (air.core.a_2 row 0).val,
                      (air.core.a_3 row 0).val]).toNat
           ≥b
         (U32.toBV #v[(air.core.b_0 row 0).val,
                     (air.core.b_1 row 0).val,
                     (air.core.b_2 row 0).val,
                     (air.core.b_3 row 0).val]).toNat
      then BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val +
           BitVec.signExtend 32 (BitVec.ofInt 13 (BabyBear.toInt (air.core.imm row 0)))
      else BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32)
:= by
  obtain ⟨ spec_blt, spec_bltu, spec_bge, spec_bgeu ⟩ :=
    spec_BLT_BLTU_BGE_BGEU_pc_FBB _ air row row_in_range constraints row_valid propertiesToAssume

  have ⟨
    h_pc, h_next_pc,
    rest
  ⟩ := BranchLessThan.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        constraints
        row_valid
        assumptions
        propertiesToAssume
  clear rest

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read pa_bit

  -- Get all opcode properties
  obtain ⟨ sop0, sop1, sop2, sop3 ⟩ := single_op air row row_in_range constraints
  obtain ⟨ op0, op1, op2, op3 ⟩ := op_from_opcode air row row_in_range constraints row_valid
  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := readInstructionBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at pa_read

  rw [Fin.ext_iff] at pa_mem
  simp [and_assoc] at pa_mem pa_range pa_read
  obtain ⟨ ub_rs1, ub_a0, ub_a1, ub_a2, ub_a3, ub_rs2, ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := pa_mem
  obtain ⟨ ri_rs1, ri_rs2, lb_imm, ub_imm ⟩ := pa_read
  clear pa_exec pa_range

  clear constraints

  split_ands <;> intro h_opcode <;>
  [
    have spec := spec_blt;
    have spec := spec_bltu;
    have spec := spec_bge;
    have spec := spec_bgeu
  ] <;>
  clear spec_blt spec_bltu spec_bge spec_bgeu

  . simp [h_opcode] at spec
    simp [← BitVec.toNat_inj, -BitVec.toNat_ofNat]
    rw [BitVec.toNat_inj]
    split_ifs with h_eq
    . rw [if_pos (by omega)] at spec
      rw [spec] at h_next_pc ⊢
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
    . rw [if_neg (by omega)] at spec
      rw [spec] at h_next_pc ⊢
      simp [← BitVec.toNat_inj, Fin.val_add]
      omega

  . simp [h_opcode] at spec
    simp [← BitVec.toNat_inj, -BitVec.toNat_ofNat]
    rw [BitVec.toNat_inj]
    split_ifs with h_eq
    . rw [if_pos (by omega)] at spec
      rw [spec] at h_next_pc ⊢
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
    . rw [if_neg (by omega)] at spec
      rw [spec] at h_next_pc ⊢
      simp [← BitVec.toNat_inj, Fin.val_add]
      omega

  . simp [h_opcode] at spec
    simp [← BitVec.toNat_inj, -BitVec.toNat_ofNat]
    rw [BitVec.toNat_inj]
    split_ifs with h_eq
    . rw [if_pos (by omega)] at spec
      rw [spec] at h_next_pc ⊢
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
    . rw [if_neg (by omega)] at spec
      rw [spec] at h_next_pc ⊢
      simp [← BitVec.toNat_inj, Fin.val_add]
      omega

  . simp [h_opcode] at spec
    simp [← BitVec.toNat_inj, -BitVec.toNat_ofNat]
    rw [BitVec.toNat_inj]
    split_ifs with h_eq
    . rw [if_pos (by omega)] at spec
      rw [spec] at h_next_pc ⊢
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
    . rw [if_neg (by omega)] at spec
      rw [spec] at h_next_pc ⊢
      simp [← BitVec.toNat_inj, Fin.val_add]
      omega

end General

end BranchLessThan.ValidRows
