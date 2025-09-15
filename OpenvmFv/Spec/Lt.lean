import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_lt
import OpenvmFv.Constraints.VmAirWrapper_lt
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_lt FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_lt.constraints.allHold air row row_in_range)

namespace Lt.NonValidRows

open VmAirWrapper_lt.constraints

variable (row_not_valid : air.core.is_valid row 0 = 0)

include
  row_in_range
in
/-- Zeros required to form a non-valid row -/
lemma non_valid_row_Lt_allZeros_allHold
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
  air.core.cmp_result row 0 = 0 ∧
  air.core.opcode_slt_flag row 0 = 0 ∧
  air.core.opcode_sltu_flag row 0 = 0 ∧
  air.core.b_msb_f row 0 = 0 ∧
  air.core.c_msb_f row 0 = 0 ∧
  air.core.diff_marker_0 row 0 = 0 ∧
  air.core.diff_marker_1 row 0 = 0 ∧
  air.core.diff_marker_2 row 0 = 0 ∧
  air.core.diff_marker_3 row 0 = 0 ∧
  air.core.diff_val row 0 = 0
    → air.core.is_valid row 0 = 0 ∧
      allHold air row row_in_range
:= by
  rw [allHold_simplified_of_allHold]
  simp_all; intro hint h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
                       h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification]
  simp [← LessThanCoreAir_4.is_valid_def,
        ← LessThanCoreAir_4.diff_def_0,
        ← LessThanCoreAir_4.diff_def_1,
        ← LessThanCoreAir_4.diff_def_2,
        ← LessThanCoreAir_4.diff_def_3,
        ← LessThanCoreAir_4.prefix_sum_0_def,
        ← LessThanCoreAir_4.prefix_sum_1_def,
        ← LessThanCoreAir_4.prefix_sum_2_def,
        ← VmAirWrapper_lt.rs2_imm_def,
        ← VmAirWrapper_lt.rs2_sign_limbs]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
  split_ands <;> (try decide) <;> simp

include
  row_in_range
  row_not_valid
  constraints
in
/-- On non-valid rows, all interactin multiplicities equal zero -/
lemma non_valid_row_Lt_all_interaction_multiplicities_zero
  (entry : FBB × List FBB)
:
  (entry ∈ executionBus_row air row ++
           memoryBus_row air row ++
           rangeBus_row air row ++
           readInstructionBus_row air row → entry.1 = 0) ∧
  (entry ∈ bitwiseBus_row air row →
    entry.1 = 0 ∨
    (air.core.prefix_sum row 0 0 = 1 ∧
     entry = (1, [air.core.diff_val row 0 - 1, 0, 0, 0])))
:= by
  obtain ⟨ hint, constraints ⟩ := constraints
  clear hint; unfold extracted_row_constraint_list at constraints
  simp only [VmAirWrapper_lt_air_simplification,
               VmAirWrapper_lt_constraint_and_interaction_simplification] at constraints
  simp at constraints
  have : air.adapter.rs2_as row 0 = 0 := by grind
  simp_all [VmAirWrapper_lt_constraint_and_interaction_simplification]
  simp_all [← LessThanCoreAir_4.prefix_sum_0_def,
            ← LessThanCoreAir_4.prefix_sum_1_def,
            ← LessThanCoreAir_4.prefix_sum_2_def]
  grind (splits := 15)

end Lt.NonValidRows

open VmAirWrapper_lt.constraints

namespace Lt.ValidRows

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
  simp [row_valid, VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_bit

  simp only [propertiesToAssume,
             ReadInstructionBusEntryInstanceLt,
             Interaction.ReadInstructionBusEntryInstance,
             _readInstructionBus_row,
             readInstructionBus_row.eq_1] at pa_read
  simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil] at pa_read
  simp only [row_valid, Interaction.ReadInstructionBusEntry.deserialise] at pa_read
  simp at pa_read
  repeat rw [Fin.ext_iff] at pa_mem pa_range pa_read pa_bit
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2n_c, ub_rs2p_c, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2_non_imm, ri_imm ⟩ := pa_read
  obtain ⟨ ba0, ba1, ba2, ba3 ⟩ := pa_bit
  clear pa_exec pa_range

  have ⟨ sop0, sop1 ⟩ := single_op air row row_in_range constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_add, b_sub, b_is_valid, b_cmp_result, msb_b, msb_c,
           b_dm3, sum3_diff, dm3_diff, b_dm2, sum2_diff, dm2_diff,
           b_dm1, sum1_diff, dm1_diff, b_dm0, sum0_diff, dm0_diff,
           b_sum, sum0_cmp1, b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints
  clear constrain_interactions rest
  simp_all

  have : (air.core.cmp_result row 0).val < 256 :=
    by rcases b_cmp_result <;> simp_all

  simp [Fin.ext_iff] at ub_rs2n_c

  rcases b_rs2_as <;>
  simp_all [VmAirWrapper_lt_constraint_and_interaction_simplification]

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
    [air.core.cmp_result row 0,
     air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0,
     air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0] ∧
  ((air.core.ctx row 0).instruction.opcode = 520 ∨
   (air.core.ctx row 0).instruction.opcode = 521) ∧
  (air.adapter.rs2_as row 0 = 0 ∨ air.adapter.rs2_as row 0 = 1) ∧
  (air.adapter.rs2_as row 0 = 0 →
    (air.adapter.rs2 row 0).val < 16777216 ∧
    (BitVec.ofNat 24 (air.adapter.rs2 row 0).val).toInt = (BitVec.ofNat 12 (air.adapter.rs2 row 0).val).toInt ∧
    air.adapter.rs2 row 0 = air.rs2_imm row 0 ∧
    air.rs2_sign row 0 = air.rs2_limbs row 0 3 ∧
    (air.core.c_2 row 0 = 0 ∨ air.core.c_2 row 0 = 255))
:= by
  have assertedProperties := wf_propertiesToAssert _ air row row_in_range constraints row_valid propertiesToAssume
  obtain ⟨ pa_exec, pa_mem, rest ⟩ := assertedProperties
  clear pa_exec rest
  simp [row_valid, and_assoc,
        VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_mem

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_bit

  simp only [propertiesToAssume,
             ReadInstructionBusEntryInstanceLt,
             Interaction.ReadInstructionBusEntryInstance,
             _readInstructionBus_row,
             readInstructionBus_row.eq_1] at pa_read
  simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil] at pa_read
  simp only [row_valid, Interaction.ReadInstructionBusEntry.deserialise] at pa_read
  simp at pa_read
  repeat rw [Fin.ext_iff] at pa_mem pa_range pa_read pa_bit
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2n_c, ub_rs2p_c, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2_non_imm, ri_imm ⟩ := pa_read
  obtain ⟨ ba0, ba1, ba2, ba3 ⟩ := pa_bit
  clear pa_exec pa_range

  -- Get all opcode properties
  obtain ⟨ sop0, sop1 ⟩ := single_op air row row_in_range constraints
  obtain ⟨ op0, op1 ⟩ := op_from_opcode air row row_in_range constraints row_valid
  have opcodes := opcode_bounds air row row_in_range constraints row_valid

  -- Get relevant constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_add, b_sub, b_is_valid, b_cmp_result, msb_b, msb_c,
           b_dm3, sum3_diff, dm3_diff, b_dm2, sum2_diff, dm2_diff,
           b_dm1, sum1_diff, dm1_diff, b_dm0, sum0_diff, dm0_diff,
           b_sum, sum0_cmp1, b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints
  clear constrain_interactions rest
  simp_all

  obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3 ⟩ :
     (air.core.c_0 row 0).val < 256 ∧
     (air.core.c_1 row 0).val < 256 ∧
     (air.core.c_2 row 0).val < 256 ∧
     (air.core.c_3 row 0).val < 256
  := by
    clear *- b_rs2_as rs2_as_imm imm_sign imm_sign_extend ub_rs2n_c ri_imm ba3
    rw [Fin.ext_iff] at *
    rcases b_rs2_as <;> simp_all
    . rw [← VmAirWrapper_lt.rs2_sign_limbs] at imm_sign
      grind

  grind

/-- From Lt opcode to RISC-V opcode -/
def rop_of_Lt_opcode (opcode : FBB) : rop :=
  if opcode = 520 then .SLT else .SLTU

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the
    two base Lt opcodes for:
    - the `b` operand read from memory; and
    - the `c` operand as per the circuit
--/
theorem spec_base_Lt
:
  U32.toBV #v[(air.core.cmp_result row 0).val, 0, 0, 0]
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
    (rop_of_Lt_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  have essentials := essentials _ air row row_in_range constraints row_valid propertiesToAssume
  simp [and_assoc] at essentials
  obtain ⟨ ub_cmp, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, opcodes, b_rs2_as, h_imm ⟩ := essentials

  -- Get all opcode properties
  obtain ⟨ sop0, sop1 ⟩ := single_op air row row_in_range constraints
  obtain ⟨ op0, op1 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  -- Prepare constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_add, b_sub, b_is_valid, b_cmp_result, msb_b, msb_c,
           b_dm3, sum3_diff, dm3_diff, b_dm2, sum2_diff, dm2_diff,
           b_dm1, sum1_diff, dm1_diff, b_dm0, sum0_diff, dm0_diff,
           b_sum, sum0_cmp1, rest ⟩ := constraints
  clear constrain_interactions rest

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  clear pa_exec pa_mem pa_range pa_read
  simp [row_valid, VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_bit
  obtain ⟨ ba0, ba1, ba2 ⟩ := pa_bit
  clear ba2

  simp [row_valid,
        ← LessThanCoreAir_4.prefix_sum_0_def,
        ← LessThanCoreAir_4.prefix_sum_1_def,
        ← LessThanCoreAir_4.prefix_sum_2_def,
        ← LessThanCoreAir_4.diff_def_0,
        ← LessThanCoreAir_4.diff_def_1,
        ← LessThanCoreAir_4.diff_def_2,
        ← LessThanCoreAir_4.diff_def_3] at *
  repeat rw [sub_eq_zero] at *
  simp_all

  have impossible : 2 * (air.core.cmp_result row 0) = 1 ↔ False := by
    clear *- b_cmp_result
    grind
  simp_all

  -- Branch on opcode
  rcases opcodes with is_slt | is_sltu
  all_goals
    simp_all [execute_RTYPE_pure, rop_of_Lt_opcode]
    simp [← BitVec.toNat_inj, U32.toNat]
    repeat rw [Nat.mod_eq_of_lt (by omega)]

  -- SLT
  . simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide]
    repeat rw [Nat.mod_eq_of_lt (by omega)]
    rcases b_sum with h_sum | h_sum <;> simp_all
    . -- All bytes are the same
      have ⟨ h_dm3, h_dm2, h_dm1, h_dm0 ⟩ :
        air.core.diff_marker_3 row 0 = 0 ∧ air.core.diff_marker_2 row 0 = 0 ∧
        air.core.diff_marker_1 row 0 = 0 ∧ air.core.diff_marker_0 row 0 = 0
        := by clear *- b_dm0 b_dm1 b_dm2 b_dm3 h_sum; grind
      rw [if_neg] <;> simp_all
      split_ifs <;> simp_all <;> grind
    . -- One byte differs
      -- Establish what the msb variables actually are
      have eq_msb_b : air.core.b_msb_f row 0 = if 128 ≤ (air.core.b_3 row 0).val then (air.core.b_3 row 0) - 256 else (air.core.b_3 row 0)
        := by clear *- ub_b3 msb_b ba0; split_ifs <;> grind
      have eq_msb_c : air.core.c_msb_f row 0 = if 128 ≤ (air.core.c_3 row 0).val then air.core.c_3 row 0 - 256 else air.core.c_3 row 0
        := by clear *- ub_c3 msb_c ba0; split_ifs <;> grind

      -- Branch on the non-negativity of `b` and `c`
      by_cases b_neg : 128 ≤ (air.core.b_3 row 0).val <;>
      by_cases c_neg : 128 ≤ (air.core.c_3 row 0).val <;> simp_all
      -- Both negative
      . simp_all [U32.toNat]
        rcases b_dm3 with h_dm3 | h_dm3 <;>
        rcases b_dm2 with h_dm2 | h_dm2 <;>
        rcases b_dm1 with h_dm1 | h_dm1 <;>
        rcases b_cmp_result <;> simp_all <;> split_ifs <;> try grind
      -- `b` negative, `c` positive, result always `0`
      . rw [if_pos] <;> [ simp; skip ]
        . rcases b_cmp_result <;> simp_all
          rcases b_dm3 <;> simp_all <;> grind
        . rw [if_neg (by omega)]
          grind
      -- `c` negative, `b` positive, result always `1`
      . rw [if_neg] <;> [ simp; skip ]
        . rcases b_cmp_result <;> simp_all
          rcases b_dm3 <;> simp_all <;> grind
        . rw [if_neg (by omega)]
          grind
      -- `b` anc `c` positive, effectively the SLTU case
      . rw [if_neg (c := 128 ≤ (air.core.c_3 row 0).val)] <;> [ skip; omega ]
        simp_all [U32.toNat]
        rcases b_dm3 with h_dm3 | h_dm3 <;>
        rcases b_dm2 with h_dm2 | h_dm2 <;>
        rcases b_dm1 with h_dm1 | h_dm1 <;>
        rcases b_cmp_result <;> simp_all <;> split_ifs <;> grind

  -- SLTU
  . -- msbs collapse
    have ⟨ eq_msb_b, eq_msb_c ⟩ : air.core.b_msb_f row 0 = air.core.b_3 row 0 ∧ air.core.c_msb_f row 0 = air.core.c_3 row 0
      := by clear *- ub_b3 ub_c3 msb_b msb_c ba0; grind
    simp_all
    rcases b_sum with h_sum | h_sum <;> simp_all
    . -- All bytes are the same
      have ⟨ h_dm3, h_dm2, h_dm1, h_dm0 ⟩ :
        air.core.diff_marker_3 row 0 = 0 ∧ air.core.diff_marker_2 row 0 = 0 ∧
        air.core.diff_marker_1 row 0 = 0 ∧ air.core.diff_marker_0 row 0 = 0
        := by clear *- b_dm0 b_dm1 b_dm2 b_dm3 h_sum; grind
      simp_all
    . -- Case analysis on the byte that differs and the outcome
      rcases b_dm3 with h_dm3 | h_dm3 <;>
      rcases b_dm2 with h_dm2 | h_dm2 <;>
      rcases b_dm1 with h_dm1 | h_dm1 <;>
      rcases b_cmp_result <;> simp_all <;> split_ifs <;> grind

end General

section NonImmediate

include
  row_valid
  constraints
  propertiesToAssume in
/-- The non-immediate variants of the five base ALU opcodes
    are implemented as per the RISC-V spec -/
theorem spec_base_Lt_non_imm
  (_ : air.adapter.rs2_as row 0 = 1)
:
  U32.toBV #v[(air.core.cmp_result row 0).val, 0, 0, 0]
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
    (rop_of_Lt_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  apply spec_base_Lt <;> assumption

end NonImmediate

section Immediate

/-- From Lt opcode to RISC-V opcode -/
def iop_of_Lt_opcode (opcode : FBB) : iop :=
  if opcode = 520 then .SLTI else .SLTIU

include
  row_valid
  constraints
  propertiesToAssume in
/-- The immediate variants of the five base ALU opcodes
    are implemented as per the RISC-V spec -/
theorem spec_base_ALU_imm
  (h_imm : air.adapter.rs2_as row 0 = 0)
:
  U32.toBV #v[(air.core.cmp_result row 0).val, 0, 0, 0]
    =
  execute_ITYPE_pure
    (BitVec.ofNat 12 (air.adapter.rs2 row 0).val)
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (iop_of_Lt_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  have propertiesToAssume' := propertiesToAssume
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume'
  clear pa_exec pa_mem pa_range pa_bit

  simp only [VmAirWrapper_lt.constraints.propertiesToAssume,
             ReadInstructionBusEntryInstanceLt,
             Interaction.ReadInstructionBusEntryInstance,
             _readInstructionBus_row,
             readInstructionBus_row.eq_1] at pa_read
  simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil] at pa_read
  simp only [row_valid, Interaction.ReadInstructionBusEntry.deserialise] at pa_read
  simp at pa_read
  repeat rw [Fin.ext_iff] at pa_read
  simp at pa_read
  obtain ⟨ ri_rd, ri_rs1, ri_rs2_non_imm, ri_imm ⟩ := pa_read

  suffices eq_c
  : U32.toBV #v[(air.core.c_0 row 0).val,
                (air.core.c_1 row 0).val,
                (air.core.c_2 row 0).val,
                (air.core.c_3 row 0).val]
      = BitVec.signExtend 32 (BitVec.ofNat 12 (air.adapter.rs2 row 0).val)
  . trans execute_RTYPE_pure
            (U32.toBV #v[(air.core.b_0 row 0).val,
                         (air.core.b_1 row 0).val,
                         (air.core.b_2 row 0).val,
                         (air.core.b_3 row 0).val])
            (U32.toBV #v[(air.core.c_0 row 0).val,
                         (air.core.c_1 row 0).val,
                         (air.core.c_2 row 0).val,
                         (air.core.c_3 row 0).val])
            (rop_of_Lt_opcode (air.core.ctx row 0).instruction.opcode)
    . apply spec_base_Lt <;> assumption
    . simp [execute_ITYPE_pure]
      rw [← eq_c]; congr

      have opcodes := opcode_bounds air row row_in_range constraints row_valid
      simp [rop_of_Lt_opcode, iop_of_Lt_opcode]
      grind
  . simp [*, ← BitVec.toInt_inj]
    trans (BitVec.ofNat 24 (air.adapter.rs2 row 0).val).toInt
    . have essentials := essentials _ air row row_in_range constraints row_valid propertiesToAssume
      simp [h_imm, and_assoc] at essentials
      obtain ⟨ ub_cmp, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
               opcodes, h_rs2, imm_sign_extend, rs2_as_imm, imm_sign, imm_sign_extend' ⟩ := essentials
      rw [← VmAirWrapper_lt.rs2_imm_def] at rs2_as_imm
      rw [← VmAirWrapper_lt.rs2_sign_limbs] at imm_sign
      simp [rs2_as_imm, Fin.val_add, Fin.val_mul]
      rw [← imm_sign,
          Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      simp [U32.toInt, BitVec.toInt, U32.negative, U32.toNat]
      rcases imm_sign_extend' with h_pos | h_neg
      . rw [h_pos]
        rw [if_neg (by omega)]
        rw [if_pos (by omega)]
        omega
      . rw [h_neg]
        rw [if_pos (by omega)]
        rw [if_neg (by omega)]
        iterate 2 rw [Int.emod_eq_of_lt (by simp) (by omega)]
        omega
    . rw [BitVec.toInt_signExtend_of_le (by simp)]
      grind

end Immediate

end Lt.ValidRows
