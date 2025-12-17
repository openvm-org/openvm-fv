import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_lt
import OpenvmFv.Constraints.VmAirWrapper_lt
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_lt FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_lt.constraints.allHold air row row_in_range)

namespace Lt.NonValidRows

open VmAirWrapper_lt.constraints

variable (row_not_valid : (executionBus_row air row)[0]!.1 = 0)

include
  row_not_valid
  constraints
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
  have : air.adapter.rs2_as row 0 = 0 := by
    obtain ⟨ hint, constraints ⟩ := constraints
    clear hint; unfold extracted_row_constraint_list at constraints
    simp only [VmAirWrapper_lt_air_simplification,
               VmAirWrapper_lt_constraint_and_interaction_simplification] at constraints
    simp at constraints
    simp [executionBus_row] at row_not_valid
    grind
  clear constraints
  simp_all [VmAirWrapper_lt_constraint_and_interaction_simplification]

end Lt.NonValidRows

open VmAirWrapper_lt.constraints

namespace Lt.ValidRows

variable (row_valid : air.core.is_valid row 0 = 1)

-- Row axioms, properties to assume, and properties to prove
variable
  (axioms : axiomsPerRow air row)
  (propertiesToAssume : wf_propertiesToAssumePerRow air row)

section General

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
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read pa_bit

  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := programBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_read

  repeat rw [Fin.ext_iff] at pa_mem pa_range pa_read pa_bit
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2n_c, ub_rs2p_c, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ba0, ba1, ba2, ba3 ⟩ := pa_bit
  clear pa_range

  have ⟨ sop0, sop1 ⟩ := single_op air row row_in_range constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_slt, b_sltu, b_is_valid, b_cmp_result, msb_b, msb_c,
           b_dm3, sum3_diff, dm3_diff, b_dm2, sum2_diff, dm2_diff,
           b_dm1, sum1_diff, dm1_diff, b_dm0, sum0_diff, dm0_diff,
           b_sum, sum0_cmp1, b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints
  clear constrain_interactions rest
  simp_all

  have : (air.core.cmp_result row 0).val < 256 :=
    by rcases b_cmp_result <;> simp_all

  simp [Fin.ext_iff] at ub_rs2n_c

  rcases b_rs2_as <;>
  simp_all [VmAirWrapper_lt_constraint_and_interaction_simplification] <;>
  grind

include
  row_valid
  constraints
  axioms
  propertiesToAssume
in
/-- Some properties more important than others that should
    be easily accessible -/
lemma essentials
:
  (air.adapter.from_state.pc row 0).val + 4 < 1073741824 ∧
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
  have assertedProperties := wf_propertiesToAssert _ air row row_in_range constraints row_valid axioms propertiesToAssume
  obtain ⟨ pa_exec, pa_mem, rest ⟩ := assertedProperties
  clear pa_exec rest
  simp [row_valid, and_assoc,
        VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_mem

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read pa_bit

  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := programBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_read

  repeat rw [Fin.ext_iff] at pa_mem pa_range pa_read pa_bit
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2n_c, ub_rs2p_c, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
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
           b_slt, b_sltu, b_is_valid, b_cmp_result, msb_b, msb_c,
           b_dm3, sum3_diff, dm3_diff, b_dm2, sum2_diff, dm2_diff,
           b_dm1, sum1_diff, dm1_diff, b_dm0, sum0_diff, dm0_diff,
           b_sum, sum0_cmp1, b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints
  clear constrain_interactions rest
  simp_all

  simp [row_valid, VmAirWrapper_lt_constraint_and_interaction_simplification] at *

  obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3 ⟩ :
     (air.core.c_0 row 0).val < 256 ∧
     (air.core.c_1 row 0).val < 256 ∧
     (air.core.c_2 row 0).val < 256 ∧
     (air.core.c_3 row 0).val < 256
  := by
    clear *- b_rs2_as rs2_as_imm imm_sign imm_sign_extend ub_rs2n_c pa_read ba3
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
  axioms
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
  have essentials := essentials _ air row row_in_range constraints row_valid axioms propertiesToAssume
  simp [and_assoc] at essentials
  obtain ⟨ ub_pc, ub_cmp, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3, opcodes, b_rs2_as, h_imm ⟩ := essentials

  -- Get all opcode properties
  obtain ⟨ sop0, sop1 ⟩ := single_op air row row_in_range constraints
  obtain ⟨ op0, op1 ⟩ := op_from_opcode air row row_in_range constraints row_valid

  -- Prepare constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification] at constraints
  obtain ⟨ constrain_interactions,
           b_slt, b_sltu, b_is_valid, b_cmp_result, msb_b, msb_c,
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
  repeat rw [sub_eq_zero] at sum0_diff sum1_diff sum2_diff sum3_diff
  simp_all

  have impossible : 2 * (air.core.cmp_result row 0) = 1 ↔ False := by
    clear *- b_cmp_result
    grind
  simp_all

  have h_lt :=
    @BabyBear.Circuits.less_than
     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
     ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
     b_cmp_result msb_b msb_c
     b_dm0 b_dm1 b_dm2 b_dm3 b_sum
     dm3_diff dm2_diff dm1_diff dm0_diff
     sum0_cmp1
     sum3_diff sum2_diff sum1_diff sum0_diff
     ba0.1 ba0.2 ba1

  -- Branch on opcode
  rcases opcodes with h_opcode | h_opcode <;>
  [
    (specialize op0 h_opcode; simp [op0] at *);
    (specialize op1 h_opcode; simp [op1, sop1] at *)
  ]
  all_goals
    simp [execute_RTYPE_pure, rop_of_Lt_opcode, h_opcode]
    simp [← BitVec.toNat_inj, BitVec.ofNat]
    split_ifs at h_lt with h_is_lt <;>
    [ rw [if_pos (by simpa)]; rw [if_neg (by aesop)] ] <;>
    simp [U32.toNat, ← h_lt]

end General

section NonImmediate

include
  row_valid
  constraints
  axioms
  propertiesToAssume in
/-- The non-immediate variants of the five base Lt opcodes
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
  axioms
  propertiesToAssume in
/-- The immediate variants of the five base Lt opcodes
    are implemented as per the RISC-V spec -/
theorem spec_base_Lt_imm
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

  simp [row_valid, VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_read
  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  replace pa_read := programBus_properties_of_opcode_bounds _ opcodes pa_read
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification] at pa_read
  repeat rw [Fin.ext_iff] at pa_read
  simp at pa_read

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
      rw [← eq_c]

      have opcodes := opcode_bounds air row row_in_range constraints row_valid
      simp [rop_of_Lt_opcode, iop_of_Lt_opcode]
      grind
  . simp [*, ← BitVec.toInt_inj]
    trans (BitVec.ofNat 24 (air.adapter.rs2 row 0).val).toInt
    . have essentials := essentials _ air row row_in_range constraints row_valid axioms propertiesToAssume
      simp [h_imm, and_assoc] at essentials
      obtain ⟨ ub_pc, ub_cmp, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
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
