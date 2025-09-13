import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Constraints.VmAirWrapper_alu
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_alu FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_alu.constraints.allHold air row row_in_range)

namespace ALU.NonValidRows

open VmAirWrapper_alu.constraints

variable (row_not_valid : air.core.is_valid row 0 = 0)

include
  row_in_range
in
/-- Zeros required to form a non-valid row -/
lemma non_valid_row_ALU_allZeros_allHold
:
  constrain_interactions air ∧
  air.adapter.rs2 row 0 = 0 ∧
  air.adapter.rs2_as row 0 = 0 ∧
  air.core.c_0 row 0 = 0 ∧
  air.core.c_1 row 0 = 0 ∧
  air.core.c_2 row 0 = 0 ∧
  air.core.c_3 row 0 = 0 ∧
  air.core.opcode_add_flag row 0 = 0 ∧
  air.core.opcode_sub_flag row 0 = 0 ∧
  air.core.opcode_xor_flag row 0 = 0 ∧
  air.core.opcode_or_flag row 0 = 0 ∧
  air.core.opcode_and_flag row 0 = 0
    → air.core.is_valid row 0 = 0 ∧
      allHold air row row_in_range
:= by
  rw [allHold_simplified_of_allHold]
  simp_all; intro hint h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [VmAirWrapper_alu_constraint_and_interaction_simplification]
  simp [← BaseAluCoreAir.is_valid_def,
        ← VmAirWrapper_alu.rs2_imm_def,
        ← VmAirWrapper_alu.rs2_sign_limbs]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  split_ands <;> (try decide) <;> simp

include
  row_in_range
  row_not_valid
  constraints
in
/-- On non-valid rows, all interactin multiplicities equal zero -/
lemma non_valid_row_ALU_all_interaction_multiplicities_zero
:
  forall entry,
  entry ∈ serialiseRow air row → entry.1 = 0
:= by
  have : air.adapter.rs2_as row 0 = 0 := by
    obtain ⟨ hint, constraints ⟩ := constraints
    clear hint; unfold extracted_row_constraint_list at constraints
    simp only [VmAirWrapper_alu_air_simplification,
               VmAirWrapper_alu_constraint_and_interaction_simplification] at constraints
    simp at constraints
    grind
  clear constraints
  simp_all [VmAirWrapper_alu_constraint_and_interaction_simplification]

end ALU.NonValidRows

open VmAirWrapper_alu.constraints

namespace ALU.ValidRows

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
  simp [row_valid, VmAirWrapper_alu_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read pa_bit
  repeat rw [Fin.ext_iff] at pa_mem pa_range pa_read pa_bit
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2n_c, ub_rs2p_c, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2_non_imm, ri_imm ⟩ := pa_read
  obtain ⟨ ba00, ba01, ba02, ba10, ba11, ba12, ba20, ba21, ba22, ba30, ba31, ba32, ba4 ⟩ := pa_bit
  clear pa_exec pa_range

  have ⟨ sop0, sop1, sop2, sop3, sop4 ⟩ := single_op air row row_in_range constraints
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_alu_constraint_and_interaction_simplification] at *
  obtain ⟨ constrain_interactions,
          b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
          add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
          b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend,
          rest ⟩ := constraints
  clear constrain_interactions rest

  simp_all

  constructor
  . rcases b_rs2_as <;> simp_all
  . constructor
    . rcases b_rs2_as <;> simp_all
      rw [Fin.ext_iff] at *; simp_all
    . clear *- b_add b_sub b_xor b_or b_and
              ba00 ba01 ba02 ba10 ba11 ba12 ba20 ba21 ba22 ba30 ba31 ba32
              sop0 sop1 sop2 sop3 sop4

      rcases b_add <;> [ skip; simp_all ]
      rcases b_sub <;> [ skip; simp_all ]
      rcases b_xor <;> rcases b_and <;> rcases b_or <;> simp_all
      all_goals
        simp [← BaseAluCoreAir.x_xor_y_0_def, ← BaseAluCoreAir.x_xor_y_1_def,
              ← BaseAluCoreAir.x_xor_y_2_def, ← BaseAluCoreAir.x_xor_y_3_def,
              ← BaseAluCoreAir.x_0_def, ← BaseAluCoreAir.x_1_def,
              ← BaseAluCoreAir.x_2_def, ← BaseAluCoreAir.x_3_def,
              ← BaseAluCoreAir.y_0_def, ← BaseAluCoreAir.y_1_def,
              ← BaseAluCoreAir.y_2_def, ← BaseAluCoreAir.y_3_def] at *

        simp_all

      . have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba00 ba01 ba02
        have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba10 ba11 ba12
        have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba20 ba21 ba22
        have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba30 ba31 ba32
        grind

      . have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba00 ba01 ba02
        have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba10 ba11 ba12
        have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba20 ba21 ba22
        have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba30 ba31 ba32
        grind

      . split_ands
        all_goals
          apply Nat.xor_lt_two_pow (n := 8) <;>
          omega

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
  ((air.core.ctx row 0).instruction.opcode = 512 ∨
   (air.core.ctx row 0).instruction.opcode = 513 ∨
   (air.core.ctx row 0).instruction.opcode = 514 ∨
   (air.core.ctx row 0).instruction.opcode = 515 ∨
   (air.core.ctx row 0).instruction.opcode = 516) ∧
  ((air.adapter.rs2_as row 0).val = 0 →
    ¬(air.core.ctx row 0).instruction.opcode = 513 ∧
    (air.adapter.rs2 row 0).val < 16777216 ∧
    (BitVec.ofNat 24 (air.adapter.rs2 row 0).val).toInt = (BitVec.ofNat 12 (air.adapter.rs2 row 0).val).toInt)
:= by
  have assertedProperties := wf_propertiesToAssert _ air row row_in_range constraints row_valid propertiesToAssume
  obtain ⟨ pa_exec, pa_mem, rest ⟩ := assertedProperties
  simp [row_valid, and_assoc,
        VmAirWrapper_alu_constraint_and_interaction_simplification] at pa_mem
  obtain ⟨ x0, ub_b0, ub_b1, ub_b2, ub_b3, x1, ub_c_imm, x2, ub_a0, ub_a1, ub_a2, ub_a3 ⟩ := pa_mem

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_alu_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read pa_bit
  repeat rw [Fin.ext_iff] at pa_mem pa_range pa_read pa_bit
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2n_c, ub_rs2p_c, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2_non_imm, ri_imm ⟩ := pa_read
  obtain ⟨ ba00, ba01, ba02, ba10, ba11, ba12, ba20, ba21, ba22, ba30, ba31, ba32, ba4 ⟩ := pa_bit

  -- Get all opcode properties
  obtain ⟨ sop0, sop1, sop2, sop3, sop4 ⟩ := single_op air row row_in_range constraints
  obtain ⟨ op0, op1, op2, op3, op4 ⟩ := op_from_opcode air row row_in_range constraints row_valid
  have opcodes := opcode_bounds air row row_in_range constraints row_valid

  rw [allHold_simplified_of_allHold] at constraints
  obtain ⟨ constrain_interactions,
           b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints
  clear constrain_interactions rest
  simp [row_valid, VmAirWrapper_alu_constraint_and_interaction_simplification] at *

  obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3 ⟩ :
     (air.core.c_0 row 0).val < 256 ∧
     (air.core.c_1 row 0).val < 256 ∧
     (air.core.c_2 row 0).val < 256 ∧
     (air.core.c_3 row 0).val < 256
  := by
    clear *- b_rs2_as rs2_as_imm imm_sign imm_sign_extend ub_rs2n_c ri_imm b_rs2_as ba4
    rw [Fin.ext_iff] at *
    rcases b_rs2_as <;> simp_all
    . rw [← VmAirWrapper_alu.rs2_sign_limbs] at imm_sign
      grind

  grind

/-- From ALU opcode to RISC-V opcode -/
def rop_of_ALU_opcode (opcode : FBB) : rop :=
  if opcode = 512 then .ADD else
  if opcode = 513 then .SUB else
  if opcode = 514 then .XOR else
  if opcode = 515 then .OR else .AND

include
  row_valid
  constraints
  propertiesToAssume in
/-- The constraints entail correct implementation of the
    five base ALU opcodes for:
    - the `b` operand read from memory; and
    - the `c` operand as per the circuit
--/
theorem spec_base_ALU
:
  U32.toBV #v[(air.core.a_0 row 0).val,
              (air.core.a_1 row 0).val,
              (air.core.a_2 row 0).val,
              (air.core.a_3 row 0).val]
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
    (rop_of_ALU_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  -- Get relevant previous info
  have assertedProperties := wf_propertiesToAssert _ air row row_in_range constraints row_valid propertiesToAssume
  obtain ⟨ pa_exec, pa_mem, rest ⟩ := assertedProperties
  simp [row_valid, and_assoc,
        VmAirWrapper_alu_constraint_and_interaction_simplification] at pa_mem
  obtain ⟨ x0, ub_b0, ub_b1, ub_b2, ub_b3, x1, ub_c_imm, x2, ub_a0, ub_a1, ub_a2, ub_a3 ⟩ := pa_mem
  clear pa_exec x0 x1 x2 rest

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  simp [row_valid, VmAirWrapper_alu_constraint_and_interaction_simplification] at pa_exec pa_mem pa_range pa_read pa_bit
  repeat rw [Fin.ext_iff] at pa_mem pa_range pa_read pa_bit
  simp [and_assoc] at pa_mem pa_range pa_read pa_bit
  obtain ⟨ ub_rs1, ub_b0, ub_b1, ub_b2, ub_b3, ub_rs2n_c, ub_rs2p_c, ub_rd, rm00, rm01, rm02, rm03 ⟩ := pa_mem
  obtain ⟨ ri_rd, ri_rs1, ri_rs2_non_imm, ri_imm ⟩ := pa_read
  obtain ⟨ ba00, ba01, ba02, ba10, ba11, ba12, ba20, ba21, ba22, ba30, ba31, ba32, ba4 ⟩ := pa_bit
  clear pa_exec pa_range

  -- Get all opcode properties
  obtain ⟨ sop0, sop1, sop2, sop3, sop4 ⟩ := single_op air row row_in_range constraints
  obtain ⟨ op0, op1, op2, op3, op4 ⟩ := op_from_opcode air row row_in_range constraints row_valid
  have opcodes := opcode_bounds air row row_in_range constraints row_valid

  -- Prepare constraints
  rw [allHold_simplified_of_allHold] at constraints
  obtain ⟨ constrain_interactions,
           b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints
  clear constrain_interactions rest
  simp [VmAirWrapper_alu_constraint_and_interaction_simplification] at *

  obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3 ⟩ :
     (air.core.c_0 row 0).val < 256 ∧
     (air.core.c_1 row 0).val < 256 ∧
     (air.core.c_2 row 0).val < 256 ∧
     (air.core.c_3 row 0).val < 256
  := by
    clear *- b_rs2_as rs2_as_imm imm_sign imm_sign_extend ub_rs2n_c ri_imm b_rs2_as ba4
    rw [Fin.ext_iff] at *
    rcases b_rs2_as <;> simp_all
    . rw [← VmAirWrapper_alu.rs2_sign_limbs] at imm_sign
      grind

    -- Branch on opcode
  rcases opcodes with is_add | is_sub | is_xor | is_or | is_and <;>
  simp_all [execute_RTYPE_pure, rop_of_ALU_opcode]

  -- ADD
  . -- Open the carries
    rw [← BaseAluCoreAir.carry_add_3_def,
        ← BaseAluCoreAir.carry_add_2_def,
        ← BaseAluCoreAir.carry_add_1_def,
        ← BaseAluCoreAir.carry_add_0_def] at *

    -- And prove
    simp_all [← BitVec.toNat_inj, U32.toBV_toNat, U32.toNat]
    clear *- add_0 add_1 add_2 add_3 ub_a0 ub_a1 ub_a2 ub_a3
             ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
    rcases add_0 <;> rcases add_1 <;>
    rcases add_2 <;> rcases add_3 <;>
    simp_all <;> omega

  -- SUB
  . -- Open the carries
    rw [← BaseAluCoreAir.carry_sub_3_def,
      ← BaseAluCoreAir.carry_sub_2_def,
      ← BaseAluCoreAir.carry_sub_1_def,
      ← BaseAluCoreAir.carry_sub_0_def] at *

    -- And prove
    simp_all [← BitVec.toNat_inj, U32.toBV_toNat, U32.toNat]
    clear *- sub_0 sub_1 sub_2 sub_3 ub_a0 ub_a1 ub_a2 ub_a3
             ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
    rcases sub_0 <;> rcases sub_1 <;>
    rcases sub_2 <;> rcases sub_3 <;>
    simp_all <;> omega

  -- Bitwise
  all_goals
    simp [← BaseAluCoreAir.x_0_def, ← BaseAluCoreAir.x_1_def,
          ← BaseAluCoreAir.x_2_def, ← BaseAluCoreAir.x_3_def,
          ← BaseAluCoreAir.y_0_def, ← BaseAluCoreAir.y_1_def,
          ← BaseAluCoreAir.y_2_def, ← BaseAluCoreAir.y_3_def,
          ← BaseAluCoreAir.x_xor_y_0_def, ← BaseAluCoreAir.x_xor_y_1_def,
          ← BaseAluCoreAir.x_xor_y_2_def, ← BaseAluCoreAir.x_xor_y_3_def] at *
    simp_all [U32.toBV]

  -- XOR
  . repeat rw [BitVec.xor_append, BitVec.append_eq_append_eql]
    simp

  -- OR
  . repeat rw [BitVec.or_append, BitVec.append_eq_append_eql]
    simp_all [← BitVec.toNat_inj]

    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ub_b0 ub_c0 ba02
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ub_b1 ub_c1 ba12
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ub_b2 ub_c2 ba22
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ub_b3 ub_c3 ba32
    repeat rw [Nat.mod_eq_of_lt (by omega)]
    simp_all

  -- AND
  . repeat rw [BitVec.and_append, BitVec.append_eq_append_eql]
    simp_all [← BitVec.toNat_inj]

    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ub_b0 ub_c0 ba02
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ub_b1 ub_c1 ba12
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ub_b2 ub_c2 ba22
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ub_b3 ub_c3 ba32
    repeat rw [Nat.mod_eq_of_lt (by omega)]
    simp_all

end General

section NonImmediate

include
  row_valid
  constraints
  propertiesToAssume in
/-- The non-immediate variants of the five base ALU opcodes
    are implemented as per the RISC-V spec -/
theorem spec_base_ALU_non_imm
  (_ : air.adapter.rs2_as row 0 = 1)
:
  U32.toBV #v[(air.core.a_0 row 0).val,
              (air.core.a_1 row 0).val,
              (air.core.a_2 row 0).val,
              (air.core.a_3 row 0).val]
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
    (rop_of_ALU_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  apply spec_base_ALU <;> assumption

end NonImmediate

section Immediate

/-- From ALU opcode to RISC-V opcode -/
def iop_of_ALU_opcode (opcode : FBB) : iop :=
  if opcode = 512 then .ADDI else
  if opcode = 514 then .XORI else
  if opcode = 515 then .ORI else .ANDI

include
  row_valid
  constraints
  propertiesToAssume in
/-- The immediate variants of the five base ALU opcodes
    are implemented as per the RISC-V spec -/
theorem spec_base_ALU_imm
  (h_imm : air.adapter.rs2_as row 0 = 0)
:
  U32.toBV #v[(air.core.a_0 row 0).val,
              (air.core.a_1 row 0).val,
              (air.core.a_2 row 0).val,
              (air.core.a_3 row 0).val]
    =
  execute_ITYPE_pure
    (BitVec.ofNat 12 (air.adapter.rs2 row 0).val)
    (U32.toBV #v[(air.core.b_0 row 0).val,
                 (air.core.b_1 row 0).val,
                 (air.core.b_2 row 0).val,
                 (air.core.b_3 row 0).val])
    (iop_of_ALU_opcode (air.core.ctx row 0).instruction.opcode)
:= by
  have propertiesToAssume' := propertiesToAssume
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume'
  clear pa_exec pa_mem pa_range pa_bit
  simp [row_valid, VmAirWrapper_alu_constraint_and_interaction_simplification] at pa_read
  repeat rw [Fin.ext_iff] at pa_read
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
            (rop_of_ALU_opcode (air.core.ctx row 0).instruction.opcode)
    . apply spec_base_ALU <;> assumption
    . simp [execute_ITYPE_pure]
      rw [← eq_c]; congr

      obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
      clear pa_exec pa_mem pa_range pa_bit
      simp [row_valid, VmAirWrapper_alu_constraint_and_interaction_simplification] at pa_read
      repeat rw [Fin.ext_iff] at pa_read
      obtain ⟨ ri_rd, ri_rs1, ri_rs2_non_imm, ri_imm ⟩ := pa_read

      have opcodes := opcode_bounds air row row_in_range constraints row_valid
      simp [rop_of_ALU_opcode, iop_of_ALU_opcode]
      grind
  . simp [*, ← BitVec.toInt_inj]
    trans (BitVec.ofNat 24 (air.adapter.rs2 row 0).val).toInt
    . have essentials := essentials _ air row row_in_range constraints row_valid propertiesToAssume
      simp [h_imm, and_assoc] at essentials
      obtain ⟨ ub_a0, ub_a1, ub_a2, ub_a3, ub_b0, ub_b1, ub_b2, ub_b3, ub_c0, ub_c1, ub_c2, ub_c3,
               opcodes, opcode_not_sub, h_rs2, imm_sign_extend ⟩ := essentials
      rw [allHold_simplified_of_allHold] at constraints
      obtain ⟨ constrain_interactions,
           b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints
      clear constrain_interactions rest
      simp [h_imm, VmAirWrapper_alu_constraint_and_interaction_simplification] at *
      rw [← VmAirWrapper_alu.rs2_imm_def] at rs2_as_imm
      rw [← VmAirWrapper_alu.rs2_sign_limbs] at imm_sign
      simp [rs2_as_imm, Fin.val_add, Fin.val_mul]
      rw [← imm_sign,
          Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      simp [U32.toInt, BitVec.toInt, U32.negative, U32.toNat]
      rcases imm_sign_extend with h_pos | h_neg
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

end ALU.ValidRows
