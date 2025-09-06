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
  -- TODO: What does it mean that these additional constraints have to be here?
  (_ : air.core.diff_marker_0 row 0 = 0)
  (_ : air.core.diff_marker_1 row 0 = 0)
  (_ : air.core.diff_marker_2 row 0 = 0)
  (_ : air.core.diff_marker_3 row 0 = 0)
:
  forall entry,
  entry ∈ executionBus_row air row ++
          memoryBus_row air row ++
          rangeBus_row air row ++
          readInstructionBus_row air row ++
          bitwiseBus_row air row → entry.1 = 0
:= by
  have : air.adapter.rs2_as row 0 = 0 := by
    obtain ⟨ hint, constraints ⟩ := constraints
    clear hint; unfold extracted_row_constraint_list at constraints
    simp only [VmAirWrapper_lt_air_simplification,
               VmAirWrapper_lt_constraint_and_interaction_simplification] at constraints
    simp at constraints
    grind
  clear constraints
  simp_all [VmAirWrapper_lt_constraint_and_interaction_simplification]
  simp_all [← LessThanCoreAir_4.prefix_sum_0_def,
            ← LessThanCoreAir_4.prefix_sum_1_def,
            ← LessThanCoreAir_4.prefix_sum_2_def]

end Lt.NonValidRows

open VmAirWrapper_lt.constraints

namespace Lt.ValidRows

variable (row_valid : air.core.is_valid row 0 = 1)

-- Execution bus is balanced
variable
  {start_pc start_timestamp mul00 mul01 end_pc end_timestamp}
  (exec_bus_balance :
  InteractionList.balanced_by_ordered
    (executionBus_row air row)
    [
      Interaction.executionBus_entry mul00 start_pc start_timestamp,
      Interaction.executionBus_entry mul01 end_pc end_timestamp,
    ]
  )
-- Execution bus assumptions
variable
  (exec_bus_assumptions :
    Interaction.executionBus_assumptions mul01 end_pc end_timestamp
  )

-- Memory bus is balanced
variable
  {mul10 as0 r0 b0' b1' b2' b3' t0 mul11 as1 r1 b0 b1 b2 b3 t1 mul12 as2 r2 c0' c1' c2' c3' t2 mul13 as3 r3 c0 c1 c2 c3 t3 mul14 as4 d0' d1' d2' d3' t4 mul15 as5 r5 a0 a1 a2 a3 t5}
  (memory_bus_balance :
  InteractionList.balanced_by_ordered
    (memoryBus_row air row)
    [
      Interaction.memoryBus_entry mul10 as0 r0 b0' b1' b2' b3' t0,
      Interaction.memoryBus_entry mul11 as1 r1 b0  b1  b2  b3  t1,
      Interaction.memoryBus_entry mul12 as2 r2 c0' c1' c2' c3' t2,
      Interaction.memoryBus_entry mul13 as3 r3 c0  c1  c2  c3  t3,
      Interaction.memoryBus_entry mul14 as4 r3 d0' d1' d2' d3' t4,
      Interaction.memoryBus_entry mul15 as5 r5 a0  a1  a2  a3  t5
    ]
  )
-- Memory bus assumptions
variable
  (memory_bus_assumptions:
    Interaction.memoryBus_assumptions mul10 as0 r0 b0' b1' b2' b3' t0 ∧
    Interaction.memoryBus_assumptions mul12 as2 r2 c0' c1' c2' c3' t2 ∧
    Interaction.memoryBus_assumptions mul14 as4 r3 d0' d1' d2' d3' t4
  )

-- Range-checking bus is balanced
variable
  {mul20 v0 deg0 mul21 v1 deg1 mul22 v2 deg2 mul23 v3 deg3 mul24 deg4 mul25 v4 deg5}
  (range_bus_balance :
  InteractionList.balanced_by_ordered
    (rangeBus_row air row)
    [
      Interaction.rangeCheckerBus_entry mul20 v0 deg0,
      Interaction.rangeCheckerBus_entry mul21 v1 deg1,
      Interaction.rangeCheckerBus_entry mul22 v2 deg2,
      Interaction.rangeCheckerBus_entry mul23 v3 deg3,
      Interaction.rangeCheckerBus_entry mul24 v3 deg4,
      Interaction.rangeCheckerBus_entry mul25 v4 deg5
    ]
  )
-- Range-checking bus assumptions
variable
  (range_bus_assumptions:
    Interaction.rangeCheckerBus_assumptions mul20 v0 deg0 ∧
    Interaction.rangeCheckerBus_assumptions mul21 v1 deg1 ∧
    Interaction.rangeCheckerBus_assumptions mul22 v2 deg2 ∧
    Interaction.rangeCheckerBus_assumptions mul23 v3 deg3 ∧
    Interaction.rangeCheckerBus_assumptions mul24 v3 deg4 ∧
    Interaction.rangeCheckerBus_assumptions mul25 v4 deg5
  )

-- Read-instruction bus is balanced
variable
  {mul pc opcode rd rs1 rs2 xd rs2_as xf xg}
  (read_bus_balance :
  InteractionList.balanced_by_ordered
    (readInstructionBus_row air row)
    [
      Interaction.readInstructionBus_entry mul pc opcode rd rs1 rs2 xd rs2_as xf xg,
    ]
  )
-- Read-instruction bus assumptions
variable
  (read_bus_assumptions:
    Interaction.readInstructionBus_assumptions_Lt mul pc opcode rd rs1 rs2 xd rs2_as xf xg
  )

-- Bitwise bus is balanced
variable
  {mul40 x0 y0 z0 xor0 mul41 x1 y1 z1 xor1 mul42 x2 y2 z2 xor2 mul43 x3 y3 z3 xor3 mul44 x4 y4 z4 xor4}
  (bitwise_bus_balance :
  InteractionList.balanced_by_ordered
    (bitwiseBus_row air row)
    [
      Interaction.bitwiseBus_entry mul40 x0 y0 z0 xor0,
      Interaction.bitwiseBus_entry mul41 x1 y1 z1 xor1,
      Interaction.bitwiseBus_entry mul42 x2 y2 z2 xor2
    ]
  )
-- Bitwise bus assumptions
variable
  (bitwise_bus_assumptions:
    Interaction.bitwiseBus_assumptions mul40 x0 y0 z0 xor0 ∧
    Interaction.bitwiseBus_assumptions mul41 x1 y1 z1 xor1 ∧
    Interaction.bitwiseBus_assumptions mul42 x2 y2 z2 xor2
  )

section General

omit
  [Field ExtF]
in
include
  row_valid
  exec_bus_balance
in
/-- The `pc` and `timestamp` are as expected -/
lemma pc_and_timestamp
:
  end_pc = start_pc + 4 ∧
  end_timestamp = start_timestamp + 3
:= by
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
        InteractionList.balanced_by_ordered,
        Interaction.balances] at exec_bus_balance
  omega

omit
  [Field ExtF]
in
include
  row_valid
  memory_bus_balance
  memory_bus_assumptions in
/-- The `b` operand is range-constrained by bus balancing -/
lemma b_eq_and_range
:
  air.core.b_0 row 0 = b0 ∧ air.core.b_1 row 0 = b1 ∧ air.core.b_2 row 0 = b2 ∧ air.core.b_3 row 0 = b3 ∧
  b0.val < 256 ∧ b1.val < 256 ∧ b2.val < 256 ∧ b3.val < 256
:= by
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
        InteractionList.balanced_by_ordered,
        Interaction.balances] at memory_bus_balance
  simp [Interaction.memoryBus_assumptions] at memory_bus_assumptions
  obtain ⟨ m0, m1, m2 ⟩ := memory_bus_assumptions
  simp_all
  grind

include
  constraints
  row_valid
  memory_bus_balance
  memory_bus_assumptions
  read_bus_balance
  read_bus_assumptions
  bitwise_bus_balance
  bitwise_bus_assumptions in
/-- The `c` operand is:
    - range-constrained by bus balancing for non-immediate opcodes;
    - is read from memory for non-immediate opcodes; and
    - is a sign-extension of a 12-bit immediate for immediate opcodes -/
lemma c_eq_and_range
:
  (air.core.c_0 row 0).val < 256 ∧ (air.core.c_1 row 0).val < 256 ∧ (air.core.c_2 row 0).val < 256 ∧ (air.core.c_3 row 0).val < 256 ∧
  (air.adapter.rs2_as row 0 = 1 →
    air.core.c_0 row 0 = c0 ∧ air.core.c_1 row 0 = c1 ∧ air.core.c_2 row 0 = c2 ∧ air.core.c_3 row 0 = c3) ∧
  (air.adapter.rs2_as row 0 = 0 →
    U32.toBV #v[air.core.c_0 row 0,
                air.core.c_1 row 0,
                air.core.c_2 row 0,
                air.core.c_3 row 0]
      = BitVec.signExtend 32 (BitVec.ofNat 12 (air.adapter.rs2 row 0).val))
:= by
  rw [allHold_simplified_of_allHold] at constraints
  obtain ⟨ constrain_interactions,
           b_slt, b_sltu, b_is_valid,
           h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
           h10, h11, h12, h13, h14, h15, h16,
           b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints
  clear constrain_interactions
        h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
        rest
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification] at *

  simp [InteractionList.balanced_by_ordered,
        Interaction.balances] at memory_bus_balance
  simp [Interaction.memoryBus_assumptions] at memory_bus_assumptions
  obtain ⟨ mb0, mb1, mb2, mb3, mb4, mb5 ⟩ := memory_bus_balance
  obtain ⟨ m0, m1, m2 ⟩ :=  memory_bus_assumptions
  clear mb0 mb1 mb4 mb5 m0 m2

  simp [InteractionList.balanced_by_ordered,
        Interaction.balances] at bitwise_bus_balance
  simp [Interaction.bitwiseBus_assumptions] at bitwise_bus_assumptions

  simp [row_valid] at bitwise_bus_balance bitwise_bus_assumptions
  obtain ⟨ bb0, bb1, bb2 ⟩ := bitwise_bus_balance
  obtain ⟨ ba0, ba1, ba2 ⟩ := bitwise_bus_assumptions
  clear ba0 ba1

  have ⟨ ub_c0, ub_c1, ub_c2, ub_c3 ⟩
  :
    (air.core.c_0 row 0).val < 256 ∧ (air.core.c_1 row 0).val < 256 ∧
    (air.core.c_2 row 0).val < 256 ∧ (air.core.c_3 row 0).val < 256
  := by
    rcases b_rs2_as with eq_rs2_as_0 | eq_rs2_as_1 <;>
    (try rw [← VmAirWrapper_lt.rs2_sign_limbs] at imm_sign) <;>
    simp_all
    omega

  rcases b_rs2_as with eq_rs2_as_0 | eq_rs2_as_1
  . split_ands; rotate_right
    . simp [row_valid,
            InteractionList.balanced_by_ordered,
            Interaction.balances] at read_bus_balance
      obtain ⟨ eq_mul, eq_pc, eq_opcode, eq_rd, eq_rs1, eq_rs2,
              eq_xd, eq_rs2_as, eq_xf, eq_xg ⟩ := read_bus_balance
      clear eq_pc eq_rd eq_rs1 eq_xd eq_xf eq_xg
      simp [eq_rs2_as] at *

      simp [Interaction.readInstructionBus_assumptions_Lt,
            eq_mul, eq_rs2_as_0] at read_bus_assumptions
      obtain ⟨ reg_rd, reg_rs1,
              ⟨ ub_rs2, sign_extend_rs2 ⟩,
              eq_xd, eq_xf, eq_xg ⟩ := read_bus_assumptions
      clear reg_rd reg_rs1 eq_xd eq_xf eq_xg bb2
      simp [*, ← BitVec.toInt_inj]
      trans (BitVec.signExtend 32 (BitVec.ofNat 24 ↑rs2)).toInt
      . rw [BitVec.toInt_signExtend_of_le (by simp)]
        simp [eq_rs2_as_0, eq_rs2] at *
        rw [← VmAirWrapper_lt.rs2_imm_def] at rs2_as_imm
        rw [← VmAirWrapper_lt.rs2_sign_limbs] at imm_sign
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
      . iterate 2 rw [BitVec.toInt_signExtend_of_le (by simp)]
        assumption

    all_goals
      simp_all

  . simp_all

include
  constraints
  row_in_range
  row_valid
  memory_bus_balance
  bitwise_bus_balance
  bitwise_bus_assumptions in
/-- The `a` operand is range-constrained by logic and bus balancing -/
lemma a_eq_and_range
:
  air.core.cmp_result row 0 = a0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧
  a0.val < 256
:= by
  rw [allHold_simplified_of_allHold] at constraints
  obtain ⟨ constrain_interactions,
           b_slt, b_sltu, b_is_valid, b_cmp_result, rest ⟩ := constraints
  clear constrain_interactions rest
  simp_all [VmAirWrapper_lt_constraint_and_interaction_simplification,
            InteractionList.balanced_by_ordered,
            Interaction.balances]

  grind

/-- From ALU opcode to RISC-V opcode -/
def rop_of_Lt_opcode (opcode : FBB) : rop :=
  if opcode = 520 then .SLT else .SLTU

include
  constraints
  row_in_range
  row_valid
  memory_bus_balance
  memory_bus_assumptions
  read_bus_balance
  read_bus_assumptions
  bitwise_bus_balance
  bitwise_bus_assumptions in
/-- The constraints entail correct implementation of the
    five base ALU opcodes for:
    - the `b` operand read from memory; and
    - the `c` operand as per the circuit
--/
theorem spec_base_Lt
:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3]
    =
  execute_RTYPE_pure
    (U32.toBV #v[↑b0, ↑b1, ↑b2, ↑b3])
    (U32.toBV #v[↑(air.core.c_0 row 0),
                 ↑(air.core.c_1 row 0),
                 ↑(air.core.c_2 row 0),
                 ↑(air.core.c_3 row 0)])
    (rop_of_Lt_opcode opcode)
:= by
  -- Get relevant previous info
  obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3, ub_a0 ⟩ := a_eq_and_range (constraints := constraints) (row_in_range := row_in_range) (row_valid := row_valid) (memory_bus_balance := memory_bus_balance) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)
  have h_eq_b := b_eq_and_range (row_valid := row_valid) (memory_bus_balance := memory_bus_balance)  (memory_bus_assumptions := memory_bus_assumptions)
  have h_eq_c := c_eq_and_range (constraints := constraints) (row_valid := row_valid) (memory_bus_balance := memory_bus_balance) (memory_bus_assumptions := memory_bus_assumptions) (read_bus_balance := read_bus_balance) (read_bus_assumptions := read_bus_assumptions) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)

  -- Get more detailed b-related information
  obtain ⟨ eq_b0, eq_b1, eq_b2, eq_b3,
           ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := h_eq_b

  -- Connect the opcode
  obtain opcode_eq : opcode = (air.core.ctx row 0).instruction.opcode := by
    simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
          InteractionList.balanced_by_ordered,
          Interaction.balances,
          Interaction.readInstructionBus_entry] at read_bus_balance
    rw [← LessThanCoreAir_4.ctx.instruction.opcode_def]
    grind

  -- Get more detailed c-related information
  obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3,
           h_not_imm, h_imm ⟩ := h_eq_c
  clear h_not_imm h_imm

  -- Get all opcode properties
  obtain ⟨ sop0, sop1 ⟩ := single_op air row row_in_range constraints
  obtain ⟨ op0, op1 ⟩ := op_from_opcode air row row_in_range constraints row_valid
  have opcodes := opcode_bounds air row row_in_range constraints row_valid
  rw [← opcode_eq] at op0 op1 opcodes; clear opcode_eq

  -- Clear up moduli using range information
  have ⟨ a_eq, b_eq, c_eq ⟩ :
    #v[↑a0, ↑a1, ↑a2, ↑a3] = #v[ ({ toFin := ⟨ a0.val, by omega ⟩} : BitVec 8), 0, 0, 0 ] ∧
    #v[↑b0, ↑b1, ↑b2, ↑b3] = #v[ ({ toFin := ⟨ b0.val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ b1.val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ b2.val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ b3.val, by omega ⟩} : BitVec 8) ]∧
    #v[(↑(air.core.c_0 row 0)), ↑(air.core.c_1 row 0), ↑(air.core.c_2 row 0), ↑(air.core.c_3 row 0)]
                           = #v[ ({ toFin := ⟨ (air.core.c_0 row 0).val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ (air.core.c_1 row 0).val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ (air.core.c_2 row 0).val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ (air.core.c_3 row 0).val, by omega ⟩} : BitVec 8) ]
  := by simp_all
  rw [a_eq, b_eq, c_eq]
  clear a_eq b_eq c_eq

  -- Prepare constraints
  rw [allHold_simplified_of_allHold] at constraints
  obtain ⟨ constrain_interactions,
           b_add, b_sub, b_is_valid, b_cmp_result, msb_b, msb_c,
           b_dm3, sum3_diff, dm3_diff, b_dm2, sum2_diff, dm2_diff,
           b_dm1, sum1_diff, dm1_diff, b_dm0, sum0_diff, dm0_diff,
           b_sum, sum0_cmp1, rest ⟩ := constraints
  clear constrain_interactions rest
  simp [VmAirWrapper_lt_constraint_and_interaction_simplification] at *

  -- Prepare bitwise_bus
  simp [InteractionList.balanced_by_ordered,
        Interaction.balances] at bitwise_bus_balance
  simp [Interaction.bitwiseBus_assumptions] at bitwise_bus_assumptions
  obtain ⟨ bb0, bb1, bb2 ⟩ := bitwise_bus_balance
  obtain ⟨ ba0, ba1, ba2 ⟩ := bitwise_bus_assumptions
  clear ba2 bb2

  simp [row_valid,
        ← LessThanCoreAir_4.prefix_sum_0_def,
        ← LessThanCoreAir_4.prefix_sum_1_def,
        ← LessThanCoreAir_4.prefix_sum_2_def,
        ← LessThanCoreAir_4.diff_def_0,
        ← LessThanCoreAir_4.diff_def_1,
        ← LessThanCoreAir_4.diff_def_2,
        ← LessThanCoreAir_4.diff_def_3] at *
  repeat rw [sub_eq_zero] at *

  obtain ⟨ eq_mul40, eq_x0, eq_y0, eq_z0, eq_xor0 ⟩ := bb0
  subst mul40 x0 y0 z0 xor0; simp_all

  -- Further simplifications
  clear read_bus_balance read_bus_assumptions
        memory_bus_balance memory_bus_assumptions

  have impossible : 2 * a0 = 1 ↔ False := by
    clear *- b_cmp_result
    grind
  simp_all

  -- Branch on opcode
  rcases opcodes with is_slt | is_sltu
  all_goals
    simp_all [execute_RTYPE_pure, rop_of_Lt_opcode]
    simp [← BitVec.toNat_inj, U32.toNat]

  -- SLT
  . simp [U32.toInt, ← U32.msb_3_negative, BitVec.msb_eq_decide]
    rcases b_sum with h_sum | h_sum <;> simp_all
    . -- All bytes are the same
      have ⟨ h_dm3, h_dm2, h_dm1, h_dm0 ⟩ :
        air.core.diff_marker_3 row 0 = 0 ∧ air.core.diff_marker_2 row 0 = 0 ∧
        air.core.diff_marker_1 row 0 = 0 ∧ air.core.diff_marker_0 row 0 = 0
        := by clear *- b_dm0 b_dm1 b_dm2 b_dm3 h_sum; grind
      rw [if_neg] <;> simp_all
      split_ifs <;> simp_all <;> grind
    . -- One byte differs
      -- Get further equalities from the bitwise bus
      obtain ⟨ eq_mul41, eq_x1, eq_y1, eq_z1, eq_xor1 ⟩ := bb1
      subst x1 y1 z1 xor1; clear eq_mul41

      -- Establish what the msb variables actually are
      have eq_msb_b : air.core.b_msb_f row 0 = if 128 ≤ b3.val then b3 - 256 else b3
        := by clear *- ub_b3 msb_b ba0; split_ifs <;> grind
      have eq_msb_c : air.core.c_msb_f row 0 = if 128 ≤ (air.core.c_3 row 0).val then air.core.c_3 row 0 - 256 else air.core.c_3 row 0
        := by clear *- ub_c3 msb_c ba0; split_ifs <;> grind

      -- Branch on the non-negativity of `b` and `c`
      by_cases b_neg : 128 ≤ b3.val <;>
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
    have ⟨ eq_msb_b, eq_msb_c ⟩ : air.core.b_msb_f row 0 = b3 ∧ air.core.c_msb_f row 0 = air.core.c_3 row 0
      := by clear *- ub_b3 ub_c3 msb_b msb_c ba0; grind
    simp_all
    rcases b_sum with h_sum | h_sum <;> simp_all
    . -- All bytes are the same
      have ⟨ h_dm3, h_dm2, h_dm1, h_dm0 ⟩ :
        air.core.diff_marker_3 row 0 = 0 ∧ air.core.diff_marker_2 row 0 = 0 ∧
        air.core.diff_marker_1 row 0 = 0 ∧ air.core.diff_marker_0 row 0 = 0
        := by clear *- b_dm0 b_dm1 b_dm2 b_dm3 h_sum; grind
      simp_all
    . -- One byte differs
      obtain ⟨ eq_mul41, eq_x1, eq_y1, eq_z1, eq_xor1 ⟩ := bb1
      subst x1 y1 z1 xor1; clear eq_mul41
      -- Case analysis on the byte that differs and the outcome
      rcases b_dm3 with h_dm3 | h_dm3 <;>
      rcases b_dm2 with h_dm2 | h_dm2 <;>
      rcases b_dm1 with h_dm1 | h_dm1 <;>
      rcases b_cmp_result <;> simp_all <;> split_ifs <;> grind

end General

section NonImmediate

include
  constraints
  row_in_range
  row_valid
  memory_bus_balance
  memory_bus_assumptions
  read_bus_balance
  read_bus_assumptions
  bitwise_bus_balance
  bitwise_bus_assumptions in
/-- The non-immediate variants of the five base ALU opcodes
    are implemented as per the RISC-V spec -/
theorem spec_base_Lt_non_imm
  (non_imm : rs2_as = 1)
:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3]
    =
  execute_RTYPE_pure
    (U32.toBV #v[↑b0, ↑b1, ↑b2, ↑b3])
    (U32.toBV #v[↑c0, ↑c1, ↑c2, ↑c3])
    (rop_of_Lt_opcode opcode)
:= by
  suffices eq_c : air.core.c_0 row 0 = c0 ∧
                  air.core.c_1 row 0 = c1 ∧
                  air.core.c_2 row 0 = c2 ∧
                  air.core.c_3 row 0 = c3
  . rw [← eq_c.1, ← eq_c.2.1, ← eq_c.2.2.1, ← eq_c.2.2.2]
    apply spec_base_Lt <;> assumption

  . obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3, h_not_imm, h_imm ⟩
      := c_eq_and_range (constraints := constraints) (row_valid := row_valid) (memory_bus_balance := memory_bus_balance) (memory_bus_assumptions := memory_bus_assumptions) (read_bus_balance := read_bus_balance) (read_bus_assumptions := read_bus_assumptions) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)
    apply h_not_imm
    simp [row_valid,
          VmAirWrapper_lt_constraint_and_interaction_simplification,
          InteractionList.balanced_by_ordered,
          Interaction.balances,
          Interaction.readInstructionBus_entry] at read_bus_balance
    grind

end NonImmediate

section Immediate

/-- From ALU opcode to RISC-V opcode -/
def iop_of_Lt_opcode (opcode : FBB) : iop :=
  if opcode = 520 then .SLTI else .SLTIU

include
  constraints
  row_in_range
  row_valid
  memory_bus_balance
  memory_bus_assumptions
  read_bus_balance
  read_bus_assumptions
  bitwise_bus_balance
  bitwise_bus_assumptions in
/-- The immediate variants of the five base ALU opcodes
    are implemented as per the RISC-V spec -/
theorem spec_base_Lt_imm
  (h_imm : rs2_as = 0)
:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3]
    =
  execute_ITYPE_pure
    (BitVec.ofNat 12 rs2)
    (U32.toBV #v[↑b0, ↑b1, ↑b2, ↑b3])
    (iop_of_Lt_opcode opcode)
:= by
  have read_bus_balance' := read_bus_balance
  simp [row_valid,
        VmAirWrapper_lt_constraint_and_interaction_simplification,
        InteractionList.balanced_by_ordered,
        Interaction.balances,
        Interaction.readInstructionBus_entry] at read_bus_balance'
  obtain ⟨ eq_mul, eq_pc, eq_opcode, eq_rd, eq_rs1, eq_rs2,
           eq_xd, eq_rs2_as, eq_xf, eq_xg ⟩ := read_bus_balance'
  clear eq_pc eq_rd eq_rs1 eq_xd eq_xf eq_xg

  have read_bus_assumptions' := read_bus_assumptions
  simp [Interaction.readInstructionBus_assumptions_Lt,
        eq_mul, h_imm] at read_bus_assumptions'
  obtain ⟨ reg_rd, reg_rs1,
           ⟨ ub_rs2, sign_extend_rs2 ⟩,
           eq_xd, eq_xf, eq_xg ⟩ := read_bus_assumptions'

  have opcode_bounds := opcode_bounds air row row_in_range constraints row_valid
  simp at opcode_bounds

  suffices eq_c
  :
    U32.toBV #v[air.core.c_0 row 0,
                air.core.c_1 row 0,
                air.core.c_2 row 0,
                air.core.c_3 row 0]
      = BitVec.signExtend 32 (BitVec.ofNat 12 rs2.val)
  . trans execute_RTYPE_pure
            (U32.toBV #v[↑b0, ↑b1, ↑b2, ↑b3])
            (U32.toBV #v[↑(air.core.c_0 row 0),
                         ↑(air.core.c_1 row 0),
                         ↑(air.core.c_2 row 0),
                         ↑(air.core.c_3 row 0)])
            (rop_of_Lt_opcode opcode)
    . apply spec_base_Lt (constraints := constraints) (row_in_range := row_in_range) (row_valid := row_valid) (memory_bus_balance := memory_bus_balance) (memory_bus_assumptions := memory_bus_assumptions) (read_bus_balance := read_bus_balance) (read_bus_assumptions := read_bus_assumptions) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)
    . simp [execute_ITYPE_pure]
      rw [← eq_c]; congr
      clear *- opcode_bounds
      simp [rop_of_Lt_opcode, iop_of_Lt_opcode]
      grind
  . obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3, h_not_imm, h_imm ⟩
      := c_eq_and_range (constraints := constraints) (row_valid := row_valid) (memory_bus_balance := memory_bus_balance) (memory_bus_assumptions := memory_bus_assumptions) (read_bus_balance := read_bus_balance) (read_bus_assumptions := read_bus_assumptions) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)
    simp [*] at h_imm
    assumption

end Immediate

end Lt.ValidRows
