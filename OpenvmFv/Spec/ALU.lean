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
  entry ∈ executionBus_row air row ++
          memoryBus_row air row ++
          rangeBus_row air row ++
          readInstructionBus_row air row ++
          bitwiseBus_row air row → entry.1 = 0
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
    Interaction.readInstructionBus_assumptions_ALU mul pc opcode rd rs1 rs2 xd rs2_as xf xg
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
      Interaction.bitwiseBus_entry mul42 x2 y2 z2 xor2,
      Interaction.bitwiseBus_entry mul43 x3 y3 z3 xor3,
      Interaction.bitwiseBus_entry mul44 x4 y4 z4 xor4,
    ]
  )
-- Bitwise bus assumptions
variable
  (bitwise_bus_assumptions:
    Interaction.bitwiseBus_assumptions mul40 x0 y0 z0 xor0 ∧
    Interaction.bitwiseBus_assumptions mul41 x1 y1 z1 xor1 ∧
    Interaction.bitwiseBus_assumptions mul42 x2 y2 z2 xor2 ∧
    Interaction.bitwiseBus_assumptions mul43 x3 y3 z3 xor3 ∧
    Interaction.bitwiseBus_assumptions mul44 x4 y4 z4 xor4
  )

section General

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
  simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
        InteractionList.balanced_by_ordered,
        Interaction.balances] at exec_bus_balance
  omega

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
  simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
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
           b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints
  clear constrain_interactions
        b_add b_sub b_xor b_or b_and b_is_valid
        add_0 sub_0 add_1 sub_1 add_2 sub_2 add_3 sub_3
        rest
  simp [VmAirWrapper_alu_constraint_and_interaction_simplification] at *

  simp [InteractionList.balanced_by_ordered,
        Interaction.balances] at memory_bus_balance
  simp [Interaction.memoryBus_assumptions] at memory_bus_assumptions
  obtain ⟨ mb0, mb1, mb2, mb3, mb4, mb5 ⟩ := memory_bus_balance
  obtain ⟨ m0, m1, m2 ⟩ :=  memory_bus_assumptions
  clear mb0 mb1 mb4 mb5 m0 m2

  simp [InteractionList.balanced_by_ordered,
        Interaction.balances] at bitwise_bus_balance
  simp [Interaction.bitwiseBus_assumptions] at bitwise_bus_assumptions

  simp [row_valid,
          ← BaseAluCoreAir.x_0_def, ← BaseAluCoreAir.x_1_def,
          ← BaseAluCoreAir.x_2_def, ← BaseAluCoreAir.x_3_def]
    at bitwise_bus_balance bitwise_bus_assumptions
  obtain ⟨ bb0, bb1, bb2, bb3, bb4 ⟩ := bitwise_bus_balance
  obtain ⟨ ba0, ba1, ba2, ba3, ba4 ⟩ := bitwise_bus_assumptions
  clear ba0 ba1 ba2 ba3

  have ⟨ ub_c0, ub_c1, ub_c2, ub_c3 ⟩
  :
    (air.core.c_0 row 0).val < 256 ∧ (air.core.c_1 row 0).val < 256 ∧
    (air.core.c_2 row 0).val < 256 ∧ (air.core.c_3 row 0).val < 256
  := by
    rcases b_rs2_as with eq_rs2_as_0 | eq_rs2_as_1 <;>
    (try rw [← VmAirWrapper_alu.rs2_sign_limbs] at imm_sign) <;>
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

      simp [Interaction.readInstructionBus_assumptions_ALU,
            eq_mul, eq_rs2_as_0] at read_bus_assumptions
      obtain ⟨ reg_rd, reg_rs1,
              ⟨ neq_opcode, ub_rs2, sign_extend_rs2 ⟩,
              eq_xd, eq_xf, eq_xg ⟩ := read_bus_assumptions
      clear reg_rd reg_rs1 eq_xd eq_xf eq_xg bb4
      simp [*, ← BitVec.toInt_inj]
      trans (BitVec.signExtend 32 (BitVec.ofNat 24 ↑rs2)).toInt
      . rw [BitVec.toInt_signExtend_of_le (by simp)]
        simp [eq_rs2_as_0, eq_rs2] at *
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
  air.core.a_0 row 0 = a0 ∧
  air.core.a_1 row 0 = a1 ∧
  air.core.a_2 row 0 = a2 ∧
  air.core.a_3 row 0 = a3 ∧
  a0.val < 256 ∧ a1.val < 256 ∧ a2.val < 256 ∧ a3.val < 256
:= by
  have ⟨ sop0, sop1, sop2, sop3, sop4 ⟩ := single_op air row row_in_range constraints

  rw [allHold_simplified_of_allHold] at constraints
  obtain ⟨ constrain_interactions,
           b_add, b_sub, b_xor, b_or, b_and, b_is_valid, rest ⟩ := constraints
  clear constrain_interactions rest
  simp [VmAirWrapper_alu_constraint_and_interaction_simplification] at *

  have ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩
  :
    air.core.a_0 row 0 = a0 ∧ air.core.a_1 row 0 = a1 ∧ air.core.a_2 row 0 = a2 ∧ air.core.a_3 row 0 = a3
  := by
      simp [InteractionList.balanced_by_ordered,
            Interaction.balances] at memory_bus_balance
      simp_all

  simp [InteractionList.balanced_by_ordered,
        Interaction.balances] at bitwise_bus_balance
  simp [Interaction.bitwiseBus_assumptions] at bitwise_bus_assumptions

  simp [row_valid,
          ← BaseAluCoreAir.x_0_def, ← BaseAluCoreAir.x_1_def,
          ← BaseAluCoreAir.x_2_def, ← BaseAluCoreAir.x_3_def] at bitwise_bus_balance bitwise_bus_assumptions
  obtain ⟨ bb0, bb1, bb2, bb3, bb4 ⟩ := bitwise_bus_balance
  obtain ⟨ ba0, ba1, ba2, ba3, ba4 ⟩ := bitwise_bus_assumptions

  simp_all

  clear *- b_add b_sub b_xor b_or b_and row_valid
           bb0 bb1 bb2 bb3 bb3 ba0 ba1 ba2 ba3
           sop0 sop1 sop2 sop3 sop4
           eq_a0 eq_a1 eq_a2 eq_a3

  rcases b_add <;> [ skip; simp_all ]
  rcases b_sub <;> [ skip; simp_all ]
  rcases b_xor <;> rcases b_and <;> rcases b_or <;> simp_all
  all_goals
    simp [← BaseAluCoreAir.x_xor_y_0_def, ← BaseAluCoreAir.x_xor_y_1_def,
          ← BaseAluCoreAir.x_xor_y_2_def, ← BaseAluCoreAir.x_xor_y_3_def,
          ← BaseAluCoreAir.y_0_def, ← BaseAluCoreAir.y_1_def,
          ← BaseAluCoreAir.y_2_def, ← BaseAluCoreAir.y_3_def] at bb0 bb1 bb2 bb3

    obtain ⟨ ba00, ba01, ba02 ⟩ := ba0
    obtain ⟨ ba10, ba11, ba12 ⟩ := ba1
    obtain ⟨ ba20, ba21, ba22 ⟩ := ba2
    obtain ⟨ ba30, ba31, ba32 ⟩ := ba3

    obtain ⟨ bb00, bb01, bb02, bb03, bb04 ⟩ := bb0
    obtain ⟨ bb10, bb11, bb12, bb13, bb14 ⟩ := bb1
    obtain ⟨ bb20, bb21, bb22, bb23, bb24 ⟩ := bb2
    obtain ⟨ bb30, bb31, bb32, bb33, bb34 ⟩ := bb3

    simp_all
    repeat rw [Fin.ext_iff] at *
    simp_all

  . have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba00 ba01 bb03
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba10 ba11 bb13
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba20 ba21 bb23
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba30 ba31 bb33
    grind

  . have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba00 ba01 bb03
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba10 ba11 bb13
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba20 ba21 bb23
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba30 ba31 bb33
    grind

  . split_ands
    all_goals
      apply Nat.xor_lt_two_pow (n := 8) <;>
      omega

/-- From ALU opcode to RISC-V opcode -/
def rop_of_ALU_opcode (opcode : FBB) : rop :=
  if opcode = 512 then .ADD else
  if opcode = 513 then .SUB else
  if opcode = 514 then .XOR else
  if opcode = 515 then .OR else .AND

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
theorem spec_base_ALU
:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3]
    =
  execute_RTYPE_pure
    (U32.toBV #v[↑b0, ↑b1, ↑b2, ↑b3])
    (U32.toBV #v[↑(air.core.c_0 row 0),
                 ↑(air.core.c_1 row 0),
                 ↑(air.core.c_2 row 0),
                 ↑(air.core.c_3 row 0)])
    (rop_of_ALU_opcode opcode)
:= by
  -- Get relevant previous info
  obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3, ub_a0, ub_a1, ub_a2, ub_a3 ⟩ := a_eq_and_range (constraints := constraints) (row_in_range := row_in_range) (row_valid := row_valid) (memory_bus_balance := memory_bus_balance) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)
  have h_eq_b := b_eq_and_range (row_valid := row_valid) (memory_bus_balance := memory_bus_balance)  (memory_bus_assumptions := memory_bus_assumptions)
  have h_eq_c := c_eq_and_range (constraints := constraints) (row_valid := row_valid) (memory_bus_balance := memory_bus_balance) (memory_bus_assumptions := memory_bus_assumptions) (read_bus_balance := read_bus_balance) (read_bus_assumptions := read_bus_assumptions) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)

  -- Get more detailed b-related information
  obtain ⟨ eq_b0, eq_b1, eq_b2, eq_b3,
           ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := h_eq_b

  -- Connect the opcode
  obtain opcode_eq : opcode = (air.core.ctx row 0).instruction.opcode := by
    simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
          InteractionList.balanced_by_ordered,
          Interaction.balances,
          Interaction.readInstructionBus_entry] at read_bus_balance
    grind

  -- Get more detailed c-related information
  obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3,
           h_not_imm, h_imm ⟩ := h_eq_c
  clear h_not_imm h_imm

  -- Get all opcode properties
  obtain ⟨ sop0, sop1, sop2, sop3, sop4 ⟩ := single_op air row row_in_range constraints
  obtain ⟨ op0, op1, op2, op3, op4 ⟩ := op_from_opcode air row row_in_range constraints row_valid
  have opcodes := opcode_bounds air row row_in_range constraints row_valid

  -- Clear up moduli using range information
  have ⟨ a_eq, b_eq, c_eq ⟩ :
    #v[↑a0, ↑a1, ↑a2, ↑a3] = #v[ ({ toFin := ⟨ a0.val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ a1.val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ a2.val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ a3.val, by omega ⟩} : BitVec 8) ] ∧
    #v[↑b0, ↑b1, ↑b2, ↑b3] = #v[ ({ toFin := ⟨ b0.val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ b1.val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ b2.val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ b3.val, by omega ⟩} : BitVec 8) ]∧
    #v[(↑(air.core.c_0 row 0)), ↑(air.core.c_1 row 0), ↑(air.core.c_2 row 0), ↑(air.core.c_3 row 0)]
                           = #v[ ({ toFin := ⟨ (air.core.c_0 row 0).val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ (air.core.c_1 row 0).val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ (air.core.c_2 row 0).val, by omega ⟩} : BitVec 8),
                                 ({ toFin := ⟨ (air.core.c_3 row 0).val, by omega ⟩} : BitVec 8) ]
  := by simp; omega
  rw [a_eq, b_eq, c_eq]

  -- Prepare constraints
  rw [allHold_simplified_of_allHold] at constraints
  obtain ⟨ constrain_interactions,
           b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rest ⟩ := constraints
  clear constrain_interactions rest
  simp [VmAirWrapper_alu_constraint_and_interaction_simplification] at *

  -- Prepare bitwise_bus
  simp [InteractionList.balanced_by_ordered,
        Interaction.balances] at bitwise_bus_balance
  simp [Interaction.bitwiseBus_assumptions] at bitwise_bus_assumptions
  obtain ⟨ bb0, bb1, bb2, bb3, bb4 ⟩ := bitwise_bus_balance
  obtain ⟨ ba0, ba1, ba2, ba3, ba4 ⟩ := bitwise_bus_assumptions

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
    obtain ⟨ ba00, ba01, ba02 ⟩ := ba0
    obtain ⟨ ba10, ba11, ba12 ⟩ := ba1
    obtain ⟨ ba20, ba21, ba22 ⟩ := ba2
    obtain ⟨ ba30, ba31, ba32 ⟩ := ba3

    obtain ⟨ bb00, bb01, bb02, bb03, bb04 ⟩ := bb0
    obtain ⟨ bb10, bb11, bb12, bb13, bb14 ⟩ := bb1
    obtain ⟨ bb20, bb21, bb22, bb23, bb24 ⟩ := bb2
    obtain ⟨ bb30, bb31, bb32, bb33, bb34 ⟩ := bb3
    symm at bb03 bb13 bb23 bb33
    simp_all

  -- XOR
  . repeat rw [BitVec.xor_append, BitVec.append_eq_append_eql]
    simp [← BitVec.toNat_inj]

  -- OR
  . repeat rw [BitVec.or_append, BitVec.append_eq_append_eql]
    simp_all [← BitVec.toNat_inj]

    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba00 ba01 ba02
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba10 ba11 ba12
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba20 ba21 ba22
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba30 ba31 ba32
    simp_all

  -- AND
  . repeat rw [BitVec.and_append, BitVec.append_eq_append_eql]
    simp_all [← BitVec.toNat_inj]

    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba00 ba01 ba02
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba10 ba11 ba12
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba20 ba21 ba22
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba30 ba31 ba32
    simp_all

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
theorem spec_base_ALU_non_imm
  (non_imm : rs2_as = 1)
:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3]
    =
  execute_RTYPE_pure
    (U32.toBV #v[↑b0, ↑b1, ↑b2, ↑b3])
    (U32.toBV #v[↑c0, ↑c1, ↑c2, ↑c3])
    (rop_of_ALU_opcode opcode)
:= by
  suffices eq_c : air.core.c_0 row 0 = c0 ∧
                  air.core.c_1 row 0 = c1 ∧
                  air.core.c_2 row 0 = c2 ∧
                  air.core.c_3 row 0 = c3
  . rw [← eq_c.1, ← eq_c.2.1, ← eq_c.2.2.1, ← eq_c.2.2.2]
    apply spec_base_ALU <;> assumption

  . obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3, h_not_imm, h_imm ⟩
      := c_eq_and_range (constraints := constraints) (row_valid := row_valid) (memory_bus_balance := memory_bus_balance) (memory_bus_assumptions := memory_bus_assumptions) (read_bus_balance := read_bus_balance) (read_bus_assumptions := read_bus_assumptions) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)
    apply h_not_imm
    simp [row_valid,
          VmAirWrapper_alu_constraint_and_interaction_simplification,
          InteractionList.balanced_by_ordered,
          Interaction.balances,
          Interaction.readInstructionBus_entry] at read_bus_balance
    grind

end NonImmediate

section Immediate

/-- From ALU opcode to RISC-V opcode -/
def iop_of_ALU_opcode (opcode : FBB) : iop :=
  if opcode = 512 then .ADDI else
  if opcode = 514 then .XORI else
  if opcode = 515 then .ORI else .ANDI

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
theorem spec_base_ALU_imm
  (h_imm : rs2_as = 0)
:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3]
    =
  execute_ITYPE_pure
    (BitVec.ofNat 12 rs2)
    (U32.toBV #v[↑b0, ↑b1, ↑b2, ↑b3])
    (iop_of_ALU_opcode opcode)
:= by
  have read_bus_balance' := read_bus_balance
  simp [row_valid,
        VmAirWrapper_alu_constraint_and_interaction_simplification,
        InteractionList.balanced_by_ordered,
        Interaction.balances,
        Interaction.readInstructionBus_entry] at read_bus_balance'
  obtain ⟨ eq_mul, eq_pc, eq_opcode, eq_rd, eq_rs1, eq_rs2,
           eq_xd, eq_rs2_as, eq_xf, eq_xg ⟩ := read_bus_balance'
  clear eq_pc eq_rd eq_rs1 eq_xd eq_xf eq_xg

  have read_bus_assumptions' := read_bus_assumptions
  simp [Interaction.readInstructionBus_assumptions_ALU,
        eq_mul, h_imm] at read_bus_assumptions'
  obtain ⟨ reg_rd, reg_rs1,
           ⟨ neq_opcode, ub_rs2, sign_extend_rs2 ⟩,
           eq_xd, eq_xf, eq_xg ⟩ := read_bus_assumptions'

  have opcode_bounds := opcode_bounds air row row_in_range constraints row_valid
  simp [eq_opcode] at opcode_bounds

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
            (rop_of_ALU_opcode opcode)
    . apply spec_base_ALU <;> assumption
    . simp [execute_ITYPE_pure]
      rw [← eq_c]; congr
      clear *- opcode_bounds neq_opcode
      simp [rop_of_ALU_opcode, iop_of_ALU_opcode]
      grind
  . obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3, h_not_imm, h_imm ⟩
      := c_eq_and_range (constraints := constraints) (row_valid := row_valid) (memory_bus_balance := memory_bus_balance) (memory_bus_assumptions := memory_bus_assumptions) (read_bus_balance := read_bus_balance) (read_bus_assumptions := read_bus_assumptions) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)
    simp [*] at h_imm
    assumption

end Immediate

end ALU.ValidRows
