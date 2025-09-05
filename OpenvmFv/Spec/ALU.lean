import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Constraints.VmAirWrapper_alu
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_alu FBB ExtF)

-- Table has only one row
variable (h_last_row : air.last_row = 0)
-- All constraints hold
variable (constraints : VmAirWrapper_alu.constraints.allHold air 0 (by simp))

-- Execution bus is balanced
variable
  {start_pc start_timestamp mul00 mul01 end_pc end_timestamp}
  (exec_bus_balance :
  InteractionList.balanced_by_ordered
    (air.buses ExecutionBus)
    [
      Interaction.executionBus_entry 1 start_pc start_timestamp,
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
    (air.buses MemoryBus)
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
    (air.buses RangeCheckerBus)
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
    (air.buses ReadInstructionBus)
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
    (air.buses BitwiseBus)
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

include constraints in
/-- Interactions are of the form enforced by constraints -/
lemma constrain_interactions
:
  VmAirWrapper_alu.extraction.constrain_interactions air
:= by
  rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints
  grind

include
  constraints
  h_last_row
  exec_bus_balance in
/-- The row is valid -/
lemma is_valid
:
  air.core.is_valid 0 0 = 1
:= by
  have ⟨ exec_bus, rest ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero
                               (by exact constrain_interactions ExtF air constraints)
                               h_last_row
  rw [exec_bus] at exec_bus_balance
  simp [VmAirWrapper_alu.buses.executionBus_row,
        InteractionList.balanced_by_ordered,
        Interaction.balances,
        Interaction.executionBus_entry] at exec_bus_balance
  grind

include
  constraints
  h_last_row
  exec_bus_balance in
/-- The `pc` and `timestamp` are as expected -/
lemma pc_and_timestamp
:
  end_pc = start_pc + 4 ∧
  end_timestamp = start_timestamp + 3
:= by
  have ⟨ exec_bus, rest ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero (by exact constrain_interactions ExtF air constraints) h_last_row
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance)
  simp [exec_bus,
        InteractionList.balanced_by_ordered,
        Interaction.balances] at exec_bus_balance
  omega

/-- **TODO** The memory read-write timestamps are monotonic -/
lemma monotonic_timestamps
:
  True
:=
  by sorry

include
  constraints
  h_last_row
  exec_bus_balance
  memory_bus_balance
  memory_bus_assumptions in
/-- The `b` operand is range-constrained by bus balancing -/
lemma b_eq_and_range
:
  air.core.b_0 0 0 = b0 ∧ air.core.b_1 0 0 = b1 ∧ air.core.b_2 0 0 = b2 ∧ air.core.b_3 0 0 = b3 ∧
  b0.val < 256 ∧ b1.val < 256 ∧ b2.val < 256 ∧ b3.val < 256
:= by
  have ⟨ exec_bus, memory_bus, rest ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero (by exact constrain_interactions ExtF air constraints) h_last_row
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance)
  simp [memory_bus,
        InteractionList.balanced_by_ordered,
        Interaction.balances] at memory_bus_balance
  simp [Interaction.memoryBus_assumptions] at memory_bus_assumptions
  grind

include
  constraints
  h_last_row
  exec_bus_balance
  memory_bus_balance
  memory_bus_assumptions
  bitwise_bus_balance
  bitwise_bus_assumptions in
/-- The `c` operand is:
    - range-constrained by bus balancing for non-immediate opcodes
    - **TODO** for immediate opcodes -/
lemma c_eq_and_range
:
  (air.core.c_0 0 0).val < 256 ∧ (air.core.c_1 0 0).val < 256 ∧ (air.core.c_2 0 0).val < 256 ∧ (air.core.c_3 0 0).val < 256 ∧
  (air.adapter.rs2_as 0 0 = 1 →
    air.core.c_0 0 0 = c0 ∧ air.core.c_1 0 0 = c1 ∧ air.core.c_2 0 0 = c2 ∧ air.core.c_3 0 0 = c3) ∧
  (air.adapter.rs2_as 0 0 = 0 → True)
:= by
  have ⟨ exec_bus, memory_bus, range_bus, readInstr_bus, bitwise_bus ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero (by exact constrain_interactions ExtF air constraints) h_last_row
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance)

  have constraints' := constraints
  rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints'
  obtain ⟨ b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints'
  clear b_add b_sub b_xor b_or b_and b_is_valid
        add_0 sub_0 add_1 sub_1 add_2 sub_2 add_3 sub_3
        rest

  simp [memory_bus,
        InteractionList.balanced_by_ordered,
        Interaction.balances] at memory_bus_balance
  simp [Interaction.memoryBus_assumptions] at memory_bus_assumptions
  obtain ⟨ m0, m1, m2 ⟩ :=  memory_bus_assumptions

  simp [bitwise_bus,
        InteractionList.balanced_by_ordered,
        Interaction.balances] at bitwise_bus_balance
  simp [Interaction.bitwiseBus_assumptions] at bitwise_bus_assumptions

  simp [is_valid,
          ← BaseAluCoreAir.x_0_def, ← BaseAluCoreAir.x_1_def,
          ← BaseAluCoreAir.x_2_def, ← BaseAluCoreAir.x_3_def]
    at bitwise_bus_balance bitwise_bus_assumptions
  obtain ⟨ ba0, ba1, ba2, ba3, ba4 ⟩ := bitwise_bus_assumptions
  clear ba0 ba1 ba2 ba3

  have ⟨ ub_c0, ub_c1, ub_c2, ub_c3 ⟩
  :
    (air.core.c_0 0 0).val < 256 ∧ (air.core.c_1 0 0).val < 256 ∧
    (air.core.c_2 0 0).val < 256 ∧ (air.core.c_3 0 0).val < 256
  := by
    rcases b_rs2_as with eq_rs2_as_0 | eq_rs2_as_1 <;>
    try rw [← VmAirWrapper_alu.rs2_sign_limbs] at imm_sign <;>
    simp_all;
    omega

  rcases b_rs2_as with eq_rs2_as_0 | eq_rs2_as_1 <;>
  simp_all;
  omega

include
  constraints
  h_last_row
  exec_bus_balance
  memory_bus_balance
  bitwise_bus_balance
  bitwise_bus_assumptions in
/-- The `a` operand is range-constrained by logic and bus balancing -/
lemma a_eq_and_range
:
  air.core.a_0 0 0 = a0 ∧
  air.core.a_1 0 0 = a1 ∧
  air.core.a_2 0 0 = a2 ∧
  air.core.a_3 0 0 = a3 ∧
  a0.val < 256 ∧ a1.val < 256 ∧ a2.val < 256 ∧ a3.val < 256
:= by
  have ⟨ exec_bus, memory_bus, range_bus, readInstr_bus, bitwise_bus ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero (by exact constrain_interactions ExtF air constraints) h_last_row
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance)
  have constraints' := constraints
  rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints'
  obtain ⟨ b_add, b_sub, b_xor, b_or, b_and, b_is_valid, rest ⟩ := constraints'
  clear rest

  have ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩
  :
    air.core.a_0 0 0 = a0 ∧ air.core.a_1 0 0 = a1 ∧ air.core.a_2 0 0 = a2 ∧ air.core.a_3 0 0 = a3
  := by
      simp [memory_bus,
        InteractionList.balanced_by_ordered,
        Interaction.balances] at memory_bus_balance
      simp_all

  simp [bitwise_bus,
        InteractionList.balanced_by_ordered,
        Interaction.balances] at bitwise_bus_balance
  simp [Interaction.bitwiseBus_assumptions] at bitwise_bus_assumptions

  simp [is_valid,
          ← BaseAluCoreAir.x_0_def, ← BaseAluCoreAir.x_1_def,
          ← BaseAluCoreAir.x_2_def, ← BaseAluCoreAir.x_3_def] at bitwise_bus_balance bitwise_bus_assumptions
  obtain ⟨ bb0, bb1, bb2, bb3, bb4 ⟩ := bitwise_bus_balance
  obtain ⟨ ba0, ba1, ba2, ba3, ba4 ⟩ := bitwise_bus_assumptions

  simp_all

  have ⟨ sop0, sop1, sop2, sop3, sop4 ⟩ := VmAirWrapper_alu.constraints.single_op air 0 (by simp) constraints
  clear *- b_add b_sub b_xor b_or b_and is_valid
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

section add

include
  constraints
  h_last_row
  exec_bus_balance
  memory_bus_balance
  memory_bus_assumptions
  read_bus_balance
  bitwise_bus_balance
  bitwise_bus_assumptions in
/-- The `ADD` opcode is implemented as per the RISC-V spec -/
theorem spec_add
  (h_add : opcode = 512)
  (h_not_imm : rs2_as = 1)
:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3]
    =
  execute_RTYPE_pure_U32
    #v[↑b0, ↑b1, ↑b2, ↑b3]
    #v[↑c0, ↑c1, ↑c2, ↑c3]
    .ADD
:= by
  -- Get relevant previous info
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance)
  obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3, ub_a0, ub_a1, ub_a2, ub_a3 ⟩ := a_eq_and_range (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance) (memory_bus_balance := memory_bus_balance) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)
  have h_eq_b := b_eq_and_range (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance) (memory_bus_balance := memory_bus_balance)  (memory_bus_assumptions := memory_bus_assumptions)
  have h_eq_c_non_imm := c_eq_and_range (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance) (memory_bus_balance := memory_bus_balance) (memory_bus_assumptions := memory_bus_assumptions) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)

  -- Isolate relevant constraints
  have constraints' := constraints
  rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints'
  obtain ⟨ b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rest ⟩ := constraints'
  clear sub_0 sub_1 sub_2 sub_3 rest

  -- Get more detailed b-related information
  obtain ⟨ eq_b0, eq_b1, eq_b2, eq_b3,
           ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := h_eq_b

  -- The operation is not immediate and the opcode is ADD
  obtain ⟨ non_imm, is_add ⟩ : air.adapter.rs2_as 0 0 = 1 ∧ air.core.opcode_add_flag 0 0 = 1 := by
    have ⟨ exec_bus, memory_bus, range_bus, readInstr_bus, bitwise_bus ⟩ :=
      VmAirWrapper_alu.buses.buses_last_row_zero
      (by exact constrain_interactions ExtF air constraints)
      h_last_row
    rw [readInstr_bus] at read_bus_balance
    simp [VmAirWrapper_alu.buses.readInstructionBus_row,
          InteractionList.balanced_by_ordered,
          Interaction.balances,
          Interaction.readInstructionBus_entry,
          h_add, h_not_imm, is_valid] at read_bus_balance
    rw [← BaseAluCoreAir.ctx.instruction.opcode_def] at read_bus_balance
    obtain ⟨ _, _, opcode_eq, _, _, _, _, eq_rs2_as, _ ⟩ := read_bus_balance
    clear *- b_add b_sub b_xor b_or b_and is_valid opcode_eq eq_rs2_as
    rw [← BaseAluCoreAir.is_valid_def] at is_valid
    grind

  -- Get more detailed c-related information
  simp [non_imm] at h_eq_c_non_imm
  obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3,
           eq_c0, eq_c1, eq_c2, eq_c3 ⟩ := h_eq_c_non_imm

  -- Recall that only one opcode can equal one
  have ⟨ sop0, sop1, sop2, sop3, sop4 ⟩ := VmAirWrapper_alu.constraints.single_op air 0 (by simp) constraints

  -- Open the carries
  rw [← BaseAluCoreAir.carry_add_3_def,
      ← BaseAluCoreAir.carry_add_2_def,
      ← BaseAluCoreAir.carry_add_1_def,
      ← BaseAluCoreAir.carry_add_0_def] at *

  -- Simplify maximally
  simp_all

  -- Now prove
  trans U32.toBV #v[ ({ toFin := ⟨ a0.val, by omega ⟩} : BitVec 8),
                     ({ toFin := ⟨ a1.val, by omega ⟩} : BitVec 8),
                     ({ toFin := ⟨ a2.val, by omega ⟩} : BitVec 8),
                     ({ toFin := ⟨ a3.val, by omega ⟩} : BitVec 8) ]
  . congr <;> omega
  . simp [← BitVec.toNat_inj, U32.toBV_toNat, U32.toNat]
    clear *- add_0 add_1 add_2 add_3 ub_a0 ub_a1 ub_a2 ub_a3
             ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
    rcases add_0 <;> rcases add_1 <;>
    rcases add_2 <;> rcases add_3 <;>
    simp_all <;> omega

end add

section sub

include
  constraints
  h_last_row
  exec_bus_balance
  memory_bus_balance
  memory_bus_assumptions
  read_bus_balance
  bitwise_bus_balance
  bitwise_bus_assumptions in
/-- The `SUB` opcode is implemented as per the RISC-V spec -/
theorem spec_sub
  (h_add : opcode = 513)
  (h_not_imm : rs2_as = 1)
:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3]
    =
  execute_RTYPE_pure_U32
    #v[↑b0, ↑b1, ↑b2, ↑b3]
    #v[↑c0, ↑c1, ↑c2, ↑c3]
    .SUB
:= by
  -- Get relevant previous info
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance)
  obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3, ub_a0, ub_a1, ub_a2, ub_a3 ⟩ := a_eq_and_range (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance) (memory_bus_balance := memory_bus_balance) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)
  have h_eq_b := b_eq_and_range (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance) (memory_bus_balance := memory_bus_balance)  (memory_bus_assumptions := memory_bus_assumptions)
  have h_eq_c_non_imm := c_eq_and_range (constraints := constraints) (h_last_row := h_last_row) (exec_bus_balance := exec_bus_balance) (memory_bus_balance := memory_bus_balance) (memory_bus_assumptions := memory_bus_assumptions) (bitwise_bus_balance := bitwise_bus_balance) (bitwise_bus_assumptions := bitwise_bus_assumptions)

  -- Isolate relevant constraints
  have constraints' := constraints
  rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints'
  obtain ⟨ b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rest ⟩ := constraints'
  clear add_0 add_1 add_2 add_3 rest

  -- Get more detailed b-related information
  obtain ⟨ eq_b0, eq_b1, eq_b2, eq_b3,
           ub_b0, ub_b1, ub_b2, ub_b3 ⟩ := h_eq_b

  -- The operation is not immediate and the opcode is ADD
  obtain ⟨ non_imm, is_sub ⟩ : air.adapter.rs2_as 0 0 = 1 ∧ air.core.opcode_sub_flag 0 0 = 1 := by
    have ⟨ exec_bus, memory_bus, range_bus, readInstr_bus, bitwise_bus ⟩ :=
      VmAirWrapper_alu.buses.buses_last_row_zero
      (by exact constrain_interactions ExtF air constraints)
      h_last_row
    rw [readInstr_bus] at read_bus_balance
    simp [VmAirWrapper_alu.buses.readInstructionBus_row,
          InteractionList.balanced_by_ordered,
          Interaction.balances,
          Interaction.readInstructionBus_entry,
          h_add, h_not_imm, is_valid] at read_bus_balance
    rw [← BaseAluCoreAir.ctx.instruction.opcode_def] at read_bus_balance
    obtain ⟨ _, _, opcode_eq, _, _, _, _, eq_rs2_as, _ ⟩ := read_bus_balance
    clear *- b_add b_sub b_xor b_or b_and is_valid opcode_eq eq_rs2_as
    rw [← BaseAluCoreAir.is_valid_def] at is_valid
    grind

  -- Get more detailed c-related information
  simp [non_imm] at h_eq_c_non_imm
  obtain ⟨ ub_c0, ub_c1, ub_c2, ub_c3,
           eq_c0, eq_c1, eq_c2, eq_c3,
           eqv_c0, eqv_c1, eqv_c2, eqv_c3 ⟩ := h_eq_c_non_imm

  -- Recall that only one opcode can equal one
  have ⟨ sop0, sop1, sop2, sop3, sop4 ⟩ := VmAirWrapper_alu.constraints.single_op air 0 (by simp) constraints

  -- Open the carries
  rw [← BaseAluCoreAir.carry_sub_3_def,
      ← BaseAluCoreAir.carry_sub_2_def,
      ← BaseAluCoreAir.carry_sub_1_def,
      ← BaseAluCoreAir.carry_sub_0_def] at *

  -- Simplify maximally
  simp_all

  -- Now prove
  trans U32.toBV #v[ ({ toFin := ⟨ a0.val, by omega ⟩} : BitVec 8),
                     ({ toFin := ⟨ a1.val, by omega ⟩} : BitVec 8),
                     ({ toFin := ⟨ a2.val, by omega ⟩} : BitVec 8),
                     ({ toFin := ⟨ a3.val, by omega ⟩} : BitVec 8) ]
  . congr <;> omega
  . simp [← BitVec.toNat_inj, U32.toBV_toNat, U32.toNat]
    clear *- sub_0 sub_1 sub_2 sub_3 ub_a0 ub_a1 ub_a2 ub_a3
             ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
    rcases sub_0 <;> rcases sub_1 <;>
    rcases sub_2 <;> rcases sub_3 <;>
    simp_all <;> omega

end sub
