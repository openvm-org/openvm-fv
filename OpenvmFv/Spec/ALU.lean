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

-- Execution bus is balanced, **and the row is valid**
variable {start_pc start_timestamp mul00 end_pc end_timestamp}
         (balanced_execution :
          InteractionList.balanced_by_ordered
            (air.buses ExecutionBus)
            [
              Interaction.executionBus_entry 1 start_pc start_timestamp,
              Interaction.executionBus_entry mul00 end_pc end_timestamp,
            ]
         )
-- Memory bus is balanced
variable {mul10 as0 r0 b t0 mul11 as1 r1 b0 b1 b2 b3 t1 mul12 as2 r2 c t2 mul13 as3 r3 c0 c1 c2 c3 t3 mul14 as4 d t4 mul15 as5 r5 a0 a1 a2 a3 t5}
         (balanced_memory :
          InteractionList.balanced_by_ordered
            (air.buses MemoryBus)
            [
              Interaction.memoryBus_write_entry mul10 as0 r0 b t0,
              Interaction.memoryBus_read_entry mul11 as1 r1 b0 b1 b2 b3 t1,
              Interaction.memoryBus_write_entry mul12 as2 r2 c t2,
              Interaction.memoryBus_read_entry mul13 as3 r3 c0 c1 c2 c3 t3,
              Interaction.memoryBus_write_entry mul14 as4 r3 d t4,
              Interaction.memoryBus_read_entry mul15 as5 r5 a0 a1 a2 a3 t5
            ]
          )
-- Range-checking bus is balanced
variable {mul20 r0l0 mul21 r0l1 mul22 r1l0 mul23 r1l1 mul24 bl0 mul25 bl1}
         (balanced_range :
          InteractionList.balanced_by_ordered
            (air.buses RangeCheckerBus)
            [
              Interaction.rangeBus_entry mul20 17 r0l0,
              Interaction.rangeBus_entry mul21 12 r0l1,
              Interaction.rangeBus_entry mul22 17 r1l0,
              Interaction.rangeBus_entry mul23 12 r1l1,
              Interaction.rangeBus_entry mul24 17 bl0,
              Interaction.rangeBus_entry mul25 12 bl1
            ]
         )
-- Read-instruction bus is balanced
variable {mul pc opcode rd rs1 rs2 unknown0 rs2_as unknown1 unknown2}
         (balanced_read :
          InteractionList.balanced_by_ordered
            (air.buses ReadInstructionBus)
            [
              Interaction.readInstructionBus_entry mul pc opcode rd rs1 rs2 unknown0 rs2_as unknown1 unknown2,
            ]
         )
-- Bitwise bus is balanced
variable {mul40 x0 y0 l0 mul41 x1 y1 l1 mul42 x2 y2 l2 mul43 x3 y3 l3 mul44 x4 y4 l4}
         (balanced_bitwise :
          InteractionList.balanced_by_ordered
            (air.buses BitwiseBus)
            [
              Interaction.bitwiseBus_entry mul40 x0 y0 l0,
              Interaction.bitwiseBus_entry mul41 x1 y1 l1,
              Interaction.bitwiseBus_entry mul42 x2 y2 l2,
              Interaction.bitwiseBus_entry mul43 x3 y3 l3,
              Interaction.bitwiseBus_entry mul44 x4 y4 l4
            ]
         )

include constraints in
/-- Interactions are of the form enforced by constraints -/
lemma ci
:
  VmAirWrapper_alu.extraction.constrain_interactions air
:= by
  rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints
  grind

include constraints h_last_row balanced_execution in
/-- The row is valid -/
lemma is_valid
:
  air.core.is_valid 0 0 = 1
:= by
  have ⟨ exec_bus, rest ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero
                               (by exact ci ExtF air constraints)
                               h_last_row
  rw [exec_bus] at balanced_execution
  simp [VmAirWrapper_alu.buses.executionBus_row,
        InteractionList.balanced_by_ordered,
        Interaction.balances,
        Interaction.executionBus_entry] at balanced_execution
  grind

include constraints h_last_row balanced_execution in
/-- The `pc` and `timestamp` are as expected -/
lemma pc_and_timestamp
:
  end_pc = start_pc + 4 ∧
  end_timestamp = start_timestamp + 3
:= by
  have ⟨ exec_bus, rest ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero (by exact ci ExtF air constraints) h_last_row
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution)
  rw [exec_bus] at balanced_execution
  apply VmAirWrapper_alu.buses.executionBus_balanced_row at balanced_execution
  simp [is_valid] at balanced_execution
  omega

/-- **TODO** The memory read-write timestamps are monotonic -/
lemma monotonic_timestamps
:
  True
:=
  by sorry
  -- rs1_prev_timestamp.val < timestamp.val ∧
  -- rs2_prev_timestamp.val < timestamp.val + 1 ∧
  -- rd_prev_timestamp.val < timestamp.val + 2

include constraints h_last_row balanced_execution balanced_memory in
/-- The `b` operand is range-constrained by bus balancing -/
lemma eq_b
:
  air.core.b_0 0 0 = b0 ∧ air.core.b_1 0 0 = b1 ∧ air.core.b_2 0 0 = b2 ∧ air.core.b_3 0 0 = b3 ∧
  b0.val < 256 ∧ b1.val < 256 ∧ b2.val < 256 ∧ b3.val < 256 ∧
  b0.val = (b.get 0).toNat ∧ b1.val = (b.get 1).toNat ∧ b2.val = (b.get 2).toNat ∧ b3.val = (b.get 3).toNat
:= by
  have ⟨ exec_bus, memory_bus, rest ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero (by exact ci ExtF air constraints) h_last_row
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution)
  rw [memory_bus] at balanced_memory
  apply VmAirWrapper_alu.buses.memoryBus_balanced_row at balanced_memory
  obtain ⟨ m0, m1, m2, m3, m4, m5 ⟩ := balanced_memory
  simp_all [Vector.get]
  omega

include constraints h_last_row balanced_execution balanced_memory balanced_bitwise in
/-- The `c` operand is:
    - range-constrained by bus balancing for non-immediate opcodes
    - **TODO** for immediate opcodes -/
lemma eq_c
:
  (air.core.c_0 0 0).val < 256 ∧ (air.core.c_1 0 0).val < 256 ∧ (air.core.c_2 0 0).val < 256 ∧ (air.core.c_3 0 0).val < 256 ∧
  (air.adapter.rs2_as 0 0 = 1 →
    air.core.c_0 0 0 = c0 ∧ air.core.c_1 0 0 = c1 ∧ air.core.c_2 0 0 = c2 ∧ air.core.c_3 0 0 = c3 ∧
    c0.val = (c.get 0).toNat ∧ c1.val = (c.get 1).toNat ∧ c2.val = (c.get 2).toNat ∧ c3.val = (c.get 3).toNat) ∧
  (air.adapter.rs2_as 0 0 = 0 → True)
:= by
  have ⟨ exec_bus, memory_bus, range_bus, readInstr_bus, bitwise_bus ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero (by exact ci ExtF air constraints) h_last_row
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution)

  have constraints' := constraints
  rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints'
  obtain ⟨ b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend, rest ⟩ := constraints'
  clear b_add b_sub b_xor b_or b_and b_is_valid
        add_0 sub_0 add_1 sub_1 add_2 sub_2 add_3 sub_3
        rest

  rw [memory_bus] at balanced_memory
  apply VmAirWrapper_alu.buses.memoryBus_balanced_row at balanced_memory
  obtain ⟨ m0, m1, m2, m3, m4, m5 ⟩ :=  balanced_memory

  rw [bitwise_bus] at balanced_bitwise
  apply VmAirWrapper_alu.buses.bitwiseBus_balanced_row at balanced_bitwise
  simp [is_valid,
          ← BaseAluCoreAir.x_0_def, ← BaseAluCoreAir.x_1_def,
          ← BaseAluCoreAir.x_2_def, ← BaseAluCoreAir.x_3_def] at balanced_bitwise
  obtain ⟨ ba0, ba1, ba2, ba3, ba4 ⟩ := balanced_bitwise
  clear ba0 ba1 ba2 ba3

  have ⟨ ub_c0, ub_c1, ub_c2, ub_c3 ⟩
  :
    (air.core.c_0 0 0).val < 256 ∧ (air.core.c_1 0 0).val < 256 ∧
    (air.core.c_2 0 0).val < 256 ∧ (air.core.c_3 0 0).val < 256
  := by
    rcases b_rs2_as with eq_rs2_as_0 | eq_rs2_as_1 <;> simp_all [-Vector.eq_mk]
    rw [← VmAirWrapper.rs2_sign_limbs] at imm_sign
    grind

  rcases b_rs2_as with eq_rs2_as_0 | eq_rs2_as_1 <;> simp_all [-Vector.eq_mk]
  . grind

-- include constraints h_last_row balanced_execution balanced_memory balanced_range balanced_bitwise balanced_read
-- lemma looking_for_false : False := by
--   have ⟨ exec_bus, memory_bus, range_bus, readInstr_bus, bitwise_bus ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero (by exact ci ExtF air constraints) h_last_row
--   have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution)

--   have constraints' := constraints
--   rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints'
--   obtain ⟨ b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
--            add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
--            b_rs2_as, rs2_as_imm, imm_sign, imm_sign_extend,
--            timestamp_0, rs2_as_is_valid, timestamp_1, timestamp_2,
--            interactions ⟩ := constraints'
--   clear interactions

--   have ⟨ sop0, sop1, sop2, sop3, sop4 ⟩ := VmAirWrapper_alu.constraints.single_op air 0 (by simp) constraints

--   rw [exec_bus] at balanced_execution
--   rw [memory_bus] at balanced_memory
--   rw [range_bus] at balanced_range
--   rw [readInstr_bus] at balanced_read
--   rw [bitwise_bus] at balanced_bitwise

--   have is_add : air.core.opcode_xor_flag 0 0 = 1 := by sorry
--   have is_imm : air.adapter.rs2_as 0 0 = 0 := by sorry

--   simp_all

--   -- Check what's in execution
--   apply VmAirWrapper_alu.buses.executionBus_balanced_row at balanced_execution
--   simp_all [-Vector.eq_mk]

--   -- Check what's in read
--   apply VmAirWrapper_alu.buses.readInstructionBus_balanced_row at balanced_read
--   simp_all [-Vector.eq_mk]
--   obtain ⟨ eq_pc, eq_opcode, eq_rd, eq_rs1, eq_rs2, eq_u0, eq_rs2_as, eq_u1, eq_u2 ⟩ := balanced_read

--   -- Check what's in range
--   apply VmAirWrapper_alu.buses.rangeBus_balanced_row at balanced_range
--   simp_all
--   obtain ⟨ br0, br1, br2, br3 ⟩ := balanced_range

--   -- Check what's in bitwise
--   apply VmAirWrapper_alu.buses.bitwiseBus_balanced_row at balanced_bitwise
--   simp [← BaseAluCoreAir.x_0_def, ← BaseAluCoreAir.x_1_def,
--         ← BaseAluCoreAir.x_2_def, ← BaseAluCoreAir.x_3_def,
--         ← BaseAluCoreAir.y_0_def, ← BaseAluCoreAir.y_1_def,
--         ← BaseAluCoreAir.y_2_def, ← BaseAluCoreAir.y_3_def,
--         ← BaseAluCoreAir.x_xor_y_0_def, ← BaseAluCoreAir.x_xor_y_1_def,
--         ← BaseAluCoreAir.x_xor_y_2_def, ← BaseAluCoreAir.x_xor_y_3_def] at balanced_bitwise
--   simp_all
--   obtain ⟨ bb0, bb1, bb2, bb3 ⟩ := balanced_bitwise

--   -- Check what's in memory
--   apply VmAirWrapper_alu.buses.memoryBus_balanced_row at balanced_memory
--   simp_all [-Vector.eq_mk]
--   obtain ⟨ bm0, ⟨ eq_b0, eq_b1, eq_b2, eq_b3 ⟩, bm2, ⟨ eq_c0, eq_c1, eq_c2, eq_c3 ⟩ ⟩ := balanced_memory

--   rw [← VmAirWrapper.rs2_imm_def] at *
--   rw [← VmAirWrapper.rs2_sign_limbs] at *

--   have sgn_is_neg_2 : air.core.c_2 0 0 = 255 := by sorry
--   have sgn_is_neg_3 : air.core.c_3 0 0 = 255 := by omega
--   have ⟨ imm_0_0, imm_0_1 ⟩ : air.core.c_0 0 0 = 0 ∧ air.core.c_1 0 0 = 0 := by sorry
--   simp_all [-Vector.eq_mk]

include constraints h_last_row balanced_execution balanced_memory balanced_bitwise in
/-- The `a` operand is range-constrained by logic and bus balancing -/
lemma eq_a
:
  air.core.a_0 0 0 = a0 ∧
  air.core.a_1 0 0 = a1 ∧
  air.core.a_2 0 0 = a2 ∧
  air.core.a_3 0 0 = a3 ∧
  a0.val < 256 ∧ a1.val < 256 ∧ a2.val < 256 ∧ a3.val < 256
:= by
  have ⟨ exec_bus, memory_bus, range_bus, readInstr_bus, bitwise_bus ⟩ := VmAirWrapper_alu.buses.buses_last_row_zero (by exact ci ExtF air constraints) h_last_row
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution)
  have constraints' := constraints
  rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints'
  obtain ⟨ b_add, b_sub, b_xor, b_or, b_and, b_is_valid, rest ⟩ := constraints'
  clear rest

  have ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩
  :
    air.core.a_0 0 0 = a0 ∧ air.core.a_1 0 0 = a1 ∧ air.core.a_2 0 0 = a2 ∧ air.core.a_3 0 0 = a3
  := by
    rw [memory_bus] at balanced_memory
    apply VmAirWrapper_alu.buses.memoryBus_balanced_row at balanced_memory
    simp_all

  rw [bitwise_bus] at balanced_bitwise
  apply VmAirWrapper_alu.buses.bitwiseBus_balanced_row at balanced_bitwise
  simp [is_valid,
          ← BaseAluCoreAir.x_0_def, ← BaseAluCoreAir.x_1_def,
          ← BaseAluCoreAir.x_2_def, ← BaseAluCoreAir.x_3_def] at balanced_bitwise
  obtain ⟨ ba0, ba1, ba2, ba3, ba4 ⟩ := balanced_bitwise

  simp_all

  have ⟨ sop0, sop1, sop2, sop3, sop4 ⟩ := VmAirWrapper_alu.constraints.single_op air 0 (by simp) constraints
  clear *- b_add b_sub b_xor b_or b_and is_valid ba0 ba1 ba2 ba3 sop0 sop1 sop2 sop3 sop4 eq_a0 eq_a1 eq_a2 eq_a3

  rcases b_add <;> [ skip; simp_all ]
  rcases b_sub <;> [ skip; simp_all ]
  rcases b_xor <;> rcases b_and <;> rcases b_or <;> simp_all

  all_goals
    simp [← BaseAluCoreAir.x_xor_y_0_def, ← BaseAluCoreAir.x_xor_y_1_def,
          ← BaseAluCoreAir.x_xor_y_2_def, ← BaseAluCoreAir.x_xor_y_3_def,
          ← BaseAluCoreAir.y_0_def, ← BaseAluCoreAir.y_1_def,
          ← BaseAluCoreAir.y_2_def, ← BaseAluCoreAir.y_3_def] at ba0 ba1 ba2 ba3
    obtain ⟨ ba00, ba01, ba02, ba03 ⟩ := ba0
    obtain ⟨ ba10, ba11, ba12, ba13 ⟩ := ba1
    obtain ⟨ ba20, ba21, ba22, ba23 ⟩ := ba2
    obtain ⟨ ba30, ba31, ba32, ba33 ⟩ := ba3
    simp_all
  . have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba00 ba01 ba03
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba10 ba11 ba13
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba20 ba21 ba23
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_or ba30 ba31 ba33
    grind
  . have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba00 ba01 ba03
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba10 ba11 ba13
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba20 ba21 ba23
    have := VmAirWrapper_alu.auxiliaries.FBB_xor_as_and ba30 ba31 ba33
    grind

section add

include constraints h_last_row balanced_execution balanced_memory balanced_read balanced_bitwise in
/-- The `ADD` opcode is implemented as per the RISC-V spec -/
theorem spec_add
  (h_add : opcode = 512)
  (h_not_imm : rs2_as = 1)
:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3] = execute_RTYPE_pure_U32 b c .ADD
:= by
  -- Get relevant previous info
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution)
  obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3, ub_a0, ub_a1, ub_a2, ub_a3 ⟩ := eq_a (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution) (balanced_memory := balanced_memory) (balanced_bitwise := balanced_bitwise)
  have h_eq_b := eq_b (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution) (balanced_memory := balanced_memory)
  have h_eq_c_non_imm := eq_c (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution) (balanced_memory := balanced_memory) (balanced_bitwise := balanced_bitwise)

  -- Isolate relevant constraints
  have constraints' := constraints
  rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints'
  obtain ⟨ b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rest ⟩ := constraints'
  clear sub_0 sub_1 sub_2 sub_3 rest

  -- Get more detailed b-related information
  obtain ⟨ eq_b0, eq_b1, eq_b2, eq_b3,
           ub_b0, ub_b1, ub_b2, ub_b3,
           eqv_b0, eqv_b1, eqv_b2, eqv_b3 ⟩ := h_eq_b

  -- The operation is not immediate and the opcode is ADD
  obtain ⟨ non_imm, is_add ⟩ : air.adapter.rs2_as 0 0 = 1 ∧ air.core.opcode_add_flag 0 0 = 1 := by
    have ⟨ exec_bus, memory_bus, range_bus, readInstr_bus, bitwise_bus ⟩ :=
      VmAirWrapper_alu.buses.buses_last_row_zero
      (by exact ci ExtF air constraints)
      h_last_row
    rw [readInstr_bus] at balanced_read
    simp [VmAirWrapper_alu.buses.readInstructionBus_row,
          InteractionList.balanced_by_ordered,
          Interaction.balances,
          Interaction.readInstructionBus_entry,
          h_add, h_not_imm, is_valid] at balanced_read
    rw [← BaseAluCoreAir.ctx.instruction.opcode_def] at balanced_read
    obtain ⟨ _, _, opcode_eq, _, _, _, _, eq_rs2_as, _ ⟩ := balanced_read
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
    simp [Vector.get] at *
    simp [← eqv_b0, ← eqv_b1, ← eqv_b2, ← eqv_b3,
          ← eqv_c0, ← eqv_c1, ← eqv_c2, ← eqv_c3] at *
    clear *- add_0 add_1 add_2 add_3 ub_a0 ub_a1 ub_a2 ub_a3
             ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
    rcases add_0 <;> rcases add_1 <;>
    rcases add_2 <;> rcases add_3 <;>
    simp_all <;> omega

end add

section sub

include constraints h_last_row balanced_execution balanced_memory balanced_read balanced_bitwise in
/-- The `SUB` opcode is implemented as per the RISC-V spec -/
theorem spec_sub
  (h_add : opcode = 513)
  (h_not_imm : rs2_as = 1)
:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3] = execute_RTYPE_pure_U32 b c .SUB
:= by
  -- Get relevant previous info
  have is_valid := is_valid (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution)
  obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3, ub_a0, ub_a1, ub_a2, ub_a3 ⟩ := eq_a (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution) (balanced_memory := balanced_memory) (balanced_bitwise := balanced_bitwise)
  have h_eq_b := eq_b (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution) (balanced_memory := balanced_memory)
  have h_eq_c_non_imm := eq_c (constraints := constraints) (h_last_row := h_last_row) (balanced_execution := balanced_execution) (balanced_memory := balanced_memory) (balanced_bitwise := balanced_bitwise)

  -- Isolate relevant constraints
  have constraints' := constraints
  rw [VmAirWrapper_alu.constraints.allHold_constraints] at constraints'
  obtain ⟨ b_add, b_sub, b_xor, b_or, b_and, b_is_valid,
           add_0, sub_0, add_1, sub_1, add_2, sub_2, add_3, sub_3,
           b_rs2_as, rest ⟩ := constraints'
  clear add_0 add_1 add_2 add_3 rest

  -- Get more detailed b-related information
  obtain ⟨ eq_b0, eq_b1, eq_b2, eq_b3,
           ub_b0, ub_b1, ub_b2, ub_b3,
           eqv_b0, eqv_b1, eqv_b2, eqv_b3 ⟩ := h_eq_b

  -- The operation is not immediate and the opcode is ADD
  obtain ⟨ non_imm, is_sub ⟩ : air.adapter.rs2_as 0 0 = 1 ∧ air.core.opcode_sub_flag 0 0 = 1 := by
    have ⟨ exec_bus, memory_bus, range_bus, readInstr_bus, bitwise_bus ⟩ :=
      VmAirWrapper_alu.buses.buses_last_row_zero
      (by exact ci ExtF air constraints)
      h_last_row
    rw [readInstr_bus] at balanced_read
    simp [VmAirWrapper_alu.buses.readInstructionBus_row,
          InteractionList.balanced_by_ordered,
          Interaction.balances,
          Interaction.readInstructionBus_entry,
          h_add, h_not_imm, is_valid] at balanced_read
    rw [← BaseAluCoreAir.ctx.instruction.opcode_def] at balanced_read
    obtain ⟨ _, _, opcode_eq, _, _, _, _, eq_rs2_as, _ ⟩ := balanced_read
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
    simp [Vector.get] at *
    simp [← eqv_b0, ← eqv_b1, ← eqv_b2, ← eqv_b3,
          ← eqv_c0, ← eqv_c1, ← eqv_c2, ← eqv_c3] at *
    clear *- sub_0 sub_1 sub_2 sub_3 ub_a0 ub_a1 ub_a2 ub_a3
             ub_b0 ub_b1 ub_b2 ub_b3 ub_c0 ub_c1 ub_c2 ub_c3
    rcases sub_0 <;> rcases sub_1 <;>
    rcases sub_2 <;> rcases sub_3 <;>
    simp_all <;> omega

end sub
