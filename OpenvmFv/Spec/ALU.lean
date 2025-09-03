import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Constraints.VmAirWrapper_alu
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_alu FBB ExtF)
variable (h_last_row : air.last_row = 0)
variable (constraints : VmAirWrapper_alu.constraints.allHold air 0 (by simp))

variable {mul00 pc00 t00 mul01 pc01 t01}
         (balanced_execution :
          InteractionList.balanced_by_ordered
            (air.buses ExecutionBus)
            [
              Interaction.executionBus_entry mul00 pc00 t00,
              Interaction.executionBus_entry mul01 pc01 t01,
            ]
         )

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

variable {mul pc opcode rd rs1 rs2 unknown0 rs2_as unknown1 unknown2}
         (balanced_read :
          InteractionList.balanced_by_ordered
            (air.buses ReadInstructionBus)
            [
              Interaction.readInstructionBus_entry mul pc opcode rd rs1 rs2 unknown0 rs2_as unknown1 unknown2,
            ]
         )

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

set_option maxHeartbeats 0
theorem spec_add


:
  U32.toBV #v[↑a0, ↑a1, ↑a2, ↑a3] = execute_RTYPE_pure_U32 b c .ADD ∧
  b = #v[↑b0, ↑b1, ↑b2, ↑b3] ∧
  c = #v[↑c0, ↑c1, ↑c2, ↑c3] ∧
  next_pc = pc + 4 ∧
  next_timestamp = timestamp + 3 ∧
  rs1_prev_timestamp.val < timestamp.val ∧
  rs2_prev_timestamp.val < timestamp.val + 1 ∧
  rd_prev_timestamp.val < timestamp.val + 2
:= by
  obtain ⟨
      h_0,
      h_1,
      h_2,
      h_3,
      h_4,
      h_5,
      h_6,
      h_7,
      h_8,
      h_9,
      h_10,
      h_11,
      h_12,
      h_13,
      h_14,
      h_15,
      h_16,
      h_17,
      h_18,
      h_19,
      h_20,
      h_21,
      h_interactions
  ⟩ := (VmAirWrapper_alu.constraints.allHold_constraints air 0 (by grind)).mp h_constraints
  clear h_constraints
  replace h_interactions := VmAirWrapper_alu.constraints.constrain_interactions' air h_interactions
  simp [h_last_row] at h_interactions
  rewrite [h_interactions] at h_execution h_memory h_range_check h_read_instruction h_bitwise
  simp at h_execution h_memory h_range_check h_read_instruction h_bitwise
  clear h_interactions
  -- use execution bus
  have h_is_valid : air.core.is_valid 0 0 = 1 := by
    apply Interaction.balanced_by_ordered_head_multiplicity at h_execution
    grind
  have h_pc : air.adapter.from_state.pc 0 0 = pc := by
    apply Interaction.balanced_by_ordered_head_data at h_execution
    grind
  have h_timestamp : air.adapter.from_state.timestamp 0 0 = timestamp := by
    apply Interaction.balanced_by_ordered_head_data at h_execution
    grind
  have h_next_pc : next_pc = pc + 4 := by
    apply Interaction.balanced_by_ordered_tail at h_execution
    apply Interaction.balanced_by_ordered_head_data at h_execution
    grind
  have h_next_timestamp : next_timestamp = timestamp + 3 := by
    apply Interaction.balanced_by_ordered_tail at h_execution
    apply Interaction.balanced_by_ordered_head_data at h_execution
    grind
  clear h_execution

  -- use read instruction bus
  unfold readInstruction_add at h_read_instruction
  have h_opcode : (air.core.ctx 0 0).instruction.opcode = 512 := by
    apply Interaction.balanced_by_ordered_head_data at h_read_instruction
    grind
  have h_flags :
    air.core.opcode_add_flag 0 0 = 1 ∧
    air.core.opcode_sub_flag 0 0 = 0 ∧
    air.core.opcode_xor_flag 0 0 = 0 ∧
    air.core.opcode_or_flag 0 0 = 0 ∧
    air.core.opcode_and_flag 0 0 = 0
  := by
    apply flags_of_opcode_512 h_0 h_1 h_2 h_3 h_4 h_is_valid
    unfold Valid_BaseAluCoreAir.ctx Valid_BaseAluCoreAir.class_offset at h_opcode
    simp at h_opcode
    exact h_opcode
  obtain ⟨h_add_flag, h_sub_flag, h_xor_flag, h_or_flag, h_and_flag⟩ := h_flags
  have h_rd : air.adapter.rd_ptr 0 0 = rd := by
    apply Interaction.balanced_by_ordered_head_data at h_read_instruction
    grind
  have h_rs1 : air.adapter.rs1_ptr 0 0 = rs1 := by
    apply Interaction.balanced_by_ordered_head_data at h_read_instruction
    grind
  have h_rs2 : air.adapter.rs2 0 0 = rs2 := by
    apply Interaction.balanced_by_ordered_head_data at h_read_instruction
    grind
  have h_rs2_as : air.adapter.rs2_as 0 0 = 1 := by
    apply Interaction.balanced_by_ordered_head_data at h_read_instruction
    grind
  clear h_read_instruction

  -- use bitwise bus
  simp [
    Valid_BaseAluCoreAir.x_0.eq_def,
    Valid_BaseAluCoreAir.x_1.eq_def,
    Valid_BaseAluCoreAir.x_2.eq_def,
    Valid_BaseAluCoreAir.x_3.eq_def,
    Valid_BaseAluCoreAir.y_0.eq_def,
    Valid_BaseAluCoreAir.y_1.eq_def,
    Valid_BaseAluCoreAir.y_2.eq_def,
    Valid_BaseAluCoreAir.y_3.eq_def,
    Valid_BaseAluCoreAir.x_xor_y_0.eq_def,
    Valid_BaseAluCoreAir.x_xor_y_1.eq_def,
    Valid_BaseAluCoreAir.x_xor_y_2.eq_def,
    Valid_BaseAluCoreAir.x_xor_y_3.eq_def,
    Valid_BaseAluCoreAir.bitwise,
    h_xor_flag, h_or_flag, h_and_flag,
    word_bytes_bitwiseBus_entries.eq_def,
    h_is_valid
  ] at h_bitwise
  have h_core_a_0_range : (air.core.a_0 0 0).val < 256 := by
    apply Interaction.balanced_by_ordered_head_data at h_bitwise
    apply range_of_eq_bitvec_8 bitwise_word[0]
    simp at h_bitwise
    simp [h_bitwise]
    exact Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_2 bitwise_word)
  have h_core_a_1_range : (air.core.a_1 0 0).val < 256 := by
    apply Interaction.balanced_by_ordered_tail at h_bitwise
    apply Interaction.balanced_by_ordered_head_data at h_bitwise
    apply range_of_eq_bitvec_8 bitwise_word[1]
    simp at h_bitwise
    simp [h_bitwise]
    exact Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_4 bitwise_word)
  have h_core_a_2_range : (air.core.a_2 0 0).val < 256 := by
    apply Interaction.balanced_by_ordered_tail at h_bitwise
    apply Interaction.balanced_by_ordered_tail at h_bitwise
    apply Interaction.balanced_by_ordered_head_data at h_bitwise
    apply range_of_eq_bitvec_8 bitwise_word[2]
    simp at h_bitwise
    simp [h_bitwise]
    exact Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_6 bitwise_word)
  have h_core_a_3_range : (air.core.a_3 0 0).val < 256 := by
    apply Interaction.balanced_by_ordered_tail at h_bitwise
    apply Interaction.balanced_by_ordered_tail at h_bitwise
    apply Interaction.balanced_by_ordered_tail at h_bitwise
    apply Interaction.balanced_by_ordered_head_data at h_bitwise
    apply range_of_eq_bitvec_8 bitwise_word[3]
    simp at h_bitwise
    simp [h_bitwise]
    exact Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_8 bitwise_word)
  clear h_bitwise

  -- use range check
  have h_reads_aux_0_lower_decomp_0_range :
    (air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 0 0).val < 2^17
  := by
    apply Interaction.balanced_by_ordered_head_data at h_range_check
    unfold range_bus_entry at h_range_check
    simp at h_range_check
    rewrite [h_range_check]
    simp
    exact val_mod_bb_lt_two_pow_17 range_val0
  have h_reads_aux_0_lower_decomp_1_range :
    (air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 0 0).val < 2^12
  := by
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_head_data at h_range_check
    unfold range_bus_entry at h_range_check
    simp at h_range_check
    rewrite [h_range_check]
    simp
    exact val_mod_bb_lt_two_pow_12 range_val1
  have h_reads_aux_1_lower_decomp_0_range :
    (air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 0 0).val < 2^17
  := by
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_head_data at h_range_check
    unfold range_bus_entry at h_range_check
    simp at h_range_check
    rewrite [h_range_check]
    simp
    exact val_mod_bb_lt_two_pow_17 range_val2
  have h_reads_aux_1_lower_decomp_1_range :
    (air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 0 0).val < 2^12
  := by
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_head_data at h_range_check
    unfold range_bus_entry at h_range_check
    simp at h_range_check
    rewrite [h_range_check]
    simp
    exact val_mod_bb_lt_two_pow_12 range_val3
  have h_writes_aux_lower_decomp_0_range :
    (air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 0 0).val < 2^17
  := by
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_head_data at h_range_check
    unfold range_bus_entry at h_range_check
    simp at h_range_check
    rewrite [h_range_check]
    simp
    exact val_mod_bb_lt_two_pow_17 range_val4
  have h_writes_aux_lower_decomp_1_range :
    (air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 0 0).val < 2^12
  := by
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_tail at h_range_check
    apply Interaction.balanced_by_ordered_head_data at h_range_check
    unfold range_bus_entry at h_range_check
    simp at h_range_check
    rewrite [h_range_check]
    simp
    exact val_mod_bb_lt_two_pow_12 range_val5
  clear h_range_check

  -- use memory bus
  simp [
    write_word_memoryBus_entry.eq_def,
    read_word_memoryBus_entry.eq_def,
    *
  ] at h_memory
  have h_core_b_0 : air.core.b_0 0 0 = b[0].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.1]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_2 b))
  have h_core_b_1 : air.core.b_1 0 0 = b[1].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.1]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_4 b))
  have h_core_b_2 : air.core.b_2 0 0 = b[2].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.2.1]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_6 b))
  have h_core_b_3 : air.core.b_3 0 0 = b[3].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.2.2.1]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_8 b))
  have h_rs1_prev_timestamp : air.adapter.reads_aux_0.base.prev_timestamp 0 0 = rs1_prev_timestamp := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.2.2.2]
  apply Interaction.balanced_by_ordered_tail at h_memory
  have h_b0 : air.core.b_0 0 0 = b0 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  have h_b1 : air.core.b_1 0 0 = b1 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  have h_b2 : air.core.b_2 0 0 = b2 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  have h_b3 : air.core.b_3 0 0 = b3 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  apply Interaction.balanced_by_ordered_tail at h_memory
  have h_core_c_0 : air.core.c_0 0 0 = (c)[0].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.1]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_2 c))
  have h_core_c_1 : air.core.c_1 0 0 = (c)[1].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.1]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_4 c))
  have h_core_c_2 : air.core.c_2 0 0 = (c)[2].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.2.1]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_6 c))
  have h_core_c_3 : air.core.c_3 0 0 = (c)[3].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.2.2]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_8 c))
  have h_rs2_prev_timestamp : air.adapter.reads_aux_1.base.prev_timestamp 0 0 = rs2_prev_timestamp := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.2.2.2]
  apply Interaction.balanced_by_ordered_tail at h_memory
  have h_c0 : air.core.c_0 0 0 = c0 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  have h_c1 : air.core.c_1 0 0 = c1 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  have h_c2 : air.core.c_2 0 0 = c2 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  have h_c3 : air.core.c_3 0 0 = c3 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  apply Interaction.balanced_by_ordered_tail at h_memory
  have h_prev_data_0 : air.adapter.writes_aux.prev_data_0 0 0 = prev_data[0].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.1]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_2 prev_data))
  have h_prev_data_1 : air.adapter.writes_aux.prev_data_1 0 0 = prev_data[1].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.1]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_4 prev_data))
  have h_prev_data_2 : air.adapter.writes_aux.prev_data_2 0 0 = prev_data[2].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.2.1]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_6 prev_data))
  have h_prev_data_3 : air.adapter.writes_aux.prev_data_3 0 0 = prev_data[3].toNat := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.2.2]
    exact Eq.symm (Fin.natCast_eq_mk (write_word_memoryBus_entry._proof_8 prev_data))
  have h_rd_prev_timestamp : air.adapter.writes_aux.base.prev_timestamp 0 0 = rd_prev_timestamp := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    simp at h_memory
    simp [h_memory.2.2.2.2]
  apply Interaction.balanced_by_ordered_tail at h_memory
  have h_a0 : air.core.a_0 0 0 = a0 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  have h_a1 : air.core.a_1 0 0 = a1 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  have h_a2 : air.core.a_2 0 0 = a2 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  have h_a3 : air.core.a_3 0 0 = a3 := by
    apply Interaction.balanced_by_ordered_head_data at h_memory
    grind
  clear h_memory

  unfold Valid_BaseAluCoreAir.carry_add_3 Valid_BaseAluCoreAir.carry_divide at h_12
  unfold Valid_BaseAluCoreAir.carry_add_2 Valid_BaseAluCoreAir.carry_divide at h_10 h_12
  unfold Valid_BaseAluCoreAir.carry_add_1 Valid_BaseAluCoreAir.carry_divide at h_8 h_10 h_12
  unfold Valid_BaseAluCoreAir.carry_add_0 Valid_BaseAluCoreAir.carry_divide at h_6 h_8 h_10 h_12

  have h_b : b = #v[↑b0, ↑b1, ↑b2, ↑b3] := by
    simp
    apply Array.ext
    . grind
    . simp
      intro i hi _
      match i with
        | 0 =>
          simp [←h_b0, h_core_b_0]
          simp (disch := omega) [Nat.mod_eq_of_lt]
        | 1 =>
          simp [←h_b1, h_core_b_1]
          simp (disch := omega) [Nat.mod_eq_of_lt]
        | 2 =>
          simp [←h_b2, h_core_b_2]
          simp (disch := omega) [Nat.mod_eq_of_lt]
        | 3 =>
          simp [←h_b3, h_core_b_3]
          simp (disch := omega) [Nat.mod_eq_of_lt]
    done
  have h_c : c = #v[↑c0, ↑c1, ↑c2, ↑c3] := by
    simp
    apply Array.ext
    . grind
    . simp
      intro i hi _
      match i with
        | 0 =>
          simp [←h_c0, h_core_c_0]
          simp (disch := omega) [Nat.mod_eq_of_lt]
        | 1 =>
          simp [←h_c1, h_core_c_1]
          simp (disch := omega) [Nat.mod_eq_of_lt]
        | 2 =>
          simp [←h_c2, h_core_c_2]
          simp (disch := omega) [Nat.mod_eq_of_lt]
        | 3 =>
          simp [←h_c3, h_core_c_3]
          simp (disch := omega) [Nat.mod_eq_of_lt]
  simp [h_b, h_c, h_next_pc, h_next_timestamp]
  clear h_last_row
    h_0 h_1 h_2 h_3 h_4 h_5 --flags boolean
    h_7 h_9 h_11 h_13 -- sub
    h_14 h_15 h_16 h_17 --addi
    h_19 --superfluous?
  simp [U32.toBV]
  have (n: ℕ) (h: n < 2^8) : BitVec.ofFin ⟨n, h⟩ = BitVec.ofNat 8 n := by
    exact BitVec.ofFin_eq_ofNat
  simp [this]
  rewrite [h_a0] at h_core_a_0_range h_6 h_8 h_10 h_12
  rewrite [h_a1] at h_core_a_1_range h_8 h_10 h_12
  rewrite [h_a2] at h_core_a_2_range h_10 h_12
  rewrite [h_a3] at h_core_a_3_range h_12
  rewrite [h_b0] at h_core_b_0 h_6 h_8 h_10 h_12
  rewrite [h_b1] at h_core_b_1 h_8 h_10 h_12
  rewrite [h_b2] at h_core_b_2 h_10 h_12
  rewrite [h_b3] at h_core_b_3 h_12
  rewrite [h_c0] at h_core_c_0 h_6 h_8 h_10 h_12
  rewrite [h_c1] at h_core_c_1 h_8 h_10 h_12
  rewrite [h_c2] at h_core_c_2 h_10 h_12
  rewrite [h_c3] at h_core_c_3 h_12
  have h_core_b_0_range := range_of_eq_bitvec_8 _ _ h_core_b_0.symm
  have h_core_b_1_range := range_of_eq_bitvec_8 _ _ h_core_b_1.symm
  have h_core_b_2_range := range_of_eq_bitvec_8 _ _ h_core_b_2.symm
  have h_core_b_3_range := range_of_eq_bitvec_8 _ _ h_core_b_3.symm
  have h_core_c_0_range := range_of_eq_bitvec_8 _ _ h_core_c_0.symm
  have h_core_c_1_range := range_of_eq_bitvec_8 _ _ h_core_c_1.symm
  have h_core_c_2_range := range_of_eq_bitvec_8 _ _ h_core_c_2.symm
  have h_core_c_3_range := range_of_eq_bitvec_8 _ _ h_core_c_3.symm
  rewrite [
    Nat.mod_eq_of_lt h_core_a_0_range,
    Nat.mod_eq_of_lt h_core_a_1_range,
    Nat.mod_eq_of_lt h_core_a_2_range,
    Nat.mod_eq_of_lt h_core_a_3_range,
    Nat.mod_eq_of_lt h_core_b_0_range,
    Nat.mod_eq_of_lt h_core_b_1_range,
    Nat.mod_eq_of_lt h_core_b_2_range,
    Nat.mod_eq_of_lt h_core_b_3_range,
    Nat.mod_eq_of_lt h_core_c_0_range,
    Nat.mod_eq_of_lt h_core_c_1_range,
    Nat.mod_eq_of_lt h_core_c_2_range,
    Nat.mod_eq_of_lt h_core_c_3_range,
  ]
  simp [h_timestamp, h_rs1_prev_timestamp, h_is_valid] at h_18
  simp [h_timestamp, h_rs2_prev_timestamp, h_rs2_as] at h_20
  simp [h_timestamp, h_rd_prev_timestamp, h_is_valid] at h_21

  have : rs1_prev_timestamp < timestamp := by
    have h_18' := combine_range_check _ _
      h_reads_aux_0_lower_decomp_0_range
      h_reads_aux_0_lower_decomp_1_range
    simp [←h_18] at h_18'; clear h_18
    have h_18 := diff_of_range_check _ _
      h_18'
      (by omega)
      (by omega)
    simp at h_18
    simp [h_18]
  simp [this]; clear this
  have : rs2_prev_timestamp.val < timestamp.val + 1 := by
    have h_20' := combine_range_check _ _
      h_reads_aux_1_lower_decomp_0_range
      h_reads_aux_1_lower_decomp_1_range
    simp [←h_20] at h_20'; clear h_20
    have h_20 := diff_of_range_check _ _
      h_20'
      (by omega)
      (by omega)
    simp at h_20
    omega
  simp [this]; clear this
  have : rd_prev_timestamp.val < timestamp.val + 2 := by
    have h_21' := combine_range_check _ _
      h_writes_aux_lower_decomp_0_range
      h_writes_aux_lower_decomp_1_range
    simp [←h_21] at h_21';
    have h_21 := diff_of_range_check _ _
      h_21'
      (by omega)
      (by omega)
    omega
  simp [this]; clear this

  simp [h_add_flag] at h_6 h_8 h_10 h_12
  -- have h_6' : a0.val = b0.val + c0.val ∨ a0.val = b0.val + c0.val - 256 := by
  --   cases h_6 with
  --     | inl h_6 =>
  --       left
  --       rewrite [←h_6]
  --       omega
  --     | inr h_6 =>
  --       right
  --       apply BabyBear.inv_256_eq_256_lr.mp at h_6
  --       omega
  -- cases h_6' with
  --   | inl h_6' =>
  --     rewrite [h_6', BitVec.ofNat_add]
  --   | inr h_6' => done


  -- -- cases h_6 <;> cases h_8 <;> cases h_10 <;> cases h_12

  -- -- cases h_6 with
  -- --   | inl h_6 =>
  -- --     simp [h_6] at h_8 h_10 h_12
  -- --     cases h_8 with
  -- --       | inl h_8 =>
  -- --         simp [assert_eq] at h_8
  -- --         simp [h_8] at h_10 h_12
  -- --         cases h_10 with
  -- --           | inl h_10 =>
  -- --             simp [assert_eq] at h_10
  -- --             simp [h_10] at h_12
  -- --             cases h_12 with
  -- --               | inl h_12 =>
  -- --                 simp [assert_eq] at h_12
  -- --                 done
  -- --               | inr h_12 =>
  -- --                 apply BabyBear.inv_256_eq_256_lr.mp at h_12
  -- --                 apply eq_add_of_sub_eq at h_12
  -- --                 done
  -- --           | inr h_10 =>
  -- --             apply BabyBear.inv_256_eq_256_lr.mp at h_10
  -- --             apply eq_add_of_sub_eq at h_10
  -- --             simp [h_10] at h_12
  -- --             cases h_12 with
  -- --               | inl h_12 =>
  -- --                 apply eq_add_of_sub_eq at h_12
  -- --                 done
  -- --               | inr h_12 =>
  -- --                 apply BabyBear.inv_256_eq_256_lr.mp at h_12
  -- --                 apply eq_add_of_sub_eq at h_12
  -- --                 done
  -- --             done
  -- --       | inr h_8 =>
  -- --         done
  -- --     done
  -- --   | inr h_6 =>
  -- --     have := BabyBear.inv_256_eq_256_lr.mp h_6
  -- --     done



  -- -- simp [*] at *
  done


  -- simp [*] at *
  -- have h_is_valid_1 : air.core.is_valid 0 0 = 1 := by
  --   unfold Valid_BaseAluCoreAir.is_valid at h_5 ⊢
  --   simp [h_is_add] at h_5
  --   have := flag1_exclusive_of_is_valid_binary h_1 h_2 h_3 h_4 h_5
  --   grind
  -- simp [h_is_valid_1] at *
  -- have :
  --   air.adapter.from_state.pc 0 0 = pc ∧
  --   (air.core.ctx 0 0).instruction.opcode = 512 ∧
  --   air.adapter.rd_ptr 0 0 = rd ∧
  --   air.adapter.rs1_ptr 0 0 = rs1 ∧
  --   air.adapter.rs2 0 0 = rs2 ∧
  --   air.adapter.rs2_as 0 0 = 1
  -- := eq_of_readInstruction_add_balanced h_read_instruction
  -- clear h_read_instruction
  -- obtain ⟨h_pc, h_opcode, h_rd, h_rs1, h_rs2, h_rs2_as⟩ := this
  -- simp [*] at *
  -- simp [write_word_memoryBus_entry.eq_def, read_word_memoryBus_entry.eq_def] at h_memory
  -- unfold word_bytes_bitwiseBus_entries at h_bitwise
  -- -- TODO
  --   -- show that x_0, x_1, ... = y_0, y_1, ... = a_0, a_1, ...
  --   -- because all -1 mult elements of h_bitwise are < 256, all +1 mult elements of h_bitwise are < 256
  --   -- this range checks a
  --   -- then, case on memory bus entries pairing off correctly (started below)
  -- -- by_cases h_memory_matches :
  -- --   air.core.b_0 0 0 = ↑b[0].toNat ∧
  -- --   air.core.b_1 0 0 = ↑b[1].toNat ∧
  -- --   air.core.b_2 0 0 = ↑b[2].toNat ∧
  -- --   air.core.b_3 0 0 = ↑b[3].toNat ∧
  -- --   air.adapter.reads_aux_0.base.prev_timestamp 0 0 = rs1_prev_timestamp ∧
  -- --   air.adapter.from_state.timestamp 0 0 = timestamp ∧
  -- --   air.core.c_0 0 0 = ↑(c)[0].toNat ∧
  -- --   air.core.c_1 0 0 = ↑(c)[1].toNat ∧
  -- --   air.core.c_2 0 0 = ↑(c)[2].toNat ∧
  -- --   air.core.c_3 0 0 = ↑(c)[3].toNat ∧
  -- --   air.adapter.reads_aux_1.base.prev_timestamp 0 0 = rs2_prev_timestamp ∧
  -- --   air.adapter.writes_aux.prev_data_0 0 0 = ↑prev_data[0].toNat ∧
  -- --   air.adapter.writes_aux.prev_data_1 0 0 = ↑prev_data[1].toNat ∧
  -- --   air.adapter.writes_aux.prev_data_2 0 0 = ↑prev_data[2].toNat ∧
  -- --   air.adapter.writes_aux.prev_data_3 0 0 = ↑prev_data[3].toNat ∧
  -- --   air.adapter.writes_aux.base.prev_timestamp 0 0 = rd_prev_timestamp ∧
  -- --   air.core.a_0 0 0 = ↑a[0].toNat ∧
  -- --   air.core.a_1 0 0 = ↑a[1].toNat ∧
  -- --   air.core.a_2 0 0 = ↑a[2].toNat ∧
  -- --   air.core.a_3 0 0 = ↑a[3].toNat



  -- -- -- simp_all

  -- -- -- unfold BitwiseBus ExecutionBus MemoryBus RangeCheckerBus ReadInstructionBus at h_bitwise
  -- -- -- simp at h_bitwise

  -- -- -- have : c.core.is_valid 0 0 = 1 := by sorry
  -- -- -- simp [this] at h_bitwise
  -- -- -- unfold Valid_BaseAluCoreAir.x_0 at h_bitwise

  -- -- done
