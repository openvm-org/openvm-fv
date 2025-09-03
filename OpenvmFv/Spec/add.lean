import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Constraints.VmAirWrapper_alu
import OpenvmFv.Fundamentals.Execution

import LeanZKCircuit.Interactions

variable (ExtF : Type)
variable (air : Valid_VmAirWrapper_alu FBB ExtF)

section bus_interpretation


end bus_interpretation

def read_word_memoryBus_entry
  (x1 x2 x3 x4 ptr : FBB) (timestamp : FBB)
: (FBB × List FBB) :=
  (-1, [1, ptr, x1, x2, x3, x4, timestamp])

def write_word_memoryBus_entry
  (val : U32) (ptr : FBB) (timestamp : FBB)
: (FBB × List FBB) :=
  (1, [1, ptr, val[0], val[1], val[2], val[3], timestamp])

def word_bytes_bitwiseBus_entries
  (val : U32)
: List (FBB × List FBB) :=
  [
    (-1, [val[0], val[0], 0, 1]),
    (-1, [val[1], val[1], 0, 1]),
    (-1, [val[2], val[2], 0, 1]),
    (-1, [val[3], val[3], 0, 1]),
  ]

def readInstruction_add
  (pc rd rs1 rs2 : FBB)
: List (FBB × List FBB) :=
  [(-1, [pc, 512, rd, rs1, rs2, 1, 1, 0, 0])]

lemma get_multiplicity_cons
  {x : F × List F}
  {data : List F}
  [Field F]
  [BEq (List F)]
:
  Interaction.get_multiplicity (x::xs) data =
  (if x.2 == data then x.1 else 0) + Interaction.get_multiplicity xs data
:= by
  unfold Interaction.get_multiplicity
  grind



lemma eq_of_readInstruction_add_balanced
  (h: Interaction.balanced_by
    [(1, [ x1, x2, x3, x4, x5, 1, x6, 0, 0 ])]
    (readInstruction_add y1 y2 y3 y4)
  )
:
  x1 = y1 ∧ x2 = 512 ∧ x3 = y2 ∧ x4 = y3 ∧ x5 = y4 ∧ x6 = 1
:= by
  unfold readInstruction_add Interaction.balanced_by at h
  specialize h [y1, 512, y2, y3, y4, 1, 1, 0, 0]
  unfold Interaction.get_multiplicity at h
  by_contra h
  grind

lemma flag1_exclusive_of_is_valid_binary
  {flag2 flag3 flag4 flag5 : FBB}
  (h_flag2 : flag2 = 0 ∨ flag2 = 1)
  (h_flag3 : flag3 = 0 ∨ flag3 = 1)
  (h_flag4 : flag4 = 0 ∨ flag4 = 1)
  (h_flag5 : flag5 = 0 ∨ flag5 = 1)
  (h_sum :
    1 + flag2 + flag3 + flag4 + flag5 = 0 ∨
    1 + flag2 + flag3 + flag4 + flag5 = 1
  )
:
  flag2 = 0 ∧ flag3 = 0 ∧ flag4 = 0 ∧ flag5 = 0
:= by grind

lemma flag2_exclusive_of_is_valid_binary
  {flag2 flag3 flag4 flag5 : FBB}
  (h_flag1 : flag1 = 0 ∨ flag1 = 1)
  (h_flag3 : flag3 = 0 ∨ flag3 = 1)
  (h_flag4 : flag4 = 0 ∨ flag4 = 1)
  (h_flag5 : flag5 = 0 ∨ flag5 = 1)
  (h_sum :
    flag1 + 1 + flag3 + flag4 + flag5 = 0 ∨
    flag1 + 1 + flag3 + flag4 + flag5 = 1
  )
:
  flag1 = 0 ∧ flag3 = 0 ∧ flag4 = 0 ∧ flag5 = 0
:= by grind

lemma flags_of_opcode_512
  {add_flag sub_flag xor_flag or_flag and_flag: FBB}
  (h_add : add_flag = 0 ∨ add_flag = 1)
  (h_sub : sub_flag = 0 ∨ sub_flag = 1)
  (h_xor : xor_flag = 0 ∨ xor_flag = 1)
  (h_or : or_flag = 0 ∨ or_flag = 1)
  (h_and : and_flag = 0 ∨ and_flag = 1)
  (h_sum :
    add_flag + sub_flag + xor_flag + or_flag + and_flag = 1
  )
  (h_weighted_sum :
    sub_flag + xor_flag * 2 + or_flag * 3 + and_flag * 4 = 0
  )
:
  add_flag = 1 ∧ sub_flag = 0 ∧ xor_flag = 0 ∧ or_flag = 0 ∧ and_flag = 0
:= by
  match add_flag, sub_flag, xor_flag, or_flag, and_flag with
    | 0, 0, 0, 0 , 0 => grind
    | 0, 0, 0, 0 , 1 => grind
    | 0, 0, 0, 1 , 0 => grind
    | 0, 0, 0, 1 , 1 => grind
    | 0, 0, 1, 0 , 0 => grind
    | 0, 0, 1, 0 , 1 => grind
    | 0, 0, 1, 1 , 0 => grind
    | 0, 0, 1, 1 , 1 => grind
    | 0, 1, 0, 0 , 0 => grind
    | 0, 1, 0, 0 , 1 => grind
    | 0, 1, 0, 1 , 0 => grind
    | 0, 1, 0, 1 , 1 => grind
    | 0, 1, 1, 0 , 0 => grind
    | 0, 1, 1, 0 , 1 => grind
    | 0, 1, 1, 1 , 0 => grind
    | 0, 1, 1, 1 , 1 => grind
    | 1, 0, 0, 0 , 0 => grind
    | 1, 0, 0, 0 , 1 => grind
    | 1, 0, 0, 1 , 0 => grind
    | 1, 0, 0, 1 , 1 => grind
    | 1, 0, 1, 0 , 0 => grind
    | 1, 0, 1, 0 , 1 => grind
    | 1, 0, 1, 1 , 0 => grind
    | 1, 0, 1, 1 , 1 => grind
    | 1, 1, 0, 0 , 0 => grind
    | 1, 1, 0, 0 , 1 => grind
    | 1, 1, 0, 1 , 0 => grind
    | 1, 1, 0, 1 , 1 => grind
    | 1, 1, 1, 0 , 0 => grind
    | 1, 1, 1, 0 , 1 => grind
    | 1, 1, 1, 1 , 0 => grind
    | 1, 1, 1, 1 , 1 => grind

namespace Interaction

  def balanced_by_ordered [Field F] (l₁ l₂ : List (F × List F)) : Prop :=
    match l₁, l₂ with
      | [], [] => true
      | _::_, [] => false
      | [], _::_ => false
      | a::as, b::bs =>
        a.2 = b.2 ∧ a.1 + b.1 = 0 ∧ balanced_by_ordered as bs

  lemma balanced_by_ordered_head_multiplicity
    [Field F] {a b: (F × List F)}
    (h: balanced_by_ordered (a::as) (b::bs))
  : a.1 + b.1 = 0 := by
    unfold balanced_by_ordered at h
    grind

  lemma balanced_by_ordered_head_data
    [Field F] {a b: (F × List F)}
    (h: balanced_by_ordered (a::as) (b::bs))
  : a.2 = b.2 := by
    unfold balanced_by_ordered at h
    grind

  lemma balanced_by_ordered_tail
    [Field F] {a b: (F × List F)}
    (h: balanced_by_ordered (a::as) (b::bs))
  : balanced_by_ordered as bs := by
    unfold balanced_by_ordered at h
    grind

end Interaction

lemma range_of_eq_bitvec_8
  (bv: BitVec 8) (x : FBB)
  (h: ↑(bv.toNat) = x)
: x.val < 256
:= by
  have : bv.toNat < 256 := by
    convert BitVec.toNat_lt_twoPow_of_le (show 8 ≤ 8 by trivial)
  rewrite [←h]
  simp
  omega

def range_bus_entry
  (val: Fin k) (_h: l = 2^x)
: FBB × List FBB :=
  (-1, [↑val.val, ↑x])

abbrev two_pow_17 := 131072
lemma two_pow_17_correct : two_pow_17 = 2^17 := by native_decide
lemma val_mod_bb_lt_two_pow_17 (a: Fin two_pow_17)
: a.val % BB_prime < two_pow_17
:= by grind
abbrev two_pow_12 := 4096
lemma two_pow_12_correct : two_pow_12 = 2^12 := by native_decide
lemma val_mod_bb_lt_two_pow_12 (a: Fin two_pow_12)
: a.val % BB_prime < two_pow_12
:= by grind

lemma combine_range_check
  (a b : FBB) (h_a : a.val < 2^17) (h_b : b.val < 2^12)
: (a + b * two_pow_17).val < 2^29 := by
  grind

lemma diff_of_range_check
  (a b: FBB) (h: (a - b - 1).val < 2^29)
: a.val < BB_prime-2^29+1 → b.val < BB_prime-2^29 → b.val < a.val := by
  grind

-- ADD
-- - split a up into 4
set_option maxHeartbeats 0
theorem spec_add
  [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : FBB)
  (b c prev_data: U32)
  (rs1 rs2 rd : FBB)
  (pc next_pc : FBB)
  (timestamp next_timestamp rs1_prev_timestamp rs2_prev_timestamp rd_prev_timestamp: FBB)
  (range_val0 range_val2 range_val4 : Fin two_pow_17)
  (range_val1 range_val3 range_val5 : Fin two_pow_12)
  (bitwise_word : U32)
  (h_last_row : air.last_row = 0)
  (h_constraints : VmAirWrapper_alu.constraints.allHold air 0 (by grind))
  (h_execution : Interaction.balanced_by_ordered
    (air.buses ExecutionBus)
    [
      (1, [pc, timestamp]),
      (-1, [next_pc, next_timestamp])
    ]
  )
  (h_memory : Interaction.balanced_by_ordered
    (air.buses MemoryBus)
    [
      write_word_memoryBus_entry b rs1 rs1_prev_timestamp,
      read_word_memoryBus_entry b0 b1 b2 b3 rs1 timestamp,
      write_word_memoryBus_entry c rs2 rs2_prev_timestamp,
      read_word_memoryBus_entry c0 c1 c2 c3 rs2 (timestamp + 1),
      write_word_memoryBus_entry prev_data rd rd_prev_timestamp,
      read_word_memoryBus_entry a0 a1 a2 a3 rd (timestamp + 2)
    ]
  )
  (h_timestamp_range : timestamp.val < 2^29 - 1)
  (h_rs1_prev_timestamp_range : rs1_prev_timestamp.val < 2^29)
  (h_rs2_prev_timestamp_range : rs2_prev_timestamp.val < 2^29)
  (h_rd_prev_timestamp_range : rd_prev_timestamp.val < 2^29)
  (h_range_check : Interaction.balanced_by_ordered
    (air.buses RangeCheckerBus)
    [
      range_bus_entry range_val0 two_pow_17_correct,
      range_bus_entry range_val1 two_pow_12_correct,
      range_bus_entry range_val2 two_pow_17_correct,
      range_bus_entry range_val3 two_pow_12_correct,
      range_bus_entry range_val4 two_pow_17_correct,
      range_bus_entry range_val5 two_pow_12_correct,
    ]
  )
  (h_read_instruction : Interaction.balanced_by_ordered
    (air.buses ReadInstructionBus)
    (readInstruction_add pc rd rs1 rs2)
  )
  (h_bitwise : Interaction.balanced_by_ordered
    (air.buses BitwiseBus)
    (word_bytes_bitwiseBus_entries bitwise_word)
  )
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
