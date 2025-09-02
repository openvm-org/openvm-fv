import Mathlib

import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Constraints.VmAirWrapper_alu
import OpenvmFv.Fundamentals.Execution

import LeanZKCircuit.Interactions

-- axiom constraints_MemoryBus
--   [Field ExtF]
--   (c : Valid_VmAirWrapper_alu_BB ExtF) :
--   ∀ x ∈ c.buses MemoryBus,
--     x.1 = 1 →
--       x.2[2]!.val < 256 ∧
--       x.2[3]!.val < 256 ∧
--       x.2[4]!.val < 256 ∧
--       x.2[5]!.val < 256

def read_word_memoryBus_entry
  (x1 x2 x3 x4 ptr: BabyBear.F) (timestamp: BabyBear.F)
: (BabyBear.F × List BabyBear.F) :=
  (
    -1,
    [
      1,
      ptr,
      x1,x2,x3,x4,
      timestamp
    ]
  )

def write_word_memoryBus_entry
  (val : U32) (ptr: BabyBear.F) (timestamp: BabyBear.F)
: (BabyBear.F × List BabyBear.F) :=
  (
    1,
    [
      1,
      ptr,
      val[0].toFin,
      val[1].toFin,
      val[2].toFin,
      val[3].toFin,
      timestamp
    ]
  )

def babyBear_to_word
  (x1 x2 x3 x4 : BabyBear.F)
: U32 :=
  #v[
    BitVec.ofNat 8 x1.toNat,
    BitVec.ofNat 8 x2.toNat,
    BitVec.ofNat 8 x3.toNat,
    BitVec.ofNat 8 x4.toNat,
  ]

def word_bytes_bitwiseBus_entries
  (val : U32)
: List (BabyBear.F × List BabyBear.F) :=
  [
    (-1, [↑(val[0].toNat % 256), ↑(val[0].toNat % 256), 0, 1]),
    (-1, [↑(val[1].toNat % 256), ↑(val[1].toNat % 256), 0, 1]),
    (-1, [↑(val[2].toNat % 256), ↑(val[2].toNat % 256), 0, 1]),
    (-1, [↑(val[3].toNat % 256), ↑(val[3].toNat % 256), 0, 1]),
  ]

def readInstruction_add
  (pc rd rs1 rs2 : BabyBear.F)
: List (BabyBear.F × List BabyBear.F) :=
  [(-1, [pc, 512, rd, rs1, rs2, 1, 1, 0, 0])]

lemma flag1_exclusive_of_is_valid_binary
  {flag2 flag3 flag4 flag5 : BabyBear.F}
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

lemma balanced_by_matching_heads
  {x y: (BabyBear.F × List BabyBear.F)}
  {xs ys : List (BabyBear.F × List BabyBear.F)}
  (h: Interaction.balanced_by (x::xs) (y::ys))
  (h_head_multiplicity : x.1 + y.1 = 0)
  (h_head_data : x.2 = y.2)
:
  Interaction.balanced_by
    xs
    ys
:= by
  unfold Interaction.balanced_by at h ⊢
  intro data
  simp [get_multiplicity_cons, h_head_data] at h
  grind

lemma eq_of_readInstruction_add_balanced
  (h: Interaction.balanced_by
    [(1,
      [
        x1,
        x2,
        x3,
        x4,
        x5,
        1,
        x6,
        0,
        0
      ]
    )]
    (readInstruction_add y1 y2 y3 y4)
  )
:
  x1 = y1 ∧
  x2 = 512 ∧
  x3 = y2 ∧
  x4 = y3 ∧
  x5 = y4 ∧
  x6 = 1
:= by
  unfold readInstruction_add Interaction.balanced_by at h
  specialize h [y1, 512, y2, y3, y4, 1, 1, 0, 0]
  unfold Interaction.get_multiplicity at h
  by_cases h: [
    x1,
    x2,
    x3,
    x4,
    x5,
    1,
    x6,
    0,
    0
  ] = [y1, 512, y2, y3, y4, 1, 1, 0, 0]
  . apply List.ext_get_iff.mp at h
    simp at h
    split_ands
    . exact h 0 (by trivial) (by trivial)
    . exact h 1 (by trivial) (by trivial)
    . exact h 2 (by trivial) (by trivial)
    . exact h 3 (by trivial) (by trivial)
    . exact h 4 (by trivial) (by trivial)
    . exact h 6 (by trivial) (by trivial)
  . simp at h
    grind

lemma byte_mod_256 (a : BitVec 8)
:
  @Nat.cast BabyBear.F _ (a.toNat % 256) =
  ↑(a.toNat)
:= by
  rw [Nat.mod_eq_of_lt]
  exact BitVec.toNat_lt_twoPow_of_le (by trivial)

-- spec for non-intermediate version
-- TODO
-- - split a up into 4
theorem spec_add
  [Field ExtF]
  (air : Valid_VmAirWrapper_alu BabyBear.F ExtF)
  (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3: BabyBear.F)
  (h_last_row : air.last_row = 0)
  (h_constraints : VmAirWrapper_alu.constraints.allHold air 0)
  (h_interactions: VmAirWrapper_alu.extraction.constrain_interactions air)
  (h_is_add : air.core.opcode_add_flag 0 0 = 1)
  (h_memory : Interaction.balanced_by
    (air.buses MemoryBus)
    [
      -- note that this is what it takes to balance the bus,
      -- so it is asserting that a read exists for each write and vice versa
      write_word_memoryBus_entry b rs1 rs1_prev_timestamp,
      read_word_memoryBus_entry b0 b1 b2 b3 rs1 timestamp,
      write_word_memoryBus_entry c rs2 rs2_prev_timestamp,
      read_word_memoryBus_entry c0 c1 c2 c3 rs2 (timestamp + 1),
      write_word_memoryBus_entry prev_data rd rd_prev_timestamp,
      read_word_memoryBus_entry a0 a1 a2 a3 rd (timestamp + 2)
    ]
  )
  (h_bitwise : Interaction.balanced_by
    (air.buses BitwiseBus)
    (word_bytes_bitwiseBus_entries a)
  )
  (h_read_instruction : Interaction.balanced_by
    (air.buses ReadInstructionBus)
    (readInstruction_add pc rd rs1 rs2 )
  )
:
  U32.toBV a = execute_RTYPE_pure_U32 b c .ADD ∧
  a = babyBear_to_word a0 a1 a2 a3 ∧
  b = babyBear_to_word b0 b1 b2 b3 ∧
  c = babyBear_to_word c0 c1 c2 c3
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
      h_21
  ⟩ := (VmAirWrapper_alu.constraints.allHold_constraints air 0).mp h_constraints
  clear h_constraints
  replace h_interactions := VmAirWrapper_alu.constraints.constrain_interactions' air h_interactions
  simp [h_interactions] at *
  clear h_interactions
  simp [*] at *
  have h_is_valid_1 : air.core.is_valid 0 0 = 1 := by
    unfold Valid_BaseAluCoreAir.is_valid at h_5 ⊢
    simp [h_is_add] at h_5
    have := flag1_exclusive_of_is_valid_binary h_1 h_2 h_3 h_4 h_5
    grind
  simp [h_is_valid_1] at *
  have :
    air.adapter.from_state.pc 0 0 = pc ∧
    (air.core.ctx 0 0).instruction.opcode = 512 ∧
    air.adapter.rd_ptr 0 0 = rd ∧
    air.adapter.rs1_ptr 0 0 = rs1 ∧
    air.adapter.rs2 0 0 = rs2 ∧
    air.adapter.rs2_as 0 0 = 1
  := eq_of_readInstruction_add_balanced h_read_instruction
  clear h_read_instruction
  obtain ⟨h_pc, h_opcode, h_rd, h_rs1, h_rs2, h_rs2_as⟩ := this
  simp [*] at *
  simp [write_word_memoryBus_entry.eq_def, read_word_memoryBus_entry.eq_def] at h_memory
  unfold word_bytes_bitwiseBus_entries at h_bitwise
  simp [byte_mod_256] at h_bitwise
  -- by_cases h_memory_matches :
  --   air.core.b_0 0 0 = ↑b[0].toNat ∧
  --   air.core.b_1 0 0 = ↑b[1].toNat ∧
  --   air.core.b_2 0 0 = ↑b[2].toNat ∧
  --   air.core.b_3 0 0 = ↑b[3].toNat ∧
  --   air.adapter.reads_aux_0.base.prev_timestamp 0 0 = rs1_prev_timestamp ∧
  --   air.adapter.from_state.timestamp 0 0 = timestamp ∧
  --   air.core.c_0 0 0 = ↑(c)[0].toNat ∧
  --   air.core.c_1 0 0 = ↑(c)[1].toNat ∧
  --   air.core.c_2 0 0 = ↑(c)[2].toNat ∧
  --   air.core.c_3 0 0 = ↑(c)[3].toNat ∧
  --   air.adapter.reads_aux_1.base.prev_timestamp 0 0 = rs2_prev_timestamp ∧
  --   air.adapter.writes_aux.prev_data_0 0 0 = ↑prev_data[0].toNat ∧
  --   air.adapter.writes_aux.prev_data_1 0 0 = ↑prev_data[1].toNat ∧
  --   air.adapter.writes_aux.prev_data_2 0 0 = ↑prev_data[2].toNat ∧
  --   air.adapter.writes_aux.prev_data_3 0 0 = ↑prev_data[3].toNat ∧
  --   air.adapter.writes_aux.base.prev_timestamp 0 0 = rd_prev_timestamp ∧
  --   air.core.a_0 0 0 = ↑a[0].toNat ∧
  --   air.core.a_1 0 0 = ↑a[1].toNat ∧
  --   air.core.a_2 0 0 = ↑a[2].toNat ∧
  --   air.core.a_3 0 0 = ↑a[3].toNat



  -- simp_all

  -- unfold BitwiseBus ExecutionBus MemoryBus RangeCheckerBus ReadInstructionBus at h_bitwise
  -- simp at h_bitwise

  -- have : c.core.is_valid 0 0 = 1 := by sorry
  -- simp [this] at h_bitwise
  -- unfold Valid_BaseAluCoreAir.x_0 at h_bitwise

  done
