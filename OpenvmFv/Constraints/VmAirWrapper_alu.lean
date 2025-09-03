import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Extraction.VmAirWrapper_alu
import OpenvmFv.Util

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

namespace VmAirWrapper_alu.constraints

def constraint_list
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List Prop :=
  [
    VmAirWrapper_alu.extraction.constraint_0 c row,
    VmAirWrapper_alu.extraction.constraint_1 c row,
    VmAirWrapper_alu.extraction.constraint_2 c row,
    VmAirWrapper_alu.extraction.constraint_3 c row,
    VmAirWrapper_alu.extraction.constraint_4 c row,
    VmAirWrapper_alu.extraction.constraint_5 c row,
    VmAirWrapper_alu.extraction.constraint_6 c row,
    VmAirWrapper_alu.extraction.constraint_7 c row,
    VmAirWrapper_alu.extraction.constraint_8 c row,
    VmAirWrapper_alu.extraction.constraint_9 c row,
    VmAirWrapper_alu.extraction.constraint_10 c row,
    VmAirWrapper_alu.extraction.constraint_11 c row,
    VmAirWrapper_alu.extraction.constraint_12 c row,
    VmAirWrapper_alu.extraction.constraint_13 c row,
    VmAirWrapper_alu.extraction.constraint_14 c row,
    VmAirWrapper_alu.extraction.constraint_15 c row,
    VmAirWrapper_alu.extraction.constraint_16 c row,
    VmAirWrapper_alu.extraction.constraint_17 c row,
    VmAirWrapper_alu.extraction.constraint_18 c row,
    VmAirWrapper_alu.extraction.constraint_19 c row,
    VmAirWrapper_alu.extraction.constraint_20 c row,
    VmAirWrapper_alu.extraction.constraint_21 c row,
    VmAirWrapper_alu.extraction.constrain_interactions c
  ]

@[simp]
def allHold
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
  (_ : row ≤ c.last_row)
: Prop :=
  List.Forall (fun x => x) (constraint_list c row)

lemma allHold_constraints
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
  (valid_row : row ≤ c.last_row)
:
  allHold c row valid_row ↔
    (c.core.opcode_add_flag row 0 = 0 ∨ c.core.opcode_add_flag row 0 = 1) ∧
    (c.core.opcode_sub_flag row 0 = 0 ∨ c.core.opcode_sub_flag row 0 = 1) ∧
    (c.core.opcode_xor_flag row 0 = 0 ∨ c.core.opcode_xor_flag row 0 = 1) ∧
    (c.core.opcode_or_flag row 0 = 0 ∨ c.core.opcode_or_flag row 0 = 1) ∧
    (c.core.opcode_and_flag row 0 = 0 ∨ c.core.opcode_and_flag row 0 = 1) ∧
    (c.core.is_valid row 0 = 0 ∨ c.core.is_valid row 0 = 1) ∧
    (c.core.opcode_add_flag row 0 = 0 ∨ (c.core.b_0 row 0 + c.core.c_0 row 0 = c.core.a_0 row 0) ∨ c.core.carry_add_0 row 0 = 1) ∧
    (c.core.opcode_sub_flag row 0 = 0 ∨ (c.core.a_0 row 0 + c.core.c_0 row 0 = c.core.b_0 row 0) ∨ c.core.carry_sub_0 row 0 = 1) ∧
    (c.core.opcode_add_flag row 0 = 0 ∨ (c.core.b_1 row 0 + c.core.c_1 row 0 - c.core.a_1 row 0 + c.core.carry_add_0 row 0 = 0) ∨ c.core.carry_add_1 row 0 = 1) ∧
    (c.core.opcode_sub_flag row 0 = 0 ∨ (c.core.a_1 row 0 + c.core.c_1 row 0 - c.core.b_1 row 0 + c.core.carry_sub_0 row 0 = 0) ∨ c.core.carry_sub_1 row 0 = 1) ∧
    (c.core.opcode_add_flag row 0 = 0 ∨ (c.core.b_2 row 0 + c.core.c_2 row 0 - c.core.a_2 row 0 + c.core.carry_add_1 row 0 = 0) ∨ c.core.carry_add_2 row 0 = 1) ∧
    (c.core.opcode_sub_flag row 0 = 0 ∨ (c.core.a_2 row 0 + c.core.c_2 row 0 - c.core.b_2 row 0 + c.core.carry_sub_1 row 0 = 0) ∨ c.core.carry_sub_2 row 0 = 1) ∧
    (c.core.opcode_add_flag row 0 = 0 ∨ (c.core.b_3 row 0 + c.core.c_3 row 0 - c.core.a_3 row 0 + c.core.carry_add_2 row 0 = 0) ∨ c.core.carry_add_3 row 0 = 1) ∧
    (c.core.opcode_sub_flag row 0 = 0 ∨ (c.core.a_3 row 0 + c.core.c_3 row 0 - c.core.b_3 row 0 + c.core.carry_sub_2 row 0 = 0) ∨ c.core.carry_sub_3 row 0 = 1) ∧
    (c.adapter.rs2_as row 0 = 0 ∨ c.adapter.rs2_as row 0 = 1) ∧
    (c.adapter.rs2_as row 0 = 1 ∨ c.adapter.rs2 row 0 = c.rs2_imm row 0) ∧
    (c.adapter.rs2_as row 0 = 1 ∨ c.rs2_sign row 0 = c.rs2_limbs row 0 3) ∧
    (c.adapter.rs2_as row 0 = 1 ∨ c.core.c_2 row 0 = 0 ∨ c.core.c_2 row 0 = 255) ∧
    (c.core.is_valid row 0 = 0 ∨ c.adapter.from_state.timestamp row 0 - c.adapter.reads_aux_0.base.prev_timestamp row 0 - 1 = c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0 + c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072) ∧
    (c.adapter.rs2_as row 0 = 0 ∨ c.core.is_valid row 0 = 1) ∧ (c.adapter.rs2_as row 0 = 0 ∨ c.adapter.from_state.timestamp row 0 + 1 - c.adapter.reads_aux_1.base.prev_timestamp row 0 - 1 = c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0 + c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072) ∧
    (c.core.is_valid row 0 = 0 ∨ c.adapter.from_state.timestamp row 0 + 2 - c.adapter.writes_aux.base.prev_timestamp row 0 - 1 = c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 + c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072) ∧
    VmAirWrapper_alu.extraction.constrain_interactions c
:= by
  simp [constraint_list]
  simp [openvm_encapsulation]
  repeat rw [eq_comm (a := (1 : FBB))]
  repeat rw [eq_comm (a := (255 : FBB))]
  grind

lemma constrain_interactions' [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (h : VmAirWrapper_alu.extraction.constrain_interactions c)
: c.buses = fun index ↦
  if index = ExecutionBus then
    List.map (fun row ↦ (-c.core.is_valid row 0, [c.adapter.from_state.pc row 0, c.adapter.from_state.timestamp row 0]))
        (List.range (c.last_row + 1)) ++
      List.map
        (fun row ↦
          (c.core.is_valid row 0, [c.adapter.from_state.pc row 0 + 4, c.adapter.from_state.timestamp row 0 + 3]))
        (List.range (c.last_row + 1))
  else
    if index = MemoryBus then
      List.map
          (fun row ↦
            (2013265920 * c.core.is_valid row 0,
              [1, c.adapter.rs1_ptr row 0, c.core.b_0 row 0, c.core.b_1 row 0, c.core.b_2 row 0, c.core.b_3 row 0,
                c.adapter.reads_aux_0.base.prev_timestamp row 0]))
          (List.range (c.last_row + 1)) ++
        (List.map
            (fun row ↦
              (c.core.is_valid row 0,
                [1, c.adapter.rs1_ptr row 0, c.core.b_0 row 0, c.core.b_1 row 0, c.core.b_2 row 0, c.core.b_3 row 0,
                  c.adapter.from_state.timestamp row 0]))
            (List.range (c.last_row + 1)) ++
          (List.map
              (fun row ↦
                (2013265920 * c.adapter.rs2_as row 0,
                  [c.adapter.rs2_as row 0, c.adapter.rs2 row 0, c.core.c_0 row 0, c.core.c_1 row 0, c.core.c_2 row 0,
                    c.core.c_3 row 0, c.adapter.reads_aux_1.base.prev_timestamp row 0]))
              (List.range (c.last_row + 1)) ++
            (List.map
                (fun row ↦
                  (c.adapter.rs2_as row 0,
                    [c.adapter.rs2_as row 0, c.adapter.rs2 row 0, c.core.c_0 row 0, c.core.c_1 row 0, c.core.c_2 row 0,
                      c.core.c_3 row 0, c.adapter.from_state.timestamp row 0 + 1]))
                (List.range (c.last_row + 1)) ++
              (List.map
                  (fun row ↦
                    (2013265920 * c.core.is_valid row 0,
                      [1, c.adapter.rd_ptr row 0, c.adapter.writes_aux.prev_data_0 row 0,
                        c.adapter.writes_aux.prev_data_1 row 0, c.adapter.writes_aux.prev_data_2 row 0,
                        c.adapter.writes_aux.prev_data_3 row 0, c.adapter.writes_aux.base.prev_timestamp row 0]))
                  (List.range (c.last_row + 1)) ++
                List.map
                  (fun row ↦
                    (c.core.is_valid row 0,
                      [1, c.adapter.rd_ptr row 0, c.core.a_0 row 0, c.core.a_1 row 0, c.core.a_2 row 0,
                        c.core.a_3 row 0, c.adapter.from_state.timestamp row 0 + 2]))
                  (List.range (c.last_row + 1))))))
    else
      if index = RangeCheckerBus then
        List.map
            (fun row ↦ (c.core.is_valid row 0, [c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]))
            (List.range (c.last_row + 1)) ++
          (List.map
              (fun row ↦
                (c.core.is_valid row 0, [c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]))
              (List.range (c.last_row + 1)) ++
            (List.map
                (fun row ↦
                  (c.adapter.rs2_as row 0, [c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]))
                (List.range (c.last_row + 1)) ++
              (List.map
                  (fun row ↦
                    (c.adapter.rs2_as row 0, [c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]))
                  (List.range (c.last_row + 1)) ++
                (List.map
                    (fun row ↦
                      (c.core.is_valid row 0, [c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]))
                    (List.range (c.last_row + 1)) ++
                  List.map
                    (fun row ↦
                      (c.core.is_valid row 0, [c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]))
                    (List.range (c.last_row + 1))))))
      else
        if index = ReadInstructionBus then
          List.map
            (fun row ↦
              (c.core.is_valid row 0,
                [c.adapter.from_state.pc row 0, (c.core.ctx row 0).instruction.opcode, c.adapter.rd_ptr row 0,
                  c.adapter.rs1_ptr row 0, c.adapter.rs2 row 0, 1, c.adapter.rs2_as row 0, 0, 0]))
            (List.range (c.last_row + 1))
        else
          if index = BitwiseBus then
            List.map
                (fun row ↦ (c.core.is_valid row 0, [c.core.x_0 row 0, c.core.y_0 row 0, c.core.x_xor_y_0 row 0, 1]))
                (List.range (c.last_row + 1)) ++
              (List.map
                  (fun row ↦ (c.core.is_valid row 0, [c.core.x_1 row 0, c.core.y_1 row 0, c.core.x_xor_y_1 row 0, 1]))
                  (List.range (c.last_row + 1)) ++
                (List.map
                    (fun row ↦ (c.core.is_valid row 0, [c.core.x_2 row 0, c.core.y_2 row 0, c.core.x_xor_y_2 row 0, 1]))
                    (List.range (c.last_row + 1)) ++
                  (List.map
                      (fun row ↦
                        (c.core.is_valid row 0, [c.core.x_3 row 0, c.core.y_3 row 0, c.core.x_xor_y_3 row 0, 1]))
                      (List.range (c.last_row + 1)) ++
                    List.map
                      (fun row ↦
                        (c.core.is_valid row 0 - c.adapter.rs2_as row 0, [c.core.c_0 row 0, c.core.c_1 row 0, 0, 0]))
                      (List.range (c.last_row + 1)))))
          else [] := by
    simp_all [openvm_encapsulation]

namespace Interaction

lemma get_multiplicity_cons
  {x : F × List F}
  {data : List F}
  [Field F]
  [BEq (List F)]
:
  Interaction.get_multiplicity (x :: xs) data =
  (if x.2 == data then x.1 else 0) + Interaction.get_multiplicity xs data
:= by
  unfold Interaction.get_multiplicity
  grind

lemma balanced_by_matching_heads
  {x y : (FBB × List FBB)}
  {xs ys : List (FBB × List FBB)}
  (h : Interaction.balanced_by (x :: xs) (y :: ys))
  (h_head_multiplicity : x.1 + y.1 = 0)
  (h_head_data : x.2 = y.2)
:
  Interaction.balanced_by xs ys
:= by
  unfold Interaction.balanced_by at h ⊢
  simp [get_multiplicity_cons] at h
  grind

end Interaction

section range_bus

def rangeBus_balance_entry
  (mul : FBB) (deg : Fin 30) (val : Fin (2 ^ deg.val))
: (FBB × List FBB) :=
  (mul, [ @Fin.mk BB_prime val.val
          (by trans 2 ^ deg.val <;> [ omega; skip ];
              apply lt_of_le_of_lt (b := 2 ^ 30) <;>
              [ apply pow_le_pow; simp ] <;> simp),
          ⟨ deg.val, by omega ⟩ ])

def rangeBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (ac.is_valid row 0, [aa.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (ac.is_valid row 0, [aa.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
    (aa.rs2_as row 0, [aa.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (aa.rs2_as row 0, [aa.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
    (ac.is_valid row 0, [aa.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (ac.is_valid row 0, [aa.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
  ]

lemma rangeBus_balanced_row [Field ExtF]
  {air : Valid_VmAirWrapper_alu FBB ExtF}
  {row : ℕ}
  (valid_row : row ≤ air.last_row)
  (b_is_valid : air.core.is_valid row 0 = 0 ∨ air.core.is_valid row 0 = 1)
  (b_rs2_as : air.adapter.rs2_as row 0 = 0 ∨ air.adapter.rs2_as row 0 = 1)
:
  let aa := air.adapter
  let ac := air.core
  let f := fun (x : ℕ → ℕ → FBB) => x row 0
  Interaction.balanced_by
    (rangeBus_row air row)
    [
      rangeBus_balance_entry (2013265920 * (f ac.is_valid)) 17 r0l0,
      rangeBus_balance_entry (2013265920 * (f ac.is_valid)) 12 r0l1,
      rangeBus_balance_entry (2013265920 * (f aa.rs2_as)) 17 r1l0,
      rangeBus_balance_entry (2013265920 * (f aa.rs2_as)) 12 r1l1,
      rangeBus_balance_entry (2013265920 * (f ac.is_valid)) 17 bl0,
      rangeBus_balance_entry (2013265920 * (f ac.is_valid)) 12 bl1
    ]
  → (f ac.is_valid = 1 → (aa.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0).val < 2 ^ 17) ∧
    (f ac.is_valid = 1 → (aa.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0).val < 2 ^ 12) ∧
    (f aa.rs2_as = 1 → (aa.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0).val < 2 ^ 17) ∧
    (f aa.rs2_as = 1 → (aa.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0).val < 2 ^ 12) ∧
    (f ac.is_valid = 1 → (aa.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0).val < 2 ^ 17) ∧
    (f ac.is_valid = 1 → (aa.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0).val < 2 ^ 12)
:= by
  simp [Interaction.balanced_by, rangeBus_row, rangeBus_balance_entry]
  intro balance
  split_ands <;> intro heq <;> simp_all
  . replace balance := balance [air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]
    simp [Interaction.get_multiplicity_cons, Interaction.get_multiplicity_empty] at balance
    split_ifs at balance <;> grind
  . replace balance := balance [air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]
    simp [Interaction.get_multiplicity_cons, Interaction.get_multiplicity_empty] at balance
    split_ifs at balance <;> grind
  . replace balance := balance [air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]
    simp [Interaction.get_multiplicity_cons, Interaction.get_multiplicity_empty] at balance
    split_ifs at balance <;> grind
  . replace balance := balance [air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]
    simp [Interaction.get_multiplicity_cons, Interaction.get_multiplicity_empty] at balance
    split_ifs at balance <;> grind
  . replace balance := balance [air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]
    simp [Interaction.get_multiplicity_cons, Interaction.get_multiplicity_empty] at balance
    split_ifs at balance <;> grind
  . replace balance := balance [air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]
    simp [Interaction.get_multiplicity_cons, Interaction.get_multiplicity_empty] at balance
    split_ifs at balance <;> grind

end range_bus

section memory_bus

def memoryBus_rd_entry
  (mul as ptr x1 x2 x3 x4 timestamp : FBB)
: (FBB × List FBB) :=
  (mul, [as, ptr, x1, x2, x3, x4, timestamp])

def memoryBus_wr_entry
  (mul as ptr : FBB) (val : U32) (timestamp : FBB)
: (FBB × List FBB) :=
  (mul, [as, ptr, val[0], val[1], val[2], val[3], timestamp])

def memoryBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (2013265920 * ac.is_valid row 0, [1, aa.rs1_ptr row 0, ac.b_0 row 0, ac.b_1 row 0, ac.b_2 row 0, ac.b_3 row 0, aa.reads_aux_0.base.prev_timestamp row 0]),
    (2013265920 * aa.rs2_as row 0, [aa.rs2_as row 0, aa.rs2 row 0, ac.c_0 row 0, ac.c_1 row 0, ac.c_2 row 0, ac.c_3 row 0, aa.reads_aux_1.base.prev_timestamp row 0]),
    (2013265920 * ac.is_valid row 0, [1, aa.rd_ptr row 0, aa.writes_aux.prev_data_0 row 0, aa.writes_aux.prev_data_1 row 0, aa.writes_aux.prev_data_2 row 0, aa.writes_aux.prev_data_3 row 0, aa.writes_aux.base.prev_timestamp row 0]),
    (ac.is_valid row 0, [1, aa.rs1_ptr row 0, ac.b_0 row 0, ac.b_1 row 0, ac.b_2 row 0, ac.b_3 row 0, aa.from_state.timestamp row 0]),
    (aa.rs2_as row 0, [aa.rs2_as row 0, aa.rs2 row 0, ac.c_0 row 0, ac.c_1 row 0, ac.c_2 row 0, ac.c_3 row 0, aa.from_state.timestamp row 0 + 1]),
    (ac.is_valid row 0, [1, aa.rd_ptr row 0, ac.a_0 row 0, ac.a_1 row 0, ac.a_2 row 0, ac.a_3 row 0, aa.from_state.timestamp row 0 + 2])
  ]

-- lemma memoryBus_balanced_row [Field ExtF]
--   {air : Valid_VmAirWrapper_alu FBB ExtF}
--   {row : ℕ}
--   (valid_row : row ≤ air.last_row)
--   (cstrs : allHold air row valid_row)
--   (is_valid :  air.core.is_valid row 0 = 1)
--   (a b c : U32)
--   (P : Prop)
-- :
--   let aa := air.adapter
--   let ac := air.core
--   let f := fun (x : ℕ → ℕ → FBB) => x row 0
--   Interaction.balanced_by
--     (memoryBus_row air row)
--     [
--       memoryBus_wr_entry (f ac.is_valid) 1 (f aa.rs1_ptr) b (f aa.reads_aux_0.base.prev_timestamp),
--       memoryBus_rd_entry (2013265920 * f ac.is_valid) 1 (f aa.rs1_ptr) (f ac.b_0) (f ac.b_1) (f ac.b_2) (f ac.b_3) (f aa.from_state.timestamp),
--       -- write_word_memoryBus_entry c rs2 rs2_prev_timestamp,
--       -- memoryBus_read_entry c0 c1 c2 c3 rs2 (timestamp + 1),
--       -- write_word_memoryBus_entry prev_data rd rd_prev_timestamp,
--       -- memoryBus_read_entry a0 a1 a2 a3 rd (timestamp + 2)
--     ]
--   → f ac.b_0 = b[0] ∧ f ac.b_1 = b[1] ∧ f ac.b_1 = b[2] ∧ f ac.b_3 = b[3]
-- := by
--   simp [Interaction.balanced_by, memoryBus_row, memoryBus_rd_entry, memoryBus_wr_entry]
--   intro balance
--   rw [allHold_constraints] at cstrs
--   obtain ⟨ h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, rest ⟩ := cstrs
--   clear rest
--   simp_all

--   have b1 := balance [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0, air.adapter.reads_aux_0.base.prev_timestamp row 0]
--   simp [Interaction.get_multiplicity_cons, Interaction.get_multiplicity_empty] at b1
--   sorry









end memory_bus

end VmAirWrapper_alu.constraints
