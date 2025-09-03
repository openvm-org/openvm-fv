import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Extraction.VmAirWrapper_alu
import OpenvmFv.Fundamentals.Interaction
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

lemma single_op
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
  (valid_row : row ≤ c.last_row)
  (cstrs : allHold c row valid_row)
:
  let is_add := c.core.opcode_add_flag row 0
  let is_sub := c.core.opcode_sub_flag row 0
  let is_xor := c.core.opcode_xor_flag row 0
  let is_or := c.core.opcode_or_flag row 0
  let is_and := c.core.opcode_and_flag row 0
  (is_add = 1 → is_sub = 0 ∧ is_xor = 0 ∧ is_or = 0 ∧ is_and = 0) ∧
  (is_sub = 1 → is_add = 0 ∧ is_xor = 0 ∧ is_or = 0 ∧ is_and = 0) ∧
  (is_xor = 1 → is_add = 0 ∧ is_sub = 0 ∧ is_or = 0 ∧ is_and = 0) ∧
  (is_or = 1 → is_add = 0 ∧ is_sub = 0 ∧ is_xor = 0 ∧ is_and = 0) ∧
  (is_and = 1 → is_add = 0 ∧ is_sub = 0 ∧ is_xor = 0 ∧ is_or = 0)
:= by
  rw [allHold_constraints c row valid_row] at cstrs
  obtain ⟨ h0, h1, h2, h3, h4, h5, rest ⟩ := cstrs
  rw [Valid_BaseAluCoreAir.is_valid] at h5
  clear rest
  grind (splits := 23)

end VmAirWrapper_alu.constraints

namespace VmAirWrapper_alu.buses

lemma buses_eq [Field ExtF]
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

section ExecutionBus

def executionBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (-ac.is_valid row 0, [aa.from_state.pc row 0, aa.from_state.timestamp row 0]),
    (ac.is_valid row 0, [aa.from_state.pc row 0 + 4, aa.from_state.timestamp row 0 + 3])
  ]

lemma executionBus_balanced_row [Field ExtF]
  {air : Valid_VmAirWrapper_alu FBB ExtF}
  {row : ℕ}
:
  let aa := air.adapter
  let ac := air.core
  let f := fun (x : ℕ → ℕ → FBB) => x row 0
  InteractionList.balanced_by_ordered
    (executionBus_row air row)
    [
      Interaction.executionBus_entry mul0 pc0 t0,
      Interaction.executionBus_entry mul1 pc1 t1,
    ]
  → (f ac.is_valid = 1 → f aa.from_state.pc = pc0 ∧ (f aa.from_state.timestamp).val = t0.val ∧ (f aa.from_state.timestamp).val < 1073741824) ∧
    (f ac.is_valid = 1 → f aa.from_state.pc + 4 = pc1 ∧ (f aa.from_state.timestamp + 3).val = t1.val ∧ (f aa.from_state.timestamp + 3).val < 1073741824)
:= by
  simp [executionBus_row, InteractionList.balanced_by_ordered]
  intro b0 b1
  apply Interaction.executionBus_balances_facts at b0
  apply Interaction.executionBus_balances_facts at b1
  grind

end ExecutionBus

section MemoryBus

def memoryBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (2013265920 * ac.is_valid row 0, [1, aa.rs1_ptr row 0, ac.b_0 row 0, ac.b_1 row 0, ac.b_2 row 0, ac.b_3 row 0, aa.reads_aux_0.base.prev_timestamp row 0]),
    (ac.is_valid row 0, [1, aa.rs1_ptr row 0, ac.b_0 row 0, ac.b_1 row 0, ac.b_2 row 0, ac.b_3 row 0, aa.from_state.timestamp row 0]),
    (2013265920 * aa.rs2_as row 0, [aa.rs2_as row 0, aa.rs2 row 0, ac.c_0 row 0, ac.c_1 row 0, ac.c_2 row 0, ac.c_3 row 0, aa.reads_aux_1.base.prev_timestamp row 0]),
    (aa.rs2_as row 0, [aa.rs2_as row 0, aa.rs2 row 0, ac.c_0 row 0, ac.c_1 row 0, ac.c_2 row 0, ac.c_3 row 0, aa.from_state.timestamp row 0 + 1]),
    (2013265920 * ac.is_valid row 0, [1, aa.rd_ptr row 0, aa.writes_aux.prev_data_0 row 0, aa.writes_aux.prev_data_1 row 0, aa.writes_aux.prev_data_2 row 0, aa.writes_aux.prev_data_3 row 0, aa.writes_aux.base.prev_timestamp row 0]),
    (ac.is_valid row 0, [1, aa.rd_ptr row 0, ac.a_0 row 0, ac.a_1 row 0, ac.a_2 row 0, ac.a_3 row 0, aa.from_state.timestamp row 0 + 2])
  ]

lemma memoryBus_balanced_row [Field ExtF]
  {air : Valid_VmAirWrapper_alu FBB ExtF}
  {row : ℕ}
:
  let aa := air.adapter
  let ac := air.core
  let f := fun (x : ℕ → ℕ → FBB) => x row 0
  let aw := aa.writes_aux
  InteractionList.balanced_by_ordered
    (memoryBus_row air row)
    [
      Interaction.memoryBus_write_entry mul0 as0 r0 b t0,
      Interaction.memoryBus_read_entry mul1 as1 r1 b0 b1 b2 b3 t1,
      Interaction.memoryBus_write_entry mul2 as2 r2 c t2,
      Interaction.memoryBus_read_entry mul3 as3 r3 c0 c1 c2 c3 t3,
      Interaction.memoryBus_write_entry mul4 as4 r3 d t4,
      Interaction.memoryBus_read_entry mul5 as5 r5 a0 a1 a2 a3 t5
    ]
  → (f ac.is_valid = 1 → (f ac.b_0).val < 256 ∧ (f ac.b_1).val < 256 ∧ (f ac.b_2).val < 256 ∧ (f ac.b_3).val < 256 ∧ b = #v[↑(f ac.b_0).val, ↑(f ac.b_1).val, ↑(f ac.b_2).val, ↑(f ac.b_3).val] ∧ (f aa.reads_aux_0.base.prev_timestamp).val = t0.val ∧ (f aa.reads_aux_0.base.prev_timestamp).val < 1073741824) ∧
    (f aa.rs2_as = 1 → (f ac.c_0).val < 256 ∧ (f ac.c_1).val < 256 ∧ (f ac.c_2).val < 256 ∧ (f ac.c_3).val < 256 ∧ c = #v[↑(f ac.c_0).val, ↑(f ac.c_1).val, ↑(f ac.c_2).val, ↑(f ac.c_3).val] ∧ (f aa.reads_aux_1.base.prev_timestamp).val = t2.val ∧ (f aa.reads_aux_1.base.prev_timestamp) < 1073741824) ∧
    (f ac.is_valid = 1 → (f aw.prev_data_0).val < 256 ∧ (f aw.prev_data_1).val < 256 ∧ (f aw.prev_data_2).val < 256 ∧ (f aw.prev_data_3).val < 256 ∧ d = #v[↑(f aw.prev_data_0).val, ↑(f aw.prev_data_1).val, ↑(f aw.prev_data_2).val, ↑(f aw.prev_data_3).val]∧ (f aw.base.prev_timestamp).val = t4.val ∧ (f aw.base.prev_timestamp).val < 1073741824)
:= by
  have := U32.destruct b; have := U32.destruct c; have := U32.destruct d
  simp [memoryBus_row, InteractionList.balanced_by_ordered]
  intro b0 b1 b2 b3 b4 b5
  apply Interaction.memoryBus_write_balances_facts at b0
  apply Interaction.memoryBus_write_balances_facts at b2
  apply Interaction.memoryBus_write_balances_facts at b4
  rw [@eq_comm (a := (1 : FBB))] at *
  split_ands <;> intro heq <;> simp_all <;> omega

end MemoryBus

section RangeBus

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
:
  let aa := air.adapter
  let ac := air.core
  let f := fun (x : ℕ → ℕ → FBB) => x row 0
  InteractionList.balanced_by_ordered
    (rangeBus_row air row)
    [
      Interaction.rangeBus_entry mul0 17 r0l0,
      Interaction.rangeBus_entry mul1 12 r0l1,
      Interaction.rangeBus_entry mul2 17 r1l0,
      Interaction.rangeBus_entry mul3 12 r1l1,
      Interaction.rangeBus_entry mul4 17 bl0,
      Interaction.rangeBus_entry mul5 12 bl1
    ]
  → (f ac.is_valid = 1 → (aa.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0).val < 2 ^ 17) ∧
    (f ac.is_valid = 1 → (aa.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0).val < 2 ^ 12) ∧
    (f aa.rs2_as = 1 → (aa.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0).val < 2 ^ 17) ∧
    (f aa.rs2_as = 1 → (aa.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0).val < 2 ^ 12) ∧
    (f ac.is_valid = 1 → (aa.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0).val < 2 ^ 17) ∧
    (f ac.is_valid = 1 → (aa.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0).val < 2 ^ 12)
:= by
  simp [rangeBus_row, InteractionList.balanced_by_ordered]
  intro b0 b1 b2 b3 b4 b5
  apply Interaction.rangeBus_balances_facts at b0
  apply Interaction.rangeBus_balances_facts at b1
  apply Interaction.rangeBus_balances_facts at b2
  apply Interaction.rangeBus_balances_facts at b3
  apply Interaction.rangeBus_balances_facts at b4
  apply Interaction.rangeBus_balances_facts at b5
  simp_all

end RangeBus

section ReadInstructionBus

def readInstructionBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (ac.is_valid row 0, [aa.from_state.pc row 0,
                         (ac.ctx row 0).instruction.opcode,
                         aa.rd_ptr row 0,
                         aa.rs1_ptr row 0,
                         aa.rs2 row 0, 1,
                         aa.rs2_as row 0,
                         0,
                         0])
  ]

lemma readInstructionBus_balanced_row [Field ExtF]
  {air : Valid_VmAirWrapper_alu FBB ExtF}
  {row : ℕ}
:
  let aa := air.adapter
  let ac := air.core
  let f := fun (x : ℕ → ℕ → FBB) => x row 0
  InteractionList.balanced_by_ordered
    (readInstructionBus_row air row)
    [
      Interaction.readInstructionBus_entry mul pc opcode rd rs1 rs2 unknown0 rs2_as unknown1 unknown2,
    ]
  → (f ac.is_valid = 1 → f aa.from_state.pc = pc ∧
                         (ac.ctx row 0).instruction.opcode = opcode ∧
                         f aa.rd_ptr = rd ∧
                         f aa.rs1_ptr = rs1 ∧
                         f aa.rs2 = rs2 ∧
                         unknown0 = 1 ∧
                         f aa.rs2_as = rs2_as ∧
                         unknown1 = 0 ∧
                         unknown2 = 0)
:= by
  simp [readInstructionBus_row, InteractionList.balanced_by_ordered]
  intro b0
  apply Interaction.readInstructionBus_balances_facts at b0
  grind

end ReadInstructionBus

section BitwiseBus

def bitwiseBus_row [Field ExtF]
  (air : Valid_VmAirWrapper_alu FBB ExtF)
  (row : ℕ)
: List (FBB × List FBB) :=
  let aa := air.adapter
  let ac := air.core
  [
    (ac.is_valid row 0, [ac.x_0 row 0, ac.y_0 row 0, ac.x_xor_y_0 row 0, 1]),
    (ac.is_valid row 0, [ac.x_1 row 0, ac.y_1 row 0, ac.x_xor_y_1 row 0, 1]),
    (ac.is_valid row 0, [ac.x_2 row 0, ac.y_2 row 0, ac.x_xor_y_2 row 0, 1]),
    (ac.is_valid row 0, [ac.x_3 row 0, ac.y_3 row 0, ac.x_xor_y_3 row 0, 1]),
    (ac.is_valid row 0 - aa.rs2_as row 0, [ac.c_0 row 0, ac.c_1 row 0, 0, 0])
  ]

lemma bitwiseBus_balanced_row [Field ExtF]
  {air : Valid_VmAirWrapper_alu FBB ExtF}
  {row : ℕ}
:
  let aa := air.adapter
  let ac := air.core
  let f := fun (x : ℕ → ℕ → FBB) => x row 0
  InteractionList.balanced_by_ordered
    (bitwiseBus_row air row)
    [
      Interaction.bitwiseBus_entry mul0 a0 b0 l0,
      Interaction.bitwiseBus_entry mul1 a1 b1 l1,
      Interaction.bitwiseBus_entry mul2 a2 b2 l2,
      Interaction.bitwiseBus_entry mul3 a3 b3 l3,
      Interaction.bitwiseBus_entry mul4 a4 b4 l4
    ]
  → (f ac.is_valid = 1 → (f ac.x_0).val < 256 ∧ (f ac.y_0).val < 256 ∧ (f ac.x_xor_y_0).val < 256 ∧ (f ac.x_xor_y_0).val = (f ac.x_0).val ^^^ (f ac.y_0).val) ∧
    (f ac.is_valid = 1 → (f ac.x_1).val < 256 ∧ (f ac.y_1).val < 256 ∧ (f ac.x_xor_y_1).val < 256 ∧ (f ac.x_xor_y_1).val = (f ac.x_1).val ^^^ (f ac.y_1).val) ∧
    (f ac.is_valid = 1 → (f ac.x_2).val < 256 ∧ (f ac.y_2).val < 256 ∧ (f ac.x_xor_y_2).val < 256 ∧ (f ac.x_xor_y_2).val = (f ac.x_2).val ^^^ (f ac.y_2).val) ∧
    (f ac.is_valid = 1 → (f ac.x_3).val < 256 ∧ (f ac.y_3).val < 256 ∧ (f ac.x_xor_y_3).val < 256 ∧ (f ac.x_xor_y_3).val = (f ac.x_3).val ^^^ (f ac.y_3).val) ∧
    (f ac.is_valid - f aa.rs2_as = 1 → (f ac.c_0).val < 256 ∧ (f ac.c_1).val < 256 ∧ f ac.c_0 = f ac.c_1)

:= by
  simp [bitwiseBus_row, InteractionList.balanced_by_ordered]
  intro b0' b1' b2' b3' b4'
  apply Interaction.bitwiseBus_balances_facts at b0'
  apply Interaction.bitwiseBus_balances_facts at b1'
  apply Interaction.bitwiseBus_balances_facts at b2'
  apply Interaction.bitwiseBus_balances_facts at b3'
  apply Interaction.bitwiseBus_balances_facts at b4'
  rw [@Fin.ext_iff _ (air.core.c_0 row 0) (air.core.c_1 row 0), ← @Nat.xor_eq_zero (air.core.c_0 row 0).val (air.core.c_1 row 0)]
  split_ands <;> [ grind; grind; grind; grind; skip ]
  . intro heq; rw [heq] at b4'; grind

end BitwiseBus

section last_row_zero

lemma buses_last_row_zero [Field ExtF]
  {air : Valid_VmAirWrapper_alu FBB ExtF}
  (h_ci : VmAirWrapper_alu.extraction.constrain_interactions air)
  (h_last_row : air.last_row = 0)
:
  air.buses ExecutionBus = executionBus_row air 0 ∧
  air.buses MemoryBus = memoryBus_row air 0 ∧
  air.buses RangeCheckerBus = rangeBus_row air 0 ∧
  air.buses ReadInstructionBus = readInstructionBus_row air 0 ∧
  air.buses BitwiseBus = bitwiseBus_row air 0
:= by
  simp [h_last_row,
        buses_eq air h_ci,
        executionBus_row,
        memoryBus_row,
        rangeBus_row,
        readInstructionBus_row,
        bitwiseBus_row]

end last_row_zero

end VmAirWrapper_alu.buses
