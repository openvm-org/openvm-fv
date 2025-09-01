import OpenvmFv.Fundamentals.BabyBear

import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Extraction.VmAirWrapper_alu
import OpenvmFv.Util

set_option maxHeartbeats 1_000_000_000

namespace VmAirWrapper_alu.constraints

def constraint_list
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu (Fin BB) ExtF)
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
    VmAirWrapper_alu.extraction.constraint_21 c row
  ]

@[simp]
def allHold
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu (Fin BB) ExtF)
  (row : ℕ) : Prop :=
  List.Forall (fun x => x) (constraint_list c row)

lemma allHold_constraints
  [Field ExtF]
  (c : Valid_VmAirWrapper_alu (Fin BB) ExtF)
  (row : ℕ)
:
  allHold c row ↔
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
    (c.core.is_valid row 0 = 0 ∨ c.adapter.from_state.timestamp row 0 + 2 - c.adapter.writes_aux.base.prev_timestamp row 0 - 1 = c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 + c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072)
:= by
  simp [constraint_list]
  simp_all [openvm_encapsulation]
  repeat rw [eq_comm (a := (1 : Fin BB))]
  repeat rw [eq_comm (a := (255 : Fin BB))]
  simp

  lemma constrain_interactions' [Field ExtF]
    (c: Valid_VmAirWrapper_alu (Fin BB) ExtF)
    (h: VmAirWrapper_alu.extraction.constrain_interactions c)
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

end VmAirWrapper_alu.constraints
