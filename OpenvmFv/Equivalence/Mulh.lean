import OpenvmFv.Spec.Mulh

import OpenvmFv.RV32D.mulh
import OpenvmFv.RV32D.mulhsu
import OpenvmFv.RV32D.mulhu

namespace Equivalence.Mulh

  @[ext]
  structure MULH_instruction_fields where
    is_valid : FBB

    pc : FBB
    next_pc : FBB

    opcode : FBB

    prev_a_timestamp : FBB
    a_timestamp : FBB
    prev_b_timestamp : FBB
    b_timestamp : FBB
    prev_c_timestamp : FBB
    c_timestamp : FBB
    timestamp : FBB
    next_timestamp : FBB

    rs1_ptr : FBB
    rs2_ptr : FBB
    rd_ptr : FBB

    prev_a : Vector FBB 4
    a : Vector FBB 4
    b : Vector FBB 4
    c : Vector FBB 4

    bitwise_check : FBB

    range_checked_vals : Vector FBB 6
    bitwise_vals : Vector (Vector FBB 3) 1
    range_checked_tuples : Vector (Vector FBB 2) 8

  lemma MULH_instruction_fields_eq (a b : MULH_instruction_fields)
  :
    a.is_valid = b.is_valid ∧
    a.pc = b.pc ∧
    a.next_pc = b.next_pc ∧
    a.opcode = b.opcode ∧
    a.prev_a_timestamp = b.prev_a_timestamp ∧
    a.a_timestamp = b.a_timestamp ∧
    a.prev_b_timestamp = b.prev_b_timestamp ∧
    a.b_timestamp = b.b_timestamp ∧
    a.prev_c_timestamp = b.prev_c_timestamp ∧
    a.c_timestamp = b.c_timestamp ∧
    a.timestamp = b.timestamp ∧
    a.next_timestamp = b.next_timestamp ∧
    a.rs1_ptr = b.rs1_ptr ∧
    a.rs2_ptr = b.rs2_ptr ∧
    a.rd_ptr = b.rd_ptr ∧
    a.prev_a = b.prev_a ∧
    a.a = b.a ∧
    a.b = b.b ∧
    a.c = b.c ∧
    a.bitwise_check = b.bitwise_check ∧
    a.range_checked_vals = b.range_checked_vals ∧
    a.bitwise_vals = b.bitwise_vals ∧
    a.range_checked_tuples = b.range_checked_tuples
      → a = b
  := by
    intro field_eq
    ext <;> grind


  def MulhInput_of_MULH_instruction_fields (row : MULH_instruction_fields) : PureSpec.MulhInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := Transpiler.wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.MulhInput
  }

  def MulhsuInput_of_MULH_instruction_fields (row : MULH_instruction_fields) : PureSpec.MulhsuInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := Transpiler.wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.MulhsuInput
  }

  def MulhuInput_of_MULH_instruction_fields (row : MULH_instruction_fields) : PureSpec.MulhuInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := Transpiler.wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.MulhuInput
  }

  def MulhOutput_matches_MULH_instruction_fields (row : MULH_instruction_fields) (mulh_output : PureSpec.MulhOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    mulh_output.nextPC = row.next_pc.toNat ∧
    match mulh_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def MulhsuOutput_matches_MULH_instruction_fields (row : MULH_instruction_fields) (mulhsu_output : PureSpec.MulhsuOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    mulhsu_output.nextPC = row.next_pc.toNat ∧
    match mulhsu_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def MulhuOutput_matches_MULH_instruction_fields (row : MULH_instruction_fields) (mulhu_output : PureSpec.MulhuOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    mulhu_output.nextPC = row.next_pc.toNat ∧
    match mulhu_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def MULH_instruction_fields.spec (row : MULH_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode ∈ Finset.Icc 593 595 ∧
      (row.opcode = 593 →
        MulhOutput_matches_MULH_instruction_fields
          row
          (PureSpec.execute_MULH_mulh_pure (MulhInput_of_MULH_instruction_fields row))
      ) ∧
      (row.opcode = 594 →
        MulhsuOutput_matches_MULH_instruction_fields
          row
          (PureSpec.execute_MULH_mulhsu_pure (MulhsuInput_of_MULH_instruction_fields row))
      ) ∧
      (row.opcode = 595 →
        MulhuOutput_matches_MULH_instruction_fields
          row
          (PureSpec.execute_MULH_mulhu_pure (MulhuInput_of_MULH_instruction_fields row))
      )
    )

  def MULH_instruction_fields.execution (row : MULH_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def MULH_instruction_fields.memory (row : MULH_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.prev_b_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.b_timestamp]),
    (-row.is_valid, [1, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.prev_c_timestamp]),
    ( row.is_valid, [1, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.c_timestamp]),
    (-row.is_valid, [1, row.rd_ptr, row.prev_a[0], row.prev_a[1], row.prev_a[2], row.prev_a[3], row.prev_a_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.a_timestamp]),
  ]

  def MULH_instruction_fields.range_checks (row : MULH_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
    (row.is_valid, [row.range_checked_vals[2], 17]),
    (row.is_valid, [row.range_checked_vals[3], 12]),
    (row.is_valid, [row.range_checked_vals[4], 17]),
    (row.is_valid, [row.range_checked_vals[5], 12]),
  ]

  def MULH_instruction_fields.read_instruction (row : MULH_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, row.rs1_ptr, row.rs2_ptr, 1, 0, 0, 0])
  ]

  def MULH_instruction_fields.bitwise (row : MULH_instruction_fields) : List (FBB × List FBB) := [
    (row.bitwise_check, [row.bitwise_vals[0][0], row.bitwise_vals[0][1], row.bitwise_vals[0][2], 0])
  ]

  def MULH_instruction_fields.range_check_tuples (row : MULH_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_tuples[0][0], row.range_checked_tuples[0][1]]),
    (row.is_valid, [row.range_checked_tuples[1][0], row.range_checked_tuples[1][1]]),
    (row.is_valid, [row.range_checked_tuples[2][0], row.range_checked_tuples[2][1]]),
    (row.is_valid, [row.range_checked_tuples[3][0], row.range_checked_tuples[3][1]]),
    (row.is_valid, [row.range_checked_tuples[4][0], row.range_checked_tuples[4][1]]),
    (row.is_valid, [row.range_checked_tuples[5][0], row.range_checked_tuples[5][1]]),
    (row.is_valid, [row.range_checked_tuples[6][0], row.range_checked_tuples[6][1]]),
    (row.is_valid, [row.range_checked_tuples[7][0], row.range_checked_tuples[7][1]])
  ]

  def bus_from_instruction_fields (rows : List MULH_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then              rows.flatMap MULH_instruction_fields.execution
      else if index = MemoryBus then            rows.flatMap MULH_instruction_fields.memory
      else if index = RangeCheckerBus then      rows.flatMap MULH_instruction_fields.range_checks
      else if index = ProgramBus then   rows.flatMap MULH_instruction_fields.read_instruction
      else if index = BitwiseBus then           rows.flatMap MULH_instruction_fields.bitwise
      else if index = RangeTupleCheckerBus then rows.flatMap MULH_instruction_fields.range_check_tuples
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_mulh FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_mulh.constraints.allHold air row.1 (by grind)

  def get_instruction_fields_row (air : Valid_VmAirWrapper_mulh FBB ExtF) (row : ℕ) : MULH_instruction_fields := {
    is_valid := air.core.is_valid row 0
    pc := air.adapter.from_state.pc row 0
    next_pc := air.adapter.from_state.pc row 0 + 4
    opcode := (air.core.ctx row 0).instruction.opcode
    prev_a_timestamp := air.adapter.writes_aux.base.prev_timestamp row 0
    a_timestamp := air.adapter.from_state.timestamp row 0 + 2
    prev_b_timestamp := air.adapter.reads_aux_0.base.prev_timestamp row 0
    b_timestamp := air.adapter.from_state.timestamp row 0
    prev_c_timestamp := air.adapter.reads_aux_1.base.prev_timestamp row 0
    c_timestamp := air.adapter.from_state.timestamp row 0 + 1
    timestamp := air.adapter.from_state.timestamp row 0
    next_timestamp := air.adapter.from_state.timestamp row 0 + 3
    rs1_ptr := air.adapter.rs1_ptr row 0
    rs2_ptr := air.adapter.rs2_ptr row 0
    rd_ptr := air.adapter.rd_ptr row 0
    prev_a := #v[air.adapter.writes_aux.prev_data_0 row 0,
                 air.adapter.writes_aux.prev_data_1 row 0,
                 air.adapter.writes_aux.prev_data_2 row 0,
                 air.adapter.writes_aux.prev_data_3 row 0]
    a := #v[air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0]
    b := #v[air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0]
    c := #v[air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0]
    bitwise_check := air.core.opcode_mulh_flag row 0 + air.core.opcode_mulhsu_flag row 0
    range_checked_vals :=
      #v[air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0,
         air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0,
         air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0]
    bitwise_vals :=
      #v[
        #v[2 * (air.core.b_3 row 0 - air.core.b_sign row 0 * 128), (air.core.opcode_mulh_flag row 0 + 1) * (air.core.c_3 row 0 - air.core.c_sign row 0 * 128), 0]
      ]
    range_checked_tuples :=
      #v[
        #v[air.core.a_mul_0 row 0, air.core.carry_mul row 0 0],
        #v[air.core.a_mul_1 row 0, air.core.carry_mul row 0 1],
        #v[air.core.a_mul_2 row 0, air.core.carry_mul row 0 2],
        #v[air.core.a_mul_3 row 0, air.core.carry_mul row 0 3],
        #v[air.core.a_0 row 0, 2005401601 * (air.core.carry_mul row 0 3 + (air.core.b_1 row 0 * air.core.c_3 row 0 + air.core.b_2 row 0 * air.core.c_2 row 0 + air.core.b_3 row 0 * air.core.c_1 row 0) + (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0) - air.core.a_0 row 0)],
        #v[air.core.a_1 row 0, 2005401601 * (2005401601 * (air.core.carry_mul row 0 3 + (air.core.b_1 row 0 * air.core.c_3 row 0 + air.core.b_2 row 0 * air.core.c_2 row 0 + air.core.b_3 row 0 * air.core.c_1 row 0) + (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0) - air.core.a_0 row 0) + (air.core.b_2 row 0 * air.core.c_3 row 0 + air.core.b_3 row 0 * air.core.c_2 row 0) + (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 + air.core.b_1 row 0 * air.core.c_ext row 0 + air.core.c_1 row 0 * air.core.b_ext row 0) - air.core.a_1 row 0)],
        #v[air.core.a_2 row 0, 2005401601 * (2005401601 * (2005401601 * (air.core.carry_mul row 0 3 + (air.core.b_1 row 0 * air.core.c_3 row 0 + air.core.b_2 row 0 * air.core.c_2 row 0 + air.core.b_3 row 0 * air.core.c_1 row 0) + (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0) - air.core.a_0 row 0) + (air.core.b_2 row 0 * air.core.c_3 row 0 + air.core.b_3 row 0 * air.core.c_2 row 0) + (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 + air.core.b_1 row 0 * air.core.c_ext row 0 + air.core.c_1 row 0 * air.core.b_ext row 0) - air.core.a_1 row 0) + air.core.b_3 row 0 * air.core.c_3 row 0 + (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 + air.core.b_1 row 0 * air.core.c_ext row 0 + air.core.c_1 row 0 * air.core.b_ext row 0 + air.core.b_2 row 0 * air.core.c_ext row 0 + air.core.c_2 row 0 * air.core.b_ext row 0) - air.core.a_2 row 0)],
        #v[air.core.a_3 row 0, 2005401601 * (2005401601 * (2005401601 * (2005401601 * (air.core.carry_mul row 0 3 + (air.core.b_1 row 0 * air.core.c_3 row 0 + air.core.b_2 row 0 * air.core.c_2 row 0 + air.core.b_3 row 0 * air.core.c_1 row 0) + (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0) - air.core.a_0 row 0) + (air.core.b_2 row 0 * air.core.c_3 row 0 + air.core.b_3 row 0 * air.core.c_2 row 0) + (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 + air.core.b_1 row 0 * air.core.c_ext row 0 + air.core.c_1 row 0 * air.core.b_ext row 0) - air.core.a_1 row 0) + air.core.b_3 row 0 * air.core.c_3 row 0 + (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 + air.core.b_1 row 0 * air.core.c_ext row 0 + air.core.c_1 row 0 * air.core.b_ext row 0 + air.core.b_2 row 0 * air.core.c_ext row 0 + air.core.c_2 row 0 * air.core.b_ext row 0) - air.core.a_2 row 0) + (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 + air.core.b_1 row 0 * air.core.c_ext row 0 + air.core.c_1 row 0 * air.core.b_ext row 0 + air.core.b_2 row 0 * air.core.c_ext row 0 + air.core.c_2 row 0 * air.core.b_ext row 0 + air.core.b_3 row 0 * air.core.c_ext row 0 + air.core.c_3 row 0 * air.core.b_ext row 0) - air.core.a_3 row 0)]
      ]
  }

  def get_instruction_fields (air : Valid_VmAirWrapper_mulh FBB ExtF) : List MULH_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma execution_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mulh.constraints.executionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MULH_instruction_fields.execution (get_instruction_fields air)
  := by
    unfold MULH_instruction_fields.execution
    unfold VmAirWrapper_mulh.constraints.executionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma memory_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mulh.constraints.memoryBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MULH_instruction_fields.memory (get_instruction_fields air)
  := by
    unfold MULH_instruction_fields.memory
    unfold VmAirWrapper_mulh.constraints.memoryBus_row
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      h_neg_one
    ]

  lemma range_checks_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mulh.constraints.rangeCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MULH_instruction_fields.range_checks (get_instruction_fields air)
  := by
    unfold MULH_instruction_fields.range_checks
    unfold VmAirWrapper_mulh.constraints.rangeCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma read_instruction_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mulh.constraints.programBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MULH_instruction_fields.read_instruction (get_instruction_fields air)
  := by
    unfold MULH_instruction_fields.read_instruction
    unfold VmAirWrapper_mulh.constraints.programBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
    ]

  lemma bitwise_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mulh.constraints.bitwiseBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MULH_instruction_fields.bitwise (get_instruction_fields air)
  := by
    unfold MULH_instruction_fields.bitwise
    unfold VmAirWrapper_mulh.constraints.bitwiseBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
    ]

  lemma range_check_tuples_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mulh.constraints.rangeTupleCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MULH_instruction_fields.range_check_tuples (get_instruction_fields air)
  := by
    unfold MULH_instruction_fields.range_check_tuples
    unfold VmAirWrapper_mulh.constraints.rangeTupleCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
    ]

  lemma bus_from_instruction_fields_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (h_constraints : allHold_allRows air)
  :
    air.buses = bus_from_instruction_fields (get_instruction_fields air)
  := by
    have h_interactions := VmAirWrapper_mulh.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_mulh.constraints.constrain_interactions at h_interactions
    rewrite [h_interactions]; clear h_interactions
    unfold bus_from_instruction_fields
    simp [
      execution_eq_air_buses,
      memory_eq_air_buses,
      range_checks_eq_air_buses,
      read_instruction_eq_air_buses,
      bitwise_eq_air_buses,
      range_check_tuples_eq_air_buses
    ]

  lemma get_instruction_fields_row_opcode_range [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow air row)
  :
    (get_instruction_fields_row air row).opcode ∈ Finset.Icc 593 595
  := by
    simp [get_instruction_fields_row]
    have :=
      VmAirWrapper_mulh.constraints.opcode_bounds
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
    grind

  lemma transpile_of_bus_wellformedness [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction a b,
    Transpiler.transpile_op instruction 1 (air.adapter.from_state.pc row 0) = some (a, b) ∧
      a = 1 ∧
        b[0] = air.adapter.from_state.pc row 0 ∧
          b[1] = (air.core.ctx row 0).instruction.opcode ∧
            b[2] = air.adapter.rd_ptr row 0 ∧
              b[3] = air.adapter.rs1_ptr row 0 ∧
                b[4] = air.adapter.rs2_ptr row 0 ∧ b[5] = 1 ∧ b[6] = 0 ∧ b[7] = 0 ∧ b[8] = 0
  := by
    unfold VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
    simp [
      VmAirWrapper_mulh.constraints.propertiesToAssume,
      Interaction.ProgramBusEntry.operand_properties,
      VmAirWrapper_mulh.constraints._programBus_row,
      VmAirWrapper_mulh.constraints.programBus_row,
      -List.map_nil, -Vector.toList_mk, -List.attach_cons
    ] at h_bus_wellformedness
    unfold Interaction.ProgramBusEntry.deserialise at h_bus_wellformedness
    dsimp [List.attach] at h_bus_wellformedness
    rewrite [h_is_valid] at h_bus_wellformedness
    simp only [
      Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.cast_one, Fin.cast_val_eq_self,
      Nat.cast_zero, Interaction.ProgramBusEntry.mk.injEq,
      forall_const
    ] at h_bus_wellformedness
    exact h_bus_wellformedness

  lemma mulh_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow air row)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 593)
  :
    ¬Transpiler.wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [Transpiler.wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile.1
    have h_bound := Transpiler.pc_bound_of_some h_transpile.1
    rewrite [h_opcode] at h_transpile
    have h_cases := Transpiler.transpiler_opcode_593 h_transpile.1 h_transpile.2.2.2.1
    obtain ⟨rs2, rs1, rd, h_instruction, h_rd⟩ := h_cases
    rewrite [h_instruction] at h_transpile
    unfold Transpiler.transpile_op at h_transpile
    rewrite [if_pos (by constructor <;> assumption)] at h_transpile
    dsimp at h_transpile
    split_ifs at h_transpile
    . have := Transpiler.extract_opcode h_transpile.1
      simp at this
      exfalso
      simp [this] at h_transpile
    . simp [-Vector.mk_eq] at h_transpile
      rewrite [←h_transpile.2.2.2.2.1, ←h_transpile.1.2]
      simp [Transpiler.ind, regidx_to_fin]
      rewrite [Nat.mod_eq_of_lt (by omega)]
      split_ands
      . by_cases h_contr : rd.1 = 0
        . simp [h_contr] at h_rd
        . simp [BitVec.toNat_eq_nat]
          convert h_contr
      . use rd

  lemma mulhsu_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow air row)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 594)
  :
    ¬Transpiler.wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [Transpiler.wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile.1
    have h_bound := Transpiler.pc_bound_of_some h_transpile.1
    rewrite [h_opcode] at h_transpile
    have h_cases := Transpiler.transpiler_opcode_594 h_transpile.1 h_transpile.2.2.2.1
    obtain ⟨rs2, rs1, rd, h_instruction, h_rd⟩ := h_cases
    rewrite [h_instruction] at h_transpile
    unfold Transpiler.transpile_op at h_transpile
    rewrite [if_pos (by constructor <;> assumption)] at h_transpile
    dsimp at h_transpile
    split_ifs at h_transpile
    . have := Transpiler.extract_opcode h_transpile.1
      simp at this
      exfalso
      simp [this] at h_transpile
    . simp [-Vector.mk_eq] at h_transpile
      rewrite [←h_transpile.2.2.2.2.1, ←h_transpile.1.2]
      simp [Transpiler.ind, regidx_to_fin]
      rewrite [Nat.mod_eq_of_lt (by omega)]
      split_ands
      . by_cases h_contr : rd.1 = 0
        . simp [h_contr] at h_rd
        . simp [BitVec.toNat_eq_nat]
          convert h_contr
      . use rd

  lemma mulhu_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow air row)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 595)
  :
    ¬Transpiler.wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [Transpiler.wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile.1
    have h_bound := Transpiler.pc_bound_of_some h_transpile.1
    rewrite [h_opcode] at h_transpile
    have h_cases := Transpiler.transpiler_opcode_595 h_transpile.1 h_transpile.2.2.2.1
    obtain ⟨rs2, rs1, rd, h_instruction, h_rd⟩ := h_cases
    rewrite [h_instruction] at h_transpile
    unfold Transpiler.transpile_op at h_transpile
    rewrite [if_pos (by constructor <;> assumption)] at h_transpile
    dsimp at h_transpile
    split_ifs at h_transpile
    . have := Transpiler.extract_opcode h_transpile.1
      simp at this
      exfalso
      simp [this] at h_transpile
    . simp [-Vector.mk_eq] at h_transpile
      rewrite [←h_transpile.2.2.2.2.1, ←h_transpile.1.2]
      simp [Transpiler.ind, regidx_to_fin]
      rewrite [Nat.mod_eq_of_lt (by omega)]
      split_ands
      . by_cases h_contr : rd.1 = 0
        . simp [h_contr] at h_rd
        . simp [BitVec.toNat_eq_nat]
          convert h_contr
      . use rd


  lemma mulh_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 593 →
        MulhOutput_matches_MULH_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_MULH_mulh_pure
            (MulhInput_of_MULH_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [MulhOutput_matches_MULH_instruction_fields]

    obtain ⟨
      h_pc,
      ub_a0, ub_a1, ub_a2, ub_a3,
      ub_b0, ub_b1, ub_b2, ub_b3,
      ub_c0, ub_c1, ub_c2, ub_c3
    ⟩ :=
      Mulh.ValidRows.essentials
        ExtF air row h_row
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_axioms row (by omega))
        (h_bus_wellformedness row (by omega))

    simp [get_instruction_fields_row, *]

    split_ands
    . clear *- h_bus_axioms h_row h_is_valid h_pc
      simp [PureSpec.execute_MULH_mulh_pure, MulhInput_of_MULH_instruction_fields]
      simp [← BitVec.toNat_inj]
      specialize h_bus_axioms row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . simp [MulhInput_of_MULH_instruction_fields, PureSpec.execute_MULH_mulh_pure]
      have h_rd := mulh_rd_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind⟩ := h_rd
      simp [get_instruction_fields_row] at h_rd_non_zero h_rd_ind
      simp only [dite_cond_eq_false, h_rd_non_zero]
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind

      split_ands
      . have := Mulh.ValidRows.spec_MULH
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_wellformedness row (by omega))
          (by clear *- h_opcode; assumption)
        trans (U32.toBV #v[(air.core.a_0 row 0).val, (air.core.a_1 row 0).val, (air.core.a_2 row 0).val, (air.core.a_3 row 0).val])
        . congr
        . rw [this]
          simp [h_opcode, Mulh.ValidRows.rop_of_Mulh_opcode]
          congr
      . rw [h_rd_ind]
        simp [Transpiler.ind, regidx_to_fin, Transpiler.wrap_to_regidx]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma mulhsu_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 594 →
        MulhsuOutput_matches_MULH_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_MULH_mulhsu_pure
            (MulhsuInput_of_MULH_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [MulhsuOutput_matches_MULH_instruction_fields]

    obtain ⟨
      h_pc,
      ub_a0, ub_a1, ub_a2, ub_a3,
      ub_b0, ub_b1, ub_b2, ub_b3,
      ub_c0, ub_c1, ub_c2, ub_c3
    ⟩ :=
      Mulh.ValidRows.essentials
        ExtF air row h_row
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_axioms row (by omega))
        (h_bus_wellformedness row (by omega))

    simp [get_instruction_fields_row, *]

    split_ands
    . clear *- h_bus_axioms h_row h_is_valid h_pc
      simp [PureSpec.execute_MULH_mulhsu_pure, MulhsuInput_of_MULH_instruction_fields]
      simp [← BitVec.toNat_inj]
      specialize h_bus_axioms row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . simp [MulhsuInput_of_MULH_instruction_fields, PureSpec.execute_MULH_mulhsu_pure]
      have h_rd := mulhsu_rd_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind⟩ := h_rd
      simp [get_instruction_fields_row] at h_rd_non_zero h_rd_ind
      simp only [dite_cond_eq_false, h_rd_non_zero]
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind

      split_ands
      . have := Mulh.ValidRows.spec_MULHSU
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_wellformedness row (by omega))
          (by clear *- h_opcode; assumption)
        trans (U32.toBV #v[(air.core.a_0 row 0).val, (air.core.a_1 row 0).val, (air.core.a_2 row 0).val, (air.core.a_3 row 0).val])
        . congr
        . rw [this]
          simp [h_opcode, Mulh.ValidRows.rop_of_Mulh_opcode]
          congr
      . rw [h_rd_ind]
        simp [Transpiler.ind, regidx_to_fin, Transpiler.wrap_to_regidx]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma mulhu_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 595 →
        MulhuOutput_matches_MULH_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_MULH_mulhu_pure
            (MulhuInput_of_MULH_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [MulhuOutput_matches_MULH_instruction_fields]

    obtain ⟨
      h_pc,
      ub_a0, ub_a1, ub_a2, ub_a3,
      ub_b0, ub_b1, ub_b2, ub_b3,
      ub_c0, ub_c1, ub_c2, ub_c3
    ⟩ :=
      Mulh.ValidRows.essentials
        ExtF air row h_row
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_axioms row (by omega))
        (h_bus_wellformedness row (by omega))

    simp [get_instruction_fields_row, *]

    split_ands
    . clear *- h_bus_axioms h_row h_is_valid h_pc
      simp [PureSpec.execute_MULH_mulhu_pure, MulhuInput_of_MULH_instruction_fields]
      simp [← BitVec.toNat_inj]
      specialize h_bus_axioms row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . simp [MulhuInput_of_MULH_instruction_fields, PureSpec.execute_MULH_mulhu_pure]
      have h_rd := mulhu_rd_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind⟩ := h_rd
      simp [get_instruction_fields_row] at h_rd_non_zero h_rd_ind
      simp only [dite_cond_eq_false, h_rd_non_zero]
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind

      split_ands
      . have := Mulh.ValidRows.spec_MULHU
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_wellformedness row (by omega))
          (by clear *- h_opcode; assumption)
        trans (U32.toBV #v[(air.core.a_0 row 0).val, (air.core.a_1 row 0).val, (air.core.a_2 row 0).val, (air.core.a_3 row 0).val])
        . congr
        . rw [this]
          simp [h_opcode, Mulh.ValidRows.rop_of_Mulh_opcode]
          congr
      . rw [h_rd_ind]
        simp [Transpiler.ind, regidx_to_fin, Transpiler.wrap_to_regidx]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow air row)
  :
    List.Forall MULH_instruction_fields.spec (get_instruction_fields air)
  := by
    apply List.forall_iff_forall_mem.mpr
    intro instruction_fields h_instruction_fields
    unfold MULH_instruction_fields.spec

    intro h_is_valid

    simp [get_instruction_fields] at h_instruction_fields
    obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
    rewrite [←h_fields] at ⊢ h_is_valid; clear h_fields

    simp [get_instruction_fields_row] at h_is_valid
    split_ands
    . exact get_instruction_fields_row_opcode_range air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
    . exact mulh_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
    . exact mulhsu_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
    . exact mulhu_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness

  theorem mulh_spec [Field ExtF]
    (air : Valid_VmAirWrapper_mulh FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_mulh.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List MULH_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall MULH_instruction_fields.spec
  := by
    use get_instruction_fields air
    simp only [
      bus_from_instruction_fields_eq_air_buses air h_constraints,
      spec_of_get_instruction_fields air h_constraints h_bus_axioms h_bus_wellformedness
    ]
    trivial

end Equivalence.Mulh
