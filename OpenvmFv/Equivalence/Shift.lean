import OpenvmFv.Spec.Shift

import OpenvmFv.Spec.RTYPE.sll
import OpenvmFv.Spec.RTYPE.sra
import OpenvmFv.Spec.RTYPE.srl

import OpenvmFv.Spec.SHIFTIOP.slli
import OpenvmFv.Spec.SHIFTIOP.srai
import OpenvmFv.Spec.SHIFTIOP.srli

set_option maxHeartbeats 1_000_000_000

namespace Equivalence.Shift

  @[ext]
  structure Shift_instruction_fields where
    is_valid : FBB
    non_imm : FBB

    pc : FBB
    next_pc : FBB

    opcode : FBB
    opcode_sra_flag : FBB

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

    range_checked_vals : Vector (Vector FBB 2) 11
    bitwise_vals : Vector (Vector FBB 3) 4

  lemma Shift_instruction_fields_eq (a b : Shift_instruction_fields)
  :
    a.is_valid = b.is_valid ∧
    a.non_imm = b.non_imm ∧
    a.pc = b.pc ∧
    a.next_pc = b.next_pc ∧
    a.opcode = b.opcode ∧
    a.opcode_sra_flag = b.opcode_sra_flag ∧
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
    a.range_checked_vals = b.range_checked_vals ∧
    a.bitwise_vals = b.bitwise_vals
      → a = b
  := by
    intro field_eq
    ext <;> grind

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val % 32, by grind⟩

  def SllInput_of_Shift_instruction_fields (row : Shift_instruction_fields) : PureSpec.SllInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SllInput
  }

  def SlliInput_of_Shift_instruction_fields (row : Shift_instruction_fields) : PureSpec.SlliInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 6 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SlliInput
  }

  def SrlInput_of_Shift_instruction_fields (row : Shift_instruction_fields) : PureSpec.SrlInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SrlInput
  }

  def SrliInput_of_Shift_instruction_fields (row : Shift_instruction_fields) : PureSpec.SrliInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 6 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SrliInput
  }

  def SraInput_of_Shift_instruction_fields (row : Shift_instruction_fields) : PureSpec.SraInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SraInput
  }

  def SraiInput_of_Shift_instruction_fields (row : Shift_instruction_fields) : PureSpec.SraiInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 6 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SraiInput
  }

  def SllOutput_matches_Shift_instruction_fields (row : Shift_instruction_fields) (add_output : PureSpec.SllOutput) : Prop :=
    row.opcode_sra_flag = 0 ∧
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    add_output.nextPC = row.next_pc.toNat ∧
    match add_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def SlliOutput_matches_Shift_instruction_fields (row : Shift_instruction_fields) (addi_output : PureSpec.SlliOutput) : Prop :=
    row.opcode_sra_flag = 0 ∧
    BabyBear.isU32 row.b ∧
    addi_output.nextPC = row.next_pc.toNat ∧
    match addi_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def SrlOutput_matches_Shift_instruction_fields (row : Shift_instruction_fields) (xor_output : PureSpec.SrlOutput) : Prop :=
    row.opcode_sra_flag = 0 ∧
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    xor_output.nextPC = row.next_pc.toNat ∧
    match xor_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def SrliOutput_matches_Shift_instruction_fields (row : Shift_instruction_fields) (xori_output : PureSpec.SrliOutput) : Prop :=
    row.opcode_sra_flag = 0 ∧
    BabyBear.isU32 row.b ∧
    xori_output.nextPC = row.next_pc.toNat ∧
    match xori_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def SraOutput_matches_Shift_instruction_fields (row : Shift_instruction_fields) (or_output : PureSpec.SraOutput) : Prop :=
    row.opcode_sra_flag = 1 ∧
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    or_output.nextPC = row.next_pc.toNat ∧
    match or_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def SraiOutput_matches_Shift_instruction_fields (row : Shift_instruction_fields) (ori_output : PureSpec.SraiOutput) : Prop :=
    row.opcode_sra_flag = 1 ∧
    BabyBear.isU32 row.b ∧
    ori_output.nextPC = row.next_pc.toNat ∧
    match ori_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def Shift_instruction_fields.spec (row : Shift_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      (row.non_imm = 0 ∨ row.non_imm = 1) ∧
      row.opcode ∈ Finset.Icc 517 519 ∧
      (row.non_imm = 1 → (
        (row.opcode = 517 →
          SllOutput_matches_Shift_instruction_fields
            row
            (PureSpec.execute_RTYPE_sll_pure (SllInput_of_Shift_instruction_fields row))
        ) ∧
        (row.opcode = 518 →
          SrlOutput_matches_Shift_instruction_fields
            row
            (PureSpec.execute_RTYPE_srl_pure (SrlInput_of_Shift_instruction_fields row))
        ) ∧
        (row.opcode = 519 →
          SraOutput_matches_Shift_instruction_fields
            row
            (PureSpec.execute_RTYPE_sra_pure (SraInput_of_Shift_instruction_fields row))
        )
      )) ∧
      (row.non_imm = 0 → (
        (row.opcode = 517 →
          SlliOutput_matches_Shift_instruction_fields
            row
            (PureSpec.execute_SHIFTIOP_slli_pure (SlliInput_of_Shift_instruction_fields row))
        ) ∧
        (row.opcode = 518 →
          SrliOutput_matches_Shift_instruction_fields
            row
            (PureSpec.execute_SHIFTIOP_srli_pure (SrliInput_of_Shift_instruction_fields row))
        ) ∧
        (row.opcode = 519 →
          SraiOutput_matches_Shift_instruction_fields
            row
            (PureSpec.execute_SHIFTIOP_srai_pure (SraiInput_of_Shift_instruction_fields row))
        )
      ))
    )

  def Shift_instruction_fields.execution (row : Shift_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def Shift_instruction_fields.memory (row : Shift_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.prev_b_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.b_timestamp]),
    (-row.non_imm, [row.non_imm, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.prev_c_timestamp]),
    ( row.non_imm, [row.non_imm, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.c_timestamp]),
    (-row.is_valid, [1, row.rd_ptr, row.prev_a[0], row.prev_a[1], row.prev_a[2], row.prev_a[3], row.prev_a_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.a_timestamp]),
  ]

  def Shift_instruction_fields.range_checks (row : Shift_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0][0], row.range_checked_vals[0][1]]),
    (row.is_valid, [row.range_checked_vals[1][0], row.range_checked_vals[1][1]]),
    (row.is_valid, [row.range_checked_vals[2][0], row.range_checked_vals[2][1]]),
    (row.is_valid, [row.range_checked_vals[3][0], row.range_checked_vals[3][1]]),
    (row.is_valid, [row.range_checked_vals[4][0], row.range_checked_vals[4][1]]),
    (row.is_valid, [row.range_checked_vals[5][0], row.range_checked_vals[5][1]]),
    (row.is_valid, [row.range_checked_vals[6][0], row.range_checked_vals[6][1]]),
    (row.non_imm, [row.range_checked_vals[7][0], row.range_checked_vals[7][1]]),
    (row.non_imm, [row.range_checked_vals[8][0], row.range_checked_vals[8][1]]),
    (row.is_valid, [row.range_checked_vals[9][0], row.range_checked_vals[9][1]]),
    (row.is_valid, [row.range_checked_vals[10][0], row.range_checked_vals[10][1]]),
  ]

  def Shift_instruction_fields.read_instruction (row : Shift_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, row.rs1_ptr, row.rs2_ptr, 1, row.non_imm, 0, 0])
  ]

  def Shift_instruction_fields.bitwise (row : Shift_instruction_fields) : List (FBB × List FBB) := [
    (row.opcode_sra_flag, [row.bitwise_vals[0][0], row.bitwise_vals[0][1], row.bitwise_vals[0][2], 1]),
    (row.is_valid, [row.bitwise_vals[1][0], row.bitwise_vals[1][1], row.bitwise_vals[1][2], 0]),
    (row.is_valid, [row.bitwise_vals[2][0], row.bitwise_vals[2][1], row.bitwise_vals[2][2], 0]),
    (row.is_valid - row.non_imm, [row.bitwise_vals[3][0], row.bitwise_vals[3][1], row.bitwise_vals[3][2], 0]),
  ]

  def bus_from_instruction_fields (rows : List Shift_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then            rows.flatMap Shift_instruction_fields.execution
      else if index = MemoryBus then          rows.flatMap Shift_instruction_fields.memory
      else if index = RangeCheckerBus then    rows.flatMap Shift_instruction_fields.range_checks
      else if index = ReadInstructionBus then rows.flatMap Shift_instruction_fields.read_instruction
      else if index = BitwiseBus then         rows.flatMap Shift_instruction_fields.bitwise
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_shift FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_shift.constraints.allHold air row.1 (by grind)

  def get_instruction_fields_row (air : Valid_VmAirWrapper_shift FBB ExtF) (row : ℕ) : Shift_instruction_fields := {
    is_valid := air.core.is_valid row 0
    non_imm := air.adapter.rs2_as row 0
    pc := air.adapter.from_state.pc row 0
    next_pc := air.adapter.from_state.pc row 0 + 4
    opcode := (air.core.ctx row 0).instruction.opcode
    opcode_sra_flag := air.core.opcode_sra_flag row 0
    prev_a_timestamp := air.adapter.writes_aux.base.prev_timestamp row 0
    a_timestamp := air.adapter.from_state.timestamp row 0 + 2
    prev_b_timestamp := air.adapter.reads_aux_0.base.prev_timestamp row 0
    b_timestamp := air.adapter.from_state.timestamp row 0
    prev_c_timestamp := air.adapter.reads_aux_1.base.prev_timestamp row 0
    c_timestamp := air.adapter.from_state.timestamp row 0 + 1
    timestamp := air.adapter.from_state.timestamp row 0
    next_timestamp := air.adapter.from_state.timestamp row 0 + 3
    rs1_ptr := air.adapter.rs1_ptr row 0
    rs2_ptr := air.adapter.rs2 row 0
    rd_ptr := air.adapter.rd_ptr row 0
    prev_a := #v[air.adapter.writes_aux.prev_data_0 row 0,
                  air.adapter.writes_aux.prev_data_1 row 0,
                  air.adapter.writes_aux.prev_data_2 row 0,
                  air.adapter.writes_aux.prev_data_3 row 0]
    a := #v[air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0]
    b := #v[air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0]
    c := #v[air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0]
    range_checked_vals :=
      #v[
        #v[(air.core.c_0 row 0 - air.core.limb_shift row 0 3 * 8 - air.core.bit_shift row 0) * 1950351361, 3],
        #v[air.core.bit_shift_carry_0 row 0, air.core.bit_shift row 0],
        #v[air.core.bit_shift_carry_1 row 0, air.core.bit_shift row 0],
        #v[air.core.bit_shift_carry_2 row 0, air.core.bit_shift row 0],
        #v[air.core.bit_shift_carry_3 row 0, air.core.bit_shift row 0],
        #v[air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17],
        #v[air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12],
        #v[air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17],
        #v[air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12],
        #v[air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17],
        #v[air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12],
      ]
    bitwise_vals :=
      #v[
        #v[air.core.b_3 row 0, 128, air.core.b_3 row 0 + 128 - 2 * (air.core.b_sign row 0 * 128)],
        #v[air.core.a_0 row 0, air.core.a_1 row 0, 0],
        #v[air.core.a_2 row 0, air.core.a_3 row 0, 0],
        #v[air.core.c_0 row 0, air.core.c_1 row 0, 0]
      ]
    : Shift_instruction_fields
  }


  def get_instruction_fields (air : Valid_VmAirWrapper_shift FBB ExtF) : List Shift_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma execution_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
  :
    List.flatMap (VmAirWrapper_shift.constraints.executionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap Shift_instruction_fields.execution (get_instruction_fields air)
  := by
    unfold Shift_instruction_fields.execution
    unfold VmAirWrapper_shift.constraints.executionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma memory_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
  :
    List.flatMap (VmAirWrapper_shift.constraints.memoryBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap Shift_instruction_fields.memory (get_instruction_fields air)
  := by
    unfold Shift_instruction_fields.memory
    unfold VmAirWrapper_shift.constraints.memoryBus_row
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      h_neg_one
    ]

  lemma range_checks_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
  :
    List.flatMap (VmAirWrapper_shift.constraints.rangeCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap Shift_instruction_fields.range_checks (get_instruction_fields air)
  := by
    unfold Shift_instruction_fields.range_checks
    unfold VmAirWrapper_shift.constraints.rangeCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma read_instruction_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
  :
    List.flatMap (VmAirWrapper_shift.constraints.readInstructionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap Shift_instruction_fields.read_instruction (get_instruction_fields air)
  := by
    unfold Shift_instruction_fields.read_instruction
    unfold VmAirWrapper_shift.constraints.readInstructionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma bitwise_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
  :
    List.flatMap (VmAirWrapper_shift.constraints.bitwiseBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap Shift_instruction_fields.bitwise (get_instruction_fields air)
  := by
    unfold Shift_instruction_fields.bitwise
    unfold VmAirWrapper_shift.constraints.bitwiseBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma bus_from_instruction_fields_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (h_constraints : allHold_allRows air)
  :
    air.buses = bus_from_instruction_fields (get_instruction_fields air)
  := by
    have h_interactions := VmAirWrapper_shift.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_shift.constraints.constrain_interactions at h_interactions
    rewrite [h_interactions]; clear h_interactions
    unfold bus_from_instruction_fields
    simp [
      execution_eq_air_buses,
      memory_eq_air_buses,
      range_checks_eq_air_buses,
      read_instruction_eq_air_buses,
      bitwise_eq_air_buses
    ]

  lemma get_instruction_fields_row_non_imm_binary [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
  :
    (get_instruction_fields_row air row).non_imm = 0 ∨
    (get_instruction_fields_row air row).non_imm = 1
  := by
    simp [get_instruction_fields_row]
    have := Shift.ValidRows.essentials
      ExtF
      air
      row
      (by omega)
      (h_constraints ⟨row, by omega⟩)
      h_is_valid
      (h_bus_wellformedness row (by omega))

    exact this.2.2.1

  lemma get_instruction_fields_row_opcode_range [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
  :
    (get_instruction_fields_row air row).opcode ∈ Finset.Icc 517 519
  := by
    simp [get_instruction_fields_row]
    have := Shift.ValidRows.essentials
      ExtF
      air
      row
      (by omega)
      (h_constraints ⟨row, by omega⟩)
      h_is_valid
      (h_bus_wellformedness row (by omega))

    replace this := this.2.1
    grind

  lemma sll_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
  :
    ((get_instruction_fields_row air row).opcode = 517 →
        SllOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_sll_pure
            (SllInput_of_Shift_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SllOutput_matches_Shift_instruction_fields]
    have ⟨
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties,
        h_bit_multiplier_left,
        h_bit_multiplier_right,
        h_bit_shift_carry_0,
        h_bit_shift_carry_1,
        h_bit_shift_carry_2,
        h_bit_shift_carry_3
      ⟩:= Shift.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
    split_ands
    . clear *- h_row h_constraints h_opcode h_is_valid
      have := VmAirWrapper_shift.constraints.single_op
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      have := VmAirWrapper_shift.constraints.op_from_opcode
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      simp [get_instruction_fields_row]
      grind
    . clear *-h_b0
      simp [get_instruction_fields_row, h_b0]
    . clear *-h_b1
      simp [get_instruction_fields_row, h_b1]
    . clear *-h_b2
      simp [get_instruction_fields_row, h_b2]
    . clear *-h_b3
      simp [get_instruction_fields_row, h_b3]
    . clear *-h_c0
      simp [get_instruction_fields_row, h_c0]
    . clear *-h_c1
      simp [get_instruction_fields_row, h_c1]
    . clear *-h_c2
      simp [get_instruction_fields_row, h_c2]
    . clear *-h_c3
      simp [List.Forall] at h_c3
      simp [get_instruction_fields_row, h_c3]
    . clear *-h_bus_assumptions h_row h_is_valid
      simp [PureSpec.execute_RTYPE_sll_pure, SllInput_of_Shift_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      simp [
        VmAirWrapper_shift.constraints.assumptionsPerRow,
        VmAirWrapper_shift_constraint_and_interaction_simplification
      ] at h_bus_assumptions
      replace h_bus_assumptions := h_bus_assumptions.1
      simp [VmAirWrapper_shift.constraints.assumptions, h_is_valid] at h_bus_assumptions
      omega
    . clear *-h_bus_wellformedness h_row h_is_valid h_opcode h_a0 h_a1 h_a2 h_a3 h_constraints h_non_imm
      simp [SllInput_of_Shift_instruction_fields, PureSpec.execute_RTYPE_sll_pure]
      have h_rd : ¬(wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0) ∧ (get_instruction_fields_row air row).rd_ptr < 32  := by
        clear *-h_bus_wellformedness h_row h_is_valid h_opcode
        specialize h_bus_wellformedness row h_row
        unfold VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
        simp [
          VmAirWrapper_shift_constraint_and_interaction_simplification,
          VmAirWrapper_shift.constraints.propertiesToAssume,
          Interaction.ReadInstructionBusEntry.operand_properties,
          h_is_valid
        ] at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.1
        simp [wrap_to_regidx, get_instruction_fields_row]
        replace h_bus_wellformedness := (h_bus_wellformedness (by omega) (by omega)).1
        omega
      obtain ⟨h_rd_non_zero, h_rd_lt_32⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_lt_32
      replace h_rd_lt_32 := Fin.val_fin_lt.mpr h_rd_lt_32
      simp at h_rd_lt_32
      simp [
        true_and,
        h_a0,
        h_a1,
        h_a2,
        h_a3,
        wrap_to_regidx,
        h_rd_lt_32
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_lt_32

      have h_spec := Shift.ValidRows.spec_base_Shift_non_imm
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
        h_non_imm

      simp only [
        h_opcode, Shift.ValidRows.rop_of_Shift_opcode, ite_cond_eq_true, execute_RTYPE_pure,
        Sail.shift_bits_left, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      ] at h_spec

      convert h_spec
      congr
      simp
      congr

  lemma srl_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
  :
    ((get_instruction_fields_row air row).opcode = 518 →
        SrlOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_srl_pure
            (SrlInput_of_Shift_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SrlOutput_matches_Shift_instruction_fields]
    have ⟨
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties,
        h_bit_multiplier_left,
        h_bit_multiplier_right,
        h_bit_shift_carry_0,
        h_bit_shift_carry_1,
        h_bit_shift_carry_2,
        h_bit_shift_carry_3
      ⟩:= Shift.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
    split_ands
    . clear *- h_row h_constraints h_opcode h_is_valid
      have := VmAirWrapper_shift.constraints.single_op
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      have := VmAirWrapper_shift.constraints.op_from_opcode
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      simp [get_instruction_fields_row]
      grind
    . clear *-h_b0
      simp [get_instruction_fields_row, h_b0]
    . clear *-h_b1
      simp [get_instruction_fields_row, h_b1]
    . clear *-h_b2
      simp [get_instruction_fields_row, h_b2]
    . clear *-h_b3
      simp [get_instruction_fields_row, h_b3]
    . clear *-h_c0
      simp [get_instruction_fields_row, h_c0]
    . clear *-h_c1
      simp [get_instruction_fields_row, h_c1]
    . clear *-h_c2
      simp [get_instruction_fields_row, h_c2]
    . clear *-h_c3
      simp [List.Forall] at h_c3
      simp [get_instruction_fields_row, h_c3]
    . clear *-h_bus_assumptions h_row h_is_valid
      simp [PureSpec.execute_RTYPE_srl_pure, SrlInput_of_Shift_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      simp [
        VmAirWrapper_shift.constraints.assumptionsPerRow,
        VmAirWrapper_shift_constraint_and_interaction_simplification
      ] at h_bus_assumptions
      replace h_bus_assumptions := h_bus_assumptions.1
      simp [VmAirWrapper_shift.constraints.assumptions, h_is_valid] at h_bus_assumptions
      omega
    . clear *-h_bus_wellformedness h_row h_is_valid h_opcode h_a0 h_a1 h_a2 h_a3 h_constraints h_non_imm
      simp [SrlInput_of_Shift_instruction_fields, PureSpec.execute_RTYPE_srl_pure]
      have h_rd : ¬(wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0) ∧ (get_instruction_fields_row air row).rd_ptr < 32  := by
        clear *-h_bus_wellformedness h_row h_is_valid h_opcode
        specialize h_bus_wellformedness row h_row
        unfold VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
        simp [
          VmAirWrapper_shift_constraint_and_interaction_simplification,
          VmAirWrapper_shift.constraints.propertiesToAssume,
          Interaction.ReadInstructionBusEntry.operand_properties,
          h_is_valid
        ] at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.1
        simp [wrap_to_regidx, get_instruction_fields_row]
        replace h_bus_wellformedness := (h_bus_wellformedness (by omega) (by omega)).1
        omega
      obtain ⟨h_rd_non_zero, h_rd_lt_32⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_lt_32
      replace h_rd_lt_32 := Fin.val_fin_lt.mpr h_rd_lt_32
      simp at h_rd_lt_32
      simp [
        true_and,
        h_a0,
        h_a1,
        h_a2,
        h_a3,
        wrap_to_regidx,
        h_rd_lt_32
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_lt_32

      have h_spec := Shift.ValidRows.spec_base_Shift_non_imm
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
        h_non_imm

      simp only [
        h_opcode, Shift.ValidRows.rop_of_Shift_opcode, execute_RTYPE_pure
      ] at h_spec
      dsimp at h_spec

      convert h_spec
      simp
      congr

  lemma sra_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
  :
    ((get_instruction_fields_row air row).opcode = 519 →
      SraOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
        (PureSpec.execute_RTYPE_sra_pure
          (SraInput_of_Shift_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SraOutput_matches_Shift_instruction_fields]
    have ⟨
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties,
        h_bit_multiplier_left,
        h_bit_multiplier_right,
        h_bit_shift_carry_0,
        h_bit_shift_carry_1,
        h_bit_shift_carry_2,
        h_bit_shift_carry_3
      ⟩:= Shift.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
    split_ands
    . clear *- h_row h_constraints h_opcode h_is_valid
      have := VmAirWrapper_shift.constraints.single_op
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      have := VmAirWrapper_shift.constraints.op_from_opcode
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      simp [get_instruction_fields_row]
      grind
    . clear *-h_b0
      simp [get_instruction_fields_row, h_b0]
    . clear *-h_b1
      simp [get_instruction_fields_row, h_b1]
    . clear *-h_b2
      simp [get_instruction_fields_row, h_b2]
    . clear *-h_b3
      simp [get_instruction_fields_row, h_b3]
    . clear *-h_c0
      simp [get_instruction_fields_row, h_c0]
    . clear *-h_c1
      simp [get_instruction_fields_row, h_c1]
    . clear *-h_c2
      simp [get_instruction_fields_row, h_c2]
    . clear *-h_c3
      simp [List.Forall] at h_c3
      simp [get_instruction_fields_row, h_c3]
    . clear *-h_bus_assumptions h_row h_is_valid
      simp [PureSpec.execute_RTYPE_sra_pure, SraInput_of_Shift_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      simp [
        VmAirWrapper_shift.constraints.assumptionsPerRow,
        VmAirWrapper_shift_constraint_and_interaction_simplification
      ] at h_bus_assumptions
      replace h_bus_assumptions := h_bus_assumptions.1
      simp [VmAirWrapper_shift.constraints.assumptions, h_is_valid] at h_bus_assumptions
      omega
    . clear *-h_bus_wellformedness h_row h_is_valid h_opcode h_a0 h_a1 h_a2 h_a3 h_constraints h_non_imm
      simp [SraInput_of_Shift_instruction_fields, PureSpec.execute_RTYPE_sra_pure]
      have h_rd : ¬(wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0) ∧ (get_instruction_fields_row air row).rd_ptr < 32  := by
        clear *-h_bus_wellformedness h_row h_is_valid h_opcode
        specialize h_bus_wellformedness row h_row
        unfold VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
        simp [
          VmAirWrapper_shift_constraint_and_interaction_simplification,
          VmAirWrapper_shift.constraints.propertiesToAssume,
          Interaction.ReadInstructionBusEntry.operand_properties,
          h_is_valid
        ] at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.1
        simp [wrap_to_regidx, get_instruction_fields_row]
        replace h_bus_wellformedness := (h_bus_wellformedness (by omega) (by omega)).1
        omega
      obtain ⟨h_rd_non_zero, h_rd_lt_32⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_lt_32
      replace h_rd_lt_32 := Fin.val_fin_lt.mpr h_rd_lt_32
      simp at h_rd_lt_32
      simp [
        true_and,
        h_a0,
        h_a1,
        h_a2,
        h_a3,
        wrap_to_regidx,
        h_rd_lt_32
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_lt_32

      have h_spec := Shift.ValidRows.spec_base_Shift_non_imm
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
        h_non_imm

      simp only [
        h_opcode, Shift.ValidRows.rop_of_Shift_opcode, execute_RTYPE_pure
      ] at h_spec
      dsimp at h_spec

      convert h_spec
      simp
      congr

  lemma slli_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
  :
    ((get_instruction_fields_row air row).opcode = 517 →
      SlliOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
        (PureSpec.execute_SHIFTIOP_slli_pure
          (SlliInput_of_Shift_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SlliOutput_matches_Shift_instruction_fields]
    have ⟨
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties,
        h_bit_multiplier_left,
        h_bit_multiplier_right,
        h_bit_shift_carry_0,
        h_bit_shift_carry_1,
        h_bit_shift_carry_2,
        h_bit_shift_carry_3
      ⟩:= Shift.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
    split_ands
    . clear *- h_row h_constraints h_opcode h_is_valid
      have := VmAirWrapper_shift.constraints.single_op
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      have := VmAirWrapper_shift.constraints.op_from_opcode
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      simp [get_instruction_fields_row]
      grind
    . clear *-h_b0
      simp [get_instruction_fields_row, h_b0]
    . clear *-h_b1
      simp [get_instruction_fields_row, h_b1]
    . clear *-h_b2
      simp [get_instruction_fields_row, h_b2]
    . clear *-h_b3
      simp [get_instruction_fields_row, h_b3]
    . clear *-h_bus_assumptions h_row h_is_valid
      simp [PureSpec.execute_SHIFTIOP_slli_pure, SlliInput_of_Shift_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      simp [
        VmAirWrapper_shift.constraints.assumptionsPerRow,
        VmAirWrapper_shift_constraint_and_interaction_simplification
      ] at h_bus_assumptions
      replace h_bus_assumptions := h_bus_assumptions.1
      simp [VmAirWrapper_shift.constraints.assumptions, h_is_valid] at h_bus_assumptions
      omega
    . clear *-h_bus_wellformedness h_row h_is_valid h_opcode h_a0 h_a1 h_a2 h_a3 h_constraints h_imm h_imm_op_properties
      replace h_imm_op_properties := (h_imm_op_properties h_imm).2.1
      simp [SlliInput_of_Shift_instruction_fields, PureSpec.execute_SHIFTIOP_slli_pure]
      have h_rd : ¬(wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0) ∧ (get_instruction_fields_row air row).rd_ptr < 32  := by
        clear *-h_bus_wellformedness h_row h_is_valid h_opcode
        specialize h_bus_wellformedness row h_row
        unfold VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
        simp [
          VmAirWrapper_shift_constraint_and_interaction_simplification,
          VmAirWrapper_shift.constraints.propertiesToAssume,
          Interaction.ReadInstructionBusEntry.operand_properties,
          h_is_valid
        ] at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.1
        simp [wrap_to_regidx, get_instruction_fields_row]
        replace h_bus_wellformedness := (h_bus_wellformedness (by omega) (by omega)).1
        omega
      obtain ⟨h_rd_non_zero, h_rd_lt_32⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_lt_32
      replace h_rd_lt_32 := Fin.val_fin_lt.mpr h_rd_lt_32
      simp at h_rd_lt_32
      simp [
        true_and,
        h_a0,
        h_a1,
        h_a2,
        h_a3,
        wrap_to_regidx,
        h_rd_lt_32
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_lt_32

      have h_spec := Shift.ValidRows.spec_base_Shift_imm
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
        h_imm

      simp only [
        h_opcode, Shift.ValidRows.iop_of_Shift_opcode, execute_SHIFTIOP_pure,
        execute_RTYPE_pure
      ] at h_spec
      dsimp at h_spec

      convert h_spec
      grind

  lemma srli_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
  :
    ((get_instruction_fields_row air row).opcode = 518 →
      SrliOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
        (PureSpec.execute_SHIFTIOP_srli_pure
          (SrliInput_of_Shift_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SrliOutput_matches_Shift_instruction_fields]
    have ⟨
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties,
        h_bit_multiplier_left,
        h_bit_multiplier_right,
        h_bit_shift_carry_0,
        h_bit_shift_carry_1,
        h_bit_shift_carry_2,
        h_bit_shift_carry_3
      ⟩:= Shift.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
    split_ands
    . clear *- h_row h_constraints h_opcode h_is_valid
      have := VmAirWrapper_shift.constraints.single_op
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      have := VmAirWrapper_shift.constraints.op_from_opcode
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      simp [get_instruction_fields_row]
      grind
    . clear *-h_b0
      simp [get_instruction_fields_row, h_b0]
    . clear *-h_b1
      simp [get_instruction_fields_row, h_b1]
    . clear *-h_b2
      simp [get_instruction_fields_row, h_b2]
    . clear *-h_b3
      simp [get_instruction_fields_row, h_b3]
    . clear *-h_bus_assumptions h_row h_is_valid
      simp [PureSpec.execute_SHIFTIOP_srli_pure, SrliInput_of_Shift_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      simp [
        VmAirWrapper_shift.constraints.assumptionsPerRow,
        VmAirWrapper_shift_constraint_and_interaction_simplification
      ] at h_bus_assumptions
      replace h_bus_assumptions := h_bus_assumptions.1
      simp [VmAirWrapper_shift.constraints.assumptions, h_is_valid] at h_bus_assumptions
      omega
    . clear *-h_bus_wellformedness h_row h_is_valid h_opcode h_a0 h_a1 h_a2 h_a3 h_constraints h_imm h_imm_op_properties
      replace h_imm_op_properties := (h_imm_op_properties h_imm).2.1
      simp [SrliInput_of_Shift_instruction_fields, PureSpec.execute_SHIFTIOP_srli_pure]
      have h_rd : ¬(wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0) ∧ (get_instruction_fields_row air row).rd_ptr < 32  := by
        clear *-h_bus_wellformedness h_row h_is_valid h_opcode
        specialize h_bus_wellformedness row h_row
        unfold VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
        simp [
          VmAirWrapper_shift_constraint_and_interaction_simplification,
          VmAirWrapper_shift.constraints.propertiesToAssume,
          Interaction.ReadInstructionBusEntry.operand_properties,
          h_is_valid
        ] at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.1
        simp [wrap_to_regidx, get_instruction_fields_row]
        replace h_bus_wellformedness := (h_bus_wellformedness (by omega) (by omega)).1
        omega
      obtain ⟨h_rd_non_zero, h_rd_lt_32⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_lt_32
      replace h_rd_lt_32 := Fin.val_fin_lt.mpr h_rd_lt_32
      simp at h_rd_lt_32
      simp [
        true_and,
        h_a0,
        h_a1,
        h_a2,
        h_a3,
        wrap_to_regidx,
        h_rd_lt_32
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_lt_32

      have h_spec := Shift.ValidRows.spec_base_Shift_imm
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
        h_imm

      simp only [
        h_opcode, Shift.ValidRows.iop_of_Shift_opcode, execute_SHIFTIOP_pure,
        execute_RTYPE_pure
      ] at h_spec
      dsimp at h_spec

      convert h_spec
      grind

  lemma srai_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
  :
    ((get_instruction_fields_row air row).opcode = 519 →
      SraiOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
        (PureSpec.execute_SHIFTIOP_srai_pure
          (SraiInput_of_Shift_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SraiOutput_matches_Shift_instruction_fields]
    have ⟨
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties,
        h_bit_multiplier_left,
        h_bit_multiplier_right,
        h_bit_shift_carry_0,
        h_bit_shift_carry_1,
        h_bit_shift_carry_2,
        h_bit_shift_carry_3
      ⟩:= Shift.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
    split_ands
    . clear *- h_row h_constraints h_opcode h_is_valid
      have := VmAirWrapper_shift.constraints.single_op
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      have := VmAirWrapper_shift.constraints.op_from_opcode
        air
        row h_row
        (h_constraints ⟨row, by omega⟩)
      simp [get_instruction_fields_row]
      grind
    . clear *-h_b0
      simp [get_instruction_fields_row, h_b0]
    . clear *-h_b1
      simp [get_instruction_fields_row, h_b1]
    . clear *-h_b2
      simp [get_instruction_fields_row, h_b2]
    . clear *-h_b3
      simp [get_instruction_fields_row, h_b3]
    . clear *-h_bus_assumptions h_row h_is_valid
      simp [PureSpec.execute_SHIFTIOP_srai_pure, SraiInput_of_Shift_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      simp [
        VmAirWrapper_shift.constraints.assumptionsPerRow,
        VmAirWrapper_shift_constraint_and_interaction_simplification
      ] at h_bus_assumptions
      replace h_bus_assumptions := h_bus_assumptions.1
      simp [VmAirWrapper_shift.constraints.assumptions, h_is_valid] at h_bus_assumptions
      omega
    . clear *-h_bus_wellformedness h_row h_is_valid h_opcode h_a0 h_a1 h_a2 h_a3 h_constraints h_imm h_imm_op_properties
      replace h_imm_op_properties := (h_imm_op_properties h_imm).2.1
      simp [SraiInput_of_Shift_instruction_fields, PureSpec.execute_SHIFTIOP_srai_pure]
      have h_rd : ¬(wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0) ∧ (get_instruction_fields_row air row).rd_ptr < 32  := by
        clear *-h_bus_wellformedness h_row h_is_valid h_opcode
        specialize h_bus_wellformedness row h_row
        unfold VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
        simp [
          VmAirWrapper_shift_constraint_and_interaction_simplification,
          VmAirWrapper_shift.constraints.propertiesToAssume,
          Interaction.ReadInstructionBusEntry.operand_properties,
          h_is_valid
        ] at h_bus_wellformedness
        replace h_bus_wellformedness := h_bus_wellformedness.1
        simp [wrap_to_regidx, get_instruction_fields_row]
        replace h_bus_wellformedness := (h_bus_wellformedness (by omega) (by omega)).1
        omega
      obtain ⟨h_rd_non_zero, h_rd_lt_32⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_lt_32
      replace h_rd_lt_32 := Fin.val_fin_lt.mpr h_rd_lt_32
      simp at h_rd_lt_32
      simp [
        true_and,
        h_a0,
        h_a1,
        h_a2,
        h_a3,
        wrap_to_regidx,
        h_rd_lt_32
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_lt_32

      have h_spec := Shift.ValidRows.spec_base_Shift_imm
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))
        h_imm

      simp only [
        h_opcode, Shift.ValidRows.iop_of_Shift_opcode, execute_SHIFTIOP_pure,
        execute_RTYPE_pure
      ] at h_spec
      dsimp at h_spec

      convert h_spec
      grind


  lemma non_imm_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).non_imm = 1 →
    ((get_instruction_fields_row air row).opcode = 517 →
        SllOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_sll_pure
            (SllInput_of_Shift_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 518 →
          SrlOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_srl_pure
              (SrlInput_of_Shift_instruction_fields (get_instruction_fields_row air row)))) ∧
        ((get_instruction_fields_row air row).opcode = 519 →
          SraOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_sra_pure
              (SraInput_of_Shift_instruction_fields (get_instruction_fields_row air row)))))
  := by
    intro h_non_imm
    simp [get_instruction_fields_row] at h_non_imm

    exact ⟨
      sll_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_non_imm,
      ⟨
        srl_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_non_imm,
        sra_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_non_imm
      ⟩
    ⟩

  lemma imm_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).non_imm = 0 →
    ((get_instruction_fields_row air row).opcode = 517 →
        SlliOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_SHIFTIOP_slli_pure
            (SlliInput_of_Shift_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 518 →
          SrliOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_SHIFTIOP_srli_pure
              (SrliInput_of_Shift_instruction_fields (get_instruction_fields_row air row)))) ∧
        ((get_instruction_fields_row air row).opcode = 519 →
          SraiOutput_matches_Shift_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_SHIFTIOP_srai_pure
              (SraiInput_of_Shift_instruction_fields (get_instruction_fields_row air row)))))
  := by
    intro h_imm
    simp [get_instruction_fields_row] at h_imm

    exact ⟨
      slli_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_imm,
      ⟨
        srli_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_imm,
        srai_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_imm
      ⟩
    ⟩

  lemma spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
  :
    List.Forall Shift_instruction_fields.spec (get_instruction_fields air)
  := by
    apply List.forall_iff_forall_mem.mpr
    intro instruction_fields h_instruction_fields
    unfold Shift_instruction_fields.spec

    intro h_is_valid

    simp [get_instruction_fields] at h_instruction_fields
    obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
    rewrite [←h_fields] at ⊢ h_is_valid; clear h_fields

    simp [get_instruction_fields_row] at h_is_valid

    exact ⟨
      get_instruction_fields_row_non_imm_binary air row (by omega) h_constraints h_is_valid h_bus_wellformedness,
      ⟨
        get_instruction_fields_row_opcode_range air row (by omega) h_constraints h_is_valid h_bus_wellformedness,
        ⟨
          non_imm_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness,
          imm_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness
        ⟩
      ⟩
    ⟩

  theorem shift_spec [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List Shift_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall Shift_instruction_fields.spec
  := by
    use get_instruction_fields air
    simp only [
      bus_from_instruction_fields_eq_air_buses air h_constraints,
      spec_of_get_instruction_fields air h_constraints h_bus_assumptions h_bus_wellformedness
    ]
    trivial

  lemma List.append_eq_append_split
    {T : Type}
    {a b c d : List T}
    (h_eq : a ++ b = c ++ d)
    (h_len_ab : a.length = c.length)
  :
    a = c ∧ b = d
  := by
    induction a generalizing b c d
    case nil => simp_all
    case cons a₀ a ih =>
      cases c
      case nil => grind
      case cons c₀ c =>
        simp_all
        apply ih <;> grind

  lemma List.flatMap_eq_flatMap
    {A B C : Type}
    {f : A → List C}
    {g : B → List C}
    {lf : List A}
    {lg : List B}
    (h_eq_fmap : List.flatMap f lf = List.flatMap g lg)
    (h_eq_len : lf.length = lg.length)
    (h_eq_len_fg : forall a b, (f a).length = (g b).length)
    (idx : ℕ)
    (h_idx : idx < lf.length)
  :
    f lf[idx] = g lg[idx]
  := by
    induction lf generalizing idx lg
    case nil => grind
    case cons f₀ lf ih =>
      cases lg
      case nil => grind
      case cons g₀ lg =>
        simp_all
        have h_eq'
        :
          List.flatMap f lf = List.flatMap g lg
        := by
          apply append_eq_append_split (h_len_ab := h_eq_len_fg f₀ g₀) at h_eq_fmap
          tauto
        cases idx
        case zero => simp_all
        case succ idx =>
          specialize @ih lg h_eq' (by grind)
          grind

  theorem shift_spec_completeness [Field ExtF]
    (air : Valid_VmAirWrapper_shift FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_shift.constraints.wf_propertiesToAssumePerRow air row)
    (instruction_fields_list : List Shift_instruction_fields)
    (h_buses : air.buses = bus_from_instruction_fields instruction_fields_list)
    (h_specs : instruction_fields_list.Forall Shift_instruction_fields.spec)
  :
    instruction_fields_list = get_instruction_fields air
  := by
    -- The two lists have equal lengths
    have h_len_eq
    :
      instruction_fields_list.length = (get_instruction_fields air).length
    := by
      simp [get_instruction_fields]
      unfold bus_from_instruction_fields at h_buses
      have h_interactions := VmAirWrapper_shift.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
      unfold VmAirWrapper_shift.constraints.constrain_interactions at h_interactions
      rewrite [h_interactions] at h_buses; clear h_interactions
      suffices h_eq_len :
        List.length (List.flatMap (VmAirWrapper_shift.constraints.executionBus_row air) (List.range (air.last_row + 1))) =
        List.length (List.flatMap Shift_instruction_fields.execution instruction_fields_list)
      . unfold VmAirWrapper_shift.constraints.executionBus_row
               Shift_instruction_fields.execution
          at h_eq_len
        simp at h_eq_len; omega
      . have := congrFun h_buses ExecutionBus
        simp_all

    -- and this length is `air.last_row + 1`
    have h_len_eq_ifl
    :
      instruction_fields_list.length = air.last_row + 1
    := by
      simp [h_len_eq, get_instruction_fields]

    -- then show all elements are equal
    apply List.ext_get h_len_eq
    intro row h₁ h₂
    apply Shift_instruction_fields_eq
    simp only [get_instruction_fields,
               get_instruction_fields_row,
               List.get_eq_getElem,
               List.getElem_map,
               List.getElem_range,
              Fin.isValue]

    -- Prepare buses
    unfold bus_from_instruction_fields at h_buses
    have h_interactions := VmAirWrapper_shift.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_shift.constraints.constrain_interactions at h_interactions
    rewrite [h_interactions] at h_buses; clear h_interactions

    -- Match from Execution bus
    have h_exec := congrFun h_buses ExecutionBus
    unfold VmAirWrapper_shift.constraints.executionBus_row
           Shift_instruction_fields.execution
      at h_exec
    simp at h_exec
    have h_eq_exec :=
      List.flatMap_eq_flatMap
        h_exec
        (by grind)
        (by simp)
        row
        (by grind)
    simp [and_assoc] at h_eq_exec
    obtain ⟨ h0, h1, h2, h3, h4, h5 ⟩ := h_eq_exec
    symm at h0 h1 h2 h3 h4 h5

    -- Match from ReadInstruction bus
    have h_read := congrFun h_buses ReadInstructionBus
    unfold VmAirWrapper_shift.constraints.readInstructionBus_row
           Shift_instruction_fields.read_instruction
      at h_read
    simp at h_read
    have h_eq_read :=
      List.flatMap_eq_flatMap
        h_read
        (by grind)
        (by simp)
        row
        (by grind)
    simp at h_eq_read
    obtain ⟨ h6, h7, h8, h9, h10, h11, h12 ⟩ := h_eq_read
    symm at h6 h7 h8 h9 h10 h11 h12

    -- Match from Memory bus
    have h_mem := congrFun h_buses MemoryBus
    unfold VmAirWrapper_shift.constraints.memoryBus_row
           Shift_instruction_fields.memory
      at h_mem
    simp at h_mem
    have h_eq_mem :=
      List.flatMap_eq_flatMap
        h_mem
        (by grind)
        (by simp)
        row
        (by grind)
    simp [and_assoc] at h_eq_mem
    obtain ⟨ h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
             h23, h24, h25, h26, h27, h28, h29, h30, h31, h32,
             h33, h34, h35, h36, h37, h38, h39, h40, h41, h42,
             h43, h44, h45, h46, h47, h48, h49, h50, h51, h52,
             h53, h54, h55 ⟩ := h_eq_mem
    symm at h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
            h23 h24 h25 h26 h27 h28 h29 h30 h31 h32
            h33 h34 h35 h36 h37 h38 h39 h40 h41 h42
            h43 h44 h45 h46 h47 h48 h49 h50 h51 h52
            h53 h54 h55

    -- Match from RangeChecker bus
    have h_range := congrFun h_buses RangeCheckerBus
    unfold VmAirWrapper_shift.constraints.rangeCheckerBus_row
          Shift_instruction_fields.range_checks
      at h_range
    simp at h_range
    have h_eq_range :=
      List.flatMap_eq_flatMap
        h_range
        (by grind)
        (by simp)
        row
        (by grind)
    simp [and_assoc] at h_eq_range
    obtain ⟨ h56, h57, h58, h59, h60, h61, h62, h63, h64, h65,
            h66, h67, h68, h69, h70, h71, h72, h73, h74, h75,
            h76, h77, h78, h79, h80, h81, h82, h83, h84, h85,
            h86, h87, h88 ⟩ := h_eq_range
    symm at h56 h57 h58 h59 h60 h61 h62 h63 h64 h65
            h66 h67 h68 h69 h70 h71 h72 h73 h74 h75
            h76 h77 h78 h79 h80 h81 h82 h83 h84 h85
            h86 h87 h88

    -- Match from Bitwise bus
    have h_bit := congrFun h_buses BitwiseBus
    unfold VmAirWrapper_shift.constraints.bitwiseBus_row
           Shift_instruction_fields.bitwise
      at h_bit
    simp at h_bit
    have h_eq_bit :=
      List.flatMap_eq_flatMap
        h_bit
        (by grind)
        (by simp)
        row
        (by grind)
    simp [and_assoc] at h_eq_bit
    obtain ⟨ h89, h90, h91, h92, h93, h94, h95, h96, h97, h98,
             h99, h100, h101, h102, h103, h104 ⟩ := h_eq_bit
    symm at h89 h90 h91 h92 h93 h94 h95 h97 h98 h99 h101 h102 h103

    split_ands <;> try assumption
    . ext i hi; interval_cases i <;> simp_all
    . ext i hi; interval_cases i <;> simp_all
    . ext i hi; interval_cases i <;> simp_all
    . ext i hi; interval_cases i <;> simp_all
    . ext i hi j hj
      interval_cases i <;> interval_cases j <;>
      simp [← Fin.ext_iff] <;> (try assumption) <;> simp [*]
    . ext i hi j hj
      interval_cases i <;> interval_cases j <;>
      simp [← Fin.ext_iff] <;> (try assumption); simp [*]

end Equivalence.Shift
