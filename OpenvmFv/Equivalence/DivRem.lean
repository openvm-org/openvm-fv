import OpenvmFv.Spec.DivRem

import OpenvmFv.Spec.DIVREM.div
import OpenvmFv.Spec.DIVREM.divu
import OpenvmFv.Spec.DIVREM.rem
import OpenvmFv.Spec.DIVREM.remu

namespace Equivalence.DivRem

  @[ext]
  structure DIVREM_instruction_fields where
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

    signed : FBB
    special_case : FBB

    range_checked_vals : Vector FBB 6
    bitwise_vals : Vector (Vector FBB 3) 2
    range_checked_tuples : Vector (Vector FBB 2) 8

  lemma DIVREM_instruction_fields_eq (a b : DIVREM_instruction_fields)
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
    a.signed = b.signed ∧
    a.special_case = b.special_case ∧
    a.range_checked_vals = b.range_checked_vals ∧
    a.bitwise_vals = b.bitwise_vals ∧
    a.range_checked_tuples = b.range_checked_tuples
      → a = b
  := by
    intro field_eq
    ext <;> grind

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val / 4 % 32, by grind⟩

  def DivInput_of_DIVREM_instruction_fields (row : DIVREM_instruction_fields) : PureSpec.DivInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.DivInput
  }

  def DivuInput_of_DIVREM_instruction_fields (row : DIVREM_instruction_fields) : PureSpec.DivuInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.DivuInput
  }

  def RemInput_of_DIVREM_instruction_fields (row : DIVREM_instruction_fields) : PureSpec.RemInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.RemInput
  }

  def RemuInput_of_DIVREM_instruction_fields (row : DIVREM_instruction_fields) : PureSpec.RemuInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.RemuInput
  }

  def DivOutput_matches_DIVREM_instruction_fields (row : DIVREM_instruction_fields) (div_output : PureSpec.DivOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    div_output.nextPC = row.next_pc.toNat ∧
    match div_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def DivuOutput_matches_DIVREM_instruction_fields (row : DIVREM_instruction_fields) (divu_output : PureSpec.DivuOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    divu_output.nextPC = row.next_pc.toNat ∧
    match divu_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def RemOutput_matches_DIVREM_instruction_fields (row : DIVREM_instruction_fields) (rem_output : PureSpec.RemOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    rem_output.nextPC = row.next_pc.toNat ∧
    match rem_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def RemuOutput_matches_DIVREM_instruction_fields (row : DIVREM_instruction_fields) (remu_output : PureSpec.RemuOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    remu_output.nextPC = row.next_pc.toNat ∧
    match remu_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def DIVREM_instruction_fields.spec (row : DIVREM_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode ∈ Finset.Icc 596 599 ∧
      (row.opcode = 596 →
        DivOutput_matches_DIVREM_instruction_fields
          row
          (PureSpec.execute_DIVREM_div_pure (DivInput_of_DIVREM_instruction_fields row))
      ) ∧
      (row.opcode = 597 →
        DivuOutput_matches_DIVREM_instruction_fields
          row
          (PureSpec.execute_DIVREM_divu_pure (DivuInput_of_DIVREM_instruction_fields row))
      ) ∧
      (row.opcode = 598 →
        RemOutput_matches_DIVREM_instruction_fields
          row
          (PureSpec.execute_DIVREM_rem_pure (RemInput_of_DIVREM_instruction_fields row))
      ) ∧
      (row.opcode = 599 →
        RemuOutput_matches_DIVREM_instruction_fields
          row
          (PureSpec.execute_DIVREM_remu_pure (RemuInput_of_DIVREM_instruction_fields row))
      )
    )

  def DIVREM_instruction_fields.execution (row : DIVREM_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def DIVREM_instruction_fields.memory (row : DIVREM_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.prev_b_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.b_timestamp]),
    (-row.is_valid, [1, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.prev_c_timestamp]),
    ( row.is_valid, [1, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.c_timestamp]),
    (-row.is_valid, [1, row.rd_ptr, row.prev_a[0], row.prev_a[1], row.prev_a[2], row.prev_a[3], row.prev_a_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.a_timestamp]),
  ]

  def DIVREM_instruction_fields.range_checks (row : DIVREM_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
    (row.is_valid, [row.range_checked_vals[2], 17]),
    (row.is_valid, [row.range_checked_vals[3], 12]),
    (row.is_valid, [row.range_checked_vals[4], 17]),
    (row.is_valid, [row.range_checked_vals[5], 12]),
  ]

  def DIVREM_instruction_fields.read_instruction (row : DIVREM_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, row.rs1_ptr, row.rs2_ptr, 1, 0, 0, 0])
  ]

  def DIVREM_instruction_fields.bitwise (row : DIVREM_instruction_fields) : List (FBB × List FBB) := [
    (row.signed, [row.bitwise_vals[0][0], row.bitwise_vals[0][1], row.bitwise_vals[0][2], 0]),
    (row.is_valid - row.special_case, [row.bitwise_vals[1][0], row.bitwise_vals[1][1], row.bitwise_vals[1][2], 0])
  ]

  def DIVREM_instruction_fields.range_check_tuples (row : DIVREM_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_tuples[0][0], row.range_checked_tuples[0][1]]),
    (row.is_valid, [row.range_checked_tuples[1][0], row.range_checked_tuples[1][1]]),
    (row.is_valid, [row.range_checked_tuples[2][0], row.range_checked_tuples[2][1]]),
    (row.is_valid, [row.range_checked_tuples[3][0], row.range_checked_tuples[3][1]]),
    (row.is_valid, [row.range_checked_tuples[4][0], row.range_checked_tuples[4][1]]),
    (row.is_valid, [row.range_checked_tuples[5][0], row.range_checked_tuples[5][1]]),
    (row.is_valid, [row.range_checked_tuples[6][0], row.range_checked_tuples[6][1]]),
    (row.is_valid, [row.range_checked_tuples[7][0], row.range_checked_tuples[7][1]])
  ]

  def bus_from_instruction_fields (rows : List DIVREM_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then              rows.flatMap DIVREM_instruction_fields.execution
      else if index = MemoryBus then            rows.flatMap DIVREM_instruction_fields.memory
      else if index = RangeCheckerBus then      rows.flatMap DIVREM_instruction_fields.range_checks
      else if index = ReadInstructionBus then   rows.flatMap DIVREM_instruction_fields.read_instruction
      else if index = BitwiseBus then           rows.flatMap DIVREM_instruction_fields.bitwise
      else if index = RangeTupleCheckerBus then rows.flatMap DIVREM_instruction_fields.range_check_tuples
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_divrem FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_divrem.constraints.allHold air row.1 (by grind)

  def get_instruction_fields_row (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ) : DIVREM_instruction_fields := {
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
    a := #v[air.core.a row 0 0, air.core.a row 0 1, air.core.a row 0 2, air.core.a row 0 3]
    b := #v[air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0]
    c := #v[air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0]
    signed := air.core.signed row 0
    special_case := air.core.special_case row 0
    range_checked_vals :=
      #v[air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0,
         air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0,
         air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0]
    bitwise_vals :=
      #v[
        #v[2 * (air.core.b_3 row 0 - air.core.b_sign row 0 * 128), 2 * (air.core.c_3 row 0 - air.core.c_sign row 0 * 128), 0],
        #v[air.core.lt_diff row 0 - 1, 0, 0]
      ]
    range_checked_tuples :=
      #v[
        #v[air.core.q_0 row 0, air.core.carry row 0 0],
        #v[air.core.q_1 row 0, air.core.carry row 0 1],
        #v[air.core.q_2 row 0, air.core.carry row 0 2],
        #v[air.core.q_3 row 0, air.core.carry row 0 3],
        #v[air.core.r_0 row 0, air.core.carry_ext row 0 0],
        #v[air.core.r_1 row 0, air.core.carry_ext row 0 1],
        #v[air.core.r_2 row 0, air.core.carry_ext row 0 2],
        #v[air.core.r_3 row 0, air.core.carry_ext row 0 3]]
    : DIVREM_instruction_fields
  }

  def get_instruction_fields (air : Valid_VmAirWrapper_divrem FBB ExtF) : List DIVREM_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma execution_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
  :
    List.flatMap (VmAirWrapper_divrem.constraints.executionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap DIVREM_instruction_fields.execution (get_instruction_fields air)
  := by
    unfold DIVREM_instruction_fields.execution
    unfold VmAirWrapper_divrem.constraints.executionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma memory_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
  :
    List.flatMap (VmAirWrapper_divrem.constraints.memoryBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap DIVREM_instruction_fields.memory (get_instruction_fields air)
  := by
    unfold DIVREM_instruction_fields.memory
    unfold VmAirWrapper_divrem.constraints.memoryBus_row
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      h_neg_one
    ]

  lemma range_checks_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
  :
    List.flatMap (VmAirWrapper_divrem.constraints.rangeCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap DIVREM_instruction_fields.range_checks (get_instruction_fields air)
  := by
    unfold DIVREM_instruction_fields.range_checks
    unfold VmAirWrapper_divrem.constraints.rangeCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma read_instruction_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
  :
    List.flatMap (VmAirWrapper_divrem.constraints.readInstructionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap DIVREM_instruction_fields.read_instruction (get_instruction_fields air)
  := by
    unfold DIVREM_instruction_fields.read_instruction
    unfold VmAirWrapper_divrem.constraints.readInstructionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      ← DivRemCoreAir_4_8.ctx_opcode_def
    ]
    have : forall {T T' : Type} {f g : T' → List T} (lx : List T'), f = g → (List.flatMap f lx = List.flatMap g lx)
      := by intro T T' f g lx eq; congr
    apply this
    funext n; simp; omega

  lemma bitwise_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
  :
    List.flatMap (VmAirWrapper_divrem.constraints.bitwiseBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap DIVREM_instruction_fields.bitwise (get_instruction_fields air)
  := by
    unfold DIVREM_instruction_fields.bitwise
    unfold VmAirWrapper_divrem.constraints.bitwiseBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      ← DivRemCoreAir_4_8.valid_and_not_special_case_def
    ]

  lemma range_check_tuples_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
  :
    List.flatMap (VmAirWrapper_divrem.constraints.rangeTupleCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap DIVREM_instruction_fields.range_check_tuples (get_instruction_fields air)
  := by
    unfold DIVREM_instruction_fields.range_check_tuples
    unfold VmAirWrapper_divrem.constraints.rangeTupleCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
    ]

  lemma bus_from_instruction_fields_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (h_constraints : allHold_allRows air)
  :
    air.buses = bus_from_instruction_fields (get_instruction_fields air)
  := by
    have h_interactions := VmAirWrapper_divrem.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_divrem.constraints.constrain_interactions at h_interactions
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
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
  :
    (get_instruction_fields_row air row).opcode ∈ Finset.Icc 596 599
  := by
    simp [get_instruction_fields_row]
    have :=
      VmAirWrapper_divrem.constraints.opcode_bounds
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
    grind

  lemma transpile_of_bus_wellformedness [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
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
    unfold VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
    simp [
      VmAirWrapper_divrem.constraints.propertiesToAssume,
      Interaction.ReadInstructionBusEntry.operand_properties,
      VmAirWrapper_divrem.constraints._readInstructionBus_row,
      VmAirWrapper_divrem.constraints.readInstructionBus_row,
      -List.map_nil, -Vector.toList_mk, -List.attach_cons
    ] at h_bus_wellformedness
    unfold Interaction.ReadInstructionBusEntry.deserialise at h_bus_wellformedness
    dsimp [List.attach] at h_bus_wellformedness
    rewrite [h_is_valid] at h_bus_wellformedness
    simp only [
      Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.cast_one, Fin.cast_val_eq_self,
      Nat.cast_zero, Interaction.ReadInstructionBusEntry.mk.injEq,
      forall_const
    ] at h_bus_wellformedness
    rw [← DivRemCoreAir_4_8.ctx_opcode_def]
    grind

  lemma div_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 596)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_cases := Transpiler.transpiler_opcode_596 h_transpile.1 h_transpile.2.2.2.1
    obtain ⟨rs2, rs1, rd, h_instruction, h_rd⟩ := h_cases
    rewrite [h_instruction] at h_transpile
    unfold Transpiler.transpile_op at h_transpile
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

  lemma divu_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 597)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_cases := Transpiler.transpiler_opcode_597 h_transpile.1 h_transpile.2.2.2.1
    obtain ⟨rs2, rs1, rd, h_instruction, h_rd⟩ := h_cases
    rewrite [h_instruction] at h_transpile
    unfold Transpiler.transpile_op at h_transpile
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

  lemma rem_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 598)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_cases := Transpiler.transpiler_opcode_598 h_transpile.1 h_transpile.2.2.2.1
    obtain ⟨rs2, rs1, rd, h_instruction, h_rd⟩ := h_cases
    rewrite [h_instruction] at h_transpile
    unfold Transpiler.transpile_op at h_transpile
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

  lemma remu_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 599)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_cases := Transpiler.transpiler_opcode_599 h_transpile.1 h_transpile.2.2.2.1
    obtain ⟨rs2, rs1, rd, h_instruction, h_rd⟩ := h_cases
    rewrite [h_instruction] at h_transpile
    unfold Transpiler.transpile_op at h_transpile
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

  lemma div_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 596 →
        DivOutput_matches_DIVREM_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_DIVREM_div_pure
            (DivInput_of_DIVREM_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [DivOutput_matches_DIVREM_instruction_fields]

    obtain ⟨
      h_pc,
      ub_a0, ub_a1, ub_a2, ub_a3,
      ub_b0, ub_b1, ub_b2, ub_b3,
      ub_c0, ub_c1, ub_c2, ub_c3,
      eq_a_div, eq_a_rem
    ⟩ :=
      DivRem.ValidRows.essentials
        ExtF air row h_row
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_assumptions row (by omega))
        (h_bus_wellformedness row (by omega))

    simp [get_instruction_fields_row, *]

    split_ands
    . clear *- h_bus_assumptions h_row h_is_valid h_pc
      simp [PureSpec.execute_DIVREM_div_pure, DivInput_of_DIVREM_instruction_fields]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . simp [DivInput_of_DIVREM_instruction_fields, PureSpec.execute_DIVREM_div_pure]
      have h_rd := div_rd_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind⟩ := h_rd
      simp [get_instruction_fields_row] at h_rd_non_zero h_rd_ind
      simp only [dite_cond_eq_false, h_rd_non_zero]
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind

      simp [h_opcode] at eq_a_div
      obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩ := eq_a_div

      split_ands
      . rw [← eq_a0]; assumption
      . rw [← eq_a1]; assumption
      . rw [← eq_a2]; assumption
      . rw [← eq_a3]; assumption
      . have := DivRem.ValidRows.spec_DIVREM
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_wellformedness row (by omega))
          (by clear *- h_opcode; left; assumption)
        trans (U32.toBV #v[BitVec.ofNat 8 (air.core.q_0 row 0).val, BitVec.ofNat 8 (air.core.q_1 row 0).val, BitVec.ofNat 8 (air.core.q_2 row 0).val,BitVec.ofNat 8 (air.core.q_3 row 0).val])
        . congr
        . simp at this; obtain ⟨ hq, hr ⟩ := this
          rw [hq]; congr
      . rw [h_rd_ind]
        simp [Transpiler.ind, regidx_to_fin, wrap_to_regidx]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma divu_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 597 →
        DivuOutput_matches_DIVREM_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_DIVREM_divu_pure
            (DivuInput_of_DIVREM_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [DivuOutput_matches_DIVREM_instruction_fields]

    obtain ⟨
      h_pc,
      ub_a0, ub_a1, ub_a2, ub_a3,
      ub_b0, ub_b1, ub_b2, ub_b3,
      ub_c0, ub_c1, ub_c2, ub_c3,
      eq_a_div, eq_a_rem
    ⟩ :=
      DivRem.ValidRows.essentials
        ExtF air row h_row
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_assumptions row (by omega))
        (h_bus_wellformedness row (by omega))

    simp [get_instruction_fields_row, *]

    split_ands
    . clear *- h_bus_assumptions h_row h_is_valid h_pc
      simp [PureSpec.execute_DIVREM_divu_pure, DivuInput_of_DIVREM_instruction_fields]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . simp [DivuInput_of_DIVREM_instruction_fields, PureSpec.execute_DIVREM_divu_pure]
      have h_rd := divu_rd_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind⟩ := h_rd
      simp [get_instruction_fields_row] at h_rd_non_zero h_rd_ind
      simp only [dite_cond_eq_false, h_rd_non_zero]
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind

      simp [h_opcode] at eq_a_div
      obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩ := eq_a_div

      split_ands
      . rw [← eq_a0]; assumption
      . rw [← eq_a1]; assumption
      . rw [← eq_a2]; assumption
      . rw [← eq_a3]; assumption
      . have := DivRem.ValidRows.spec_DIVUREMU
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_wellformedness row (by omega))
          (by clear *- h_opcode; left; assumption)
        trans (U32.toBV #v[BitVec.ofNat 8 (air.core.q_0 row 0).val, BitVec.ofNat 8 (air.core.q_1 row 0).val, BitVec.ofNat 8 (air.core.q_2 row 0).val,BitVec.ofNat 8 (air.core.q_3 row 0).val])
        . congr
        . simp at this; obtain ⟨ hq, hr ⟩ := this
          rw [hq]; congr
      . rw [h_rd_ind]
        simp [Transpiler.ind, regidx_to_fin, wrap_to_regidx]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma rem_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 598 →
        RemOutput_matches_DIVREM_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_DIVREM_rem_pure
            (RemInput_of_DIVREM_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [RemOutput_matches_DIVREM_instruction_fields]

    obtain ⟨
      h_pc,
      ub_a0, ub_a1, ub_a2, ub_a3,
      ub_b0, ub_b1, ub_b2, ub_b3,
      ub_c0, ub_c1, ub_c2, ub_c3,
      eq_a_div, eq_a_rem
    ⟩ :=
      DivRem.ValidRows.essentials
        ExtF air row h_row
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_assumptions row (by omega))
        (h_bus_wellformedness row (by omega))

    simp [get_instruction_fields_row, *]

    split_ands
    . clear *- h_bus_assumptions h_row h_is_valid h_pc
      simp [PureSpec.execute_DIVREM_rem_pure, RemInput_of_DIVREM_instruction_fields]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . simp [RemInput_of_DIVREM_instruction_fields, PureSpec.execute_DIVREM_rem_pure]
      have h_rd := rem_rd_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind⟩ := h_rd
      simp [get_instruction_fields_row] at h_rd_non_zero h_rd_ind
      simp only [dite_cond_eq_false, h_rd_non_zero]
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind

      simp [h_opcode] at eq_a_rem
      obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩ := eq_a_rem

      split_ands
      . rw [← eq_a0]; assumption
      . rw [← eq_a1]; assumption
      . rw [← eq_a2]; assumption
      . rw [← eq_a3]; assumption
      . have := DivRem.ValidRows.spec_DIVREM
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_wellformedness row (by omega))
          (by clear *- h_opcode; right; assumption)
        trans (U32.toBV #v[BitVec.ofNat 8 (air.core.r_0 row 0).val, BitVec.ofNat 8 (air.core.r_1 row 0).val, BitVec.ofNat 8 (air.core.r_2 row 0).val,BitVec.ofNat 8 (air.core.r_3 row 0).val])
        . congr
        . simp at this; obtain ⟨ hq, hr ⟩ := this
          rw [hr]; congr
      . rw [h_rd_ind]
        simp [Transpiler.ind, regidx_to_fin, wrap_to_regidx]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma remu_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 599 →
        RemuOutput_matches_DIVREM_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_DIVREM_remu_pure
            (RemuInput_of_DIVREM_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [RemuOutput_matches_DIVREM_instruction_fields]

    obtain ⟨
      h_pc,
      ub_a0, ub_a1, ub_a2, ub_a3,
      ub_b0, ub_b1, ub_b2, ub_b3,
      ub_c0, ub_c1, ub_c2, ub_c3,
      eq_a_div, eq_a_rem
    ⟩ :=
      DivRem.ValidRows.essentials
        ExtF air row h_row
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_assumptions row (by omega))
        (h_bus_wellformedness row (by omega))

    simp [get_instruction_fields_row, *]

    split_ands
    . clear *- h_bus_assumptions h_row h_is_valid h_pc
      simp [PureSpec.execute_DIVREM_remu_pure, RemuInput_of_DIVREM_instruction_fields]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . simp [RemuInput_of_DIVREM_instruction_fields, PureSpec.execute_DIVREM_remu_pure]
      have h_rd := remu_rd_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind⟩ := h_rd
      simp [get_instruction_fields_row] at h_rd_non_zero h_rd_ind
      simp only [dite_cond_eq_false, h_rd_non_zero]
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind

      simp [h_opcode] at eq_a_rem
      obtain ⟨ eq_a0, eq_a1, eq_a2, eq_a3 ⟩ := eq_a_rem

      split_ands
      . rw [← eq_a0]; assumption
      . rw [← eq_a1]; assumption
      . rw [← eq_a2]; assumption
      . rw [← eq_a3]; assumption
      . have := DivRem.ValidRows.spec_DIVUREMU
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_wellformedness row (by omega))
          (by clear *- h_opcode; right; assumption)
        trans (U32.toBV #v[BitVec.ofNat 8 (air.core.r_0 row 0).val, BitVec.ofNat 8 (air.core.r_1 row 0).val, BitVec.ofNat 8 (air.core.r_2 row 0).val,BitVec.ofNat 8 (air.core.r_3 row 0).val])
        . congr
        . simp at this; obtain ⟨ hq, hr ⟩ := this
          rw [hr]; congr
      . rw [h_rd_ind]
        simp [Transpiler.ind, regidx_to_fin, wrap_to_regidx]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_divrem FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_divrem.constraints.wf_propertiesToAssumePerRow air row)
  :
    List.Forall DIVREM_instruction_fields.spec (get_instruction_fields air)
  := by
    apply List.forall_iff_forall_mem.mpr
    intro instruction_fields h_instruction_fields
    unfold DIVREM_instruction_fields.spec

    intro h_is_valid

    simp [get_instruction_fields] at h_instruction_fields
    obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
    rewrite [←h_fields] at ⊢ h_is_valid; clear h_fields

    simp [get_instruction_fields_row] at h_is_valid
    split_ands
    . exact get_instruction_fields_row_opcode_range air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness
    . exact div_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness
    . exact divu_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness
    . exact rem_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness
    . exact remu_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness

end Equivalence.DivRem
