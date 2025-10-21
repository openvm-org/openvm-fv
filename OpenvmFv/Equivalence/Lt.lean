import OpenvmFv.Spec.Lt

import OpenvmFv.Spec.RTYPE.slt
import OpenvmFv.Spec.RTYPE.sltu

import OpenvmFv.Spec.ITYPE.slti
import OpenvmFv.Spec.ITYPE.sltiu


namespace Equivalence.Lt

  @[ext]
  structure Lt_instruction_fields where
    is_valid : FBB
    non_imm : FBB

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

    prefix_sum : FBB

    range_checked_vals : Vector FBB 6
    bitwise_vals : Vector (Vector FBB 3) 3

  lemma Lt_instruction_fields_eq (a b : Lt_instruction_fields)
  :
    a.is_valid = b.is_valid ∧
    a.non_imm = b.non_imm ∧
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
    a.prefix_sum = b.prefix_sum ∧
    a.range_checked_vals = b.range_checked_vals ∧
    a.bitwise_vals = b.bitwise_vals
      → a = b
  := by
    intro field_eq
    ext <;> grind

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val / 4 % 32, by grind⟩

  def SltInput_of_Lt_instruction_fields (row : Lt_instruction_fields) : PureSpec.SltInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SltInput
  }

  def SltiInput_of_Lt_instruction_fields (row : Lt_instruction_fields) : PureSpec.SltiInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 12 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SltiInput
  }

  def SltuInput_of_Lt_instruction_fields (row : Lt_instruction_fields) : PureSpec.SltuInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SltuInput
  }

  def SltiuInput_of_Lt_instruction_fields (row : Lt_instruction_fields) : PureSpec.SltiuInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 12 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SltiuInput
  }

  def SltOutput_matches_Lt_instruction_fields (row : Lt_instruction_fields) (sll_output : PureSpec.SltOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    sll_output.nextPC = row.next_pc.toNat ∧
    match sll_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def SltiOutput_matches_Lt_instruction_fields (row : Lt_instruction_fields) (slti_output : PureSpec.SltiOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    slti_output.nextPC = row.next_pc.toNat ∧
    match slti_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def SltuOutput_matches_Lt_instruction_fields (row : Lt_instruction_fields) (sltu_output : PureSpec.SltuOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    sltu_output.nextPC = row.next_pc.toNat ∧
    match sltu_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def SltiuOutput_matches_Lt_instruction_fields (row : Lt_instruction_fields) (sltiu_output : PureSpec.SltiuOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    sltiu_output.nextPC = row.next_pc.toNat ∧
    match sltiu_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def Lt_instruction_fields.spec (row : Lt_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      (row.non_imm = 0 ∨ row.non_imm = 1) ∧
      row.opcode ∈ Finset.Icc 520 521 ∧
      (row.non_imm = 1 → (
        (row.opcode = 520 →
          SltOutput_matches_Lt_instruction_fields
            row
            (PureSpec.execute_RTYPE_slt_pure (SltInput_of_Lt_instruction_fields row))
        ) ∧
        (row.opcode = 521 →
          SltuOutput_matches_Lt_instruction_fields
            row
            (PureSpec.execute_RTYPE_sltu_pure (SltuInput_of_Lt_instruction_fields row))
        )
      )) ∧
      (row.non_imm = 0 → (
        (row.opcode = 520 →
          SltiOutput_matches_Lt_instruction_fields
            row
            (PureSpec.execute_ITYPE_slti_pure (SltiInput_of_Lt_instruction_fields row))
        ) ∧
        (row.opcode = 521 →
          SltiuOutput_matches_Lt_instruction_fields
            row
            (PureSpec.execute_ITYPE_sltiu_pure (SltiuInput_of_Lt_instruction_fields row))
        )
      ))
    )

  def Lt_instruction_fields.execution (row : Lt_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def Lt_instruction_fields.memory (row : Lt_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.prev_b_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.b_timestamp]),
    (-row.non_imm, [row.non_imm, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.prev_c_timestamp]),
    ( row.non_imm, [row.non_imm, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.c_timestamp]),
    (-row.is_valid, [1, row.rd_ptr, row.prev_a[0], row.prev_a[1], row.prev_a[2], row.prev_a[3], row.prev_a_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.a_timestamp]),
  ]

  def Lt_instruction_fields.range_checks (row : Lt_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
    (row.non_imm, [row.range_checked_vals[2], 17]),
    (row.non_imm, [row.range_checked_vals[3], 12]),
    (row.is_valid, [row.range_checked_vals[4], 17]),
    (row.is_valid, [row.range_checked_vals[5], 12]),
  ]

  def Lt_instruction_fields.read_instruction (row : Lt_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, row.rs1_ptr, row.rs2_ptr, 1, row.non_imm, 0, 0])
  ]

  def Lt_instruction_fields.bitwise (row : Lt_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.bitwise_vals[0][0], row.bitwise_vals[0][1], row.bitwise_vals[0][2], 0]),
    (row.prefix_sum, [row.bitwise_vals[1][0], row.bitwise_vals[1][1], row.bitwise_vals[1][2], 0]),
    (row.is_valid - row.non_imm, [row.bitwise_vals[2][0], row.bitwise_vals[2][1], row.bitwise_vals[2][2], 0])
  ]

  def bus_from_instruction_fields (rows : List Lt_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then            rows.flatMap Lt_instruction_fields.execution
      else if index = MemoryBus then          rows.flatMap Lt_instruction_fields.memory
      else if index = RangeCheckerBus then    rows.flatMap Lt_instruction_fields.range_checks
      else if index = ReadInstructionBus then rows.flatMap Lt_instruction_fields.read_instruction
      else if index = BitwiseBus then         rows.flatMap Lt_instruction_fields.bitwise
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_lt FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_lt.constraints.allHold air row.1 (by grind)

  def get_instruction_fields_row (air : Valid_VmAirWrapper_lt FBB ExtF) (row : ℕ) : Lt_instruction_fields := {
    is_valid := air.core.is_valid row 0
    non_imm := air.adapter.rs2_as row 0
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
    rs2_ptr := air.adapter.rs2 row 0
    rd_ptr := air.adapter.rd_ptr row 0
    prev_a := #v[air.adapter.writes_aux.prev_data_0 row 0,
                  air.adapter.writes_aux.prev_data_1 row 0,
                  air.adapter.writes_aux.prev_data_2 row 0,
                  air.adapter.writes_aux.prev_data_3 row 0]
    a := #v[air.core.cmp_result row 0, 0, 0, 0]
    b := #v[air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0]
    c := #v[air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0]
    prefix_sum := air.core.prefix_sum row 0 0,
    range_checked_vals :=
      #v[air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0,
          air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0,
          air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0,
          air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0,
          air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0,
          air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0]
    bitwise_vals :=
      #v[
          #v[air.core.b_msb_f row 0 + 128 * air.core.opcode_slt_flag row 0, air.core.c_msb_f row 0 + 128 * air.core.opcode_slt_flag row 0, 0],
          #v[air.core.diff_val row 0 - 1, 0, 0],
          #v[air.core.c_0 row 0, air.core.c_1 row 0, 0]
      ]
    : Lt_instruction_fields
  }

  def get_instruction_fields (air : Valid_VmAirWrapper_lt FBB ExtF) : List Lt_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma execution_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
  :
    List.flatMap (VmAirWrapper_lt.constraints.executionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap Lt_instruction_fields.execution (get_instruction_fields air)
  := by
    unfold Lt_instruction_fields.execution
    unfold VmAirWrapper_lt.constraints.executionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma memory_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
  :
    List.flatMap (VmAirWrapper_lt.constraints.memoryBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap Lt_instruction_fields.memory (get_instruction_fields air)
  := by
    unfold Lt_instruction_fields.memory
    unfold VmAirWrapper_lt.constraints.memoryBus_row
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      h_neg_one
    ]

  lemma range_checks_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
  :
    List.flatMap (VmAirWrapper_lt.constraints.rangeCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap Lt_instruction_fields.range_checks (get_instruction_fields air)
  := by
    unfold Lt_instruction_fields.range_checks
    unfold VmAirWrapper_lt.constraints.rangeCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma read_instruction_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
  :
    List.flatMap (VmAirWrapper_lt.constraints.readInstructionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap Lt_instruction_fields.read_instruction (get_instruction_fields air)
  := by
    unfold Lt_instruction_fields.read_instruction
    unfold VmAirWrapper_lt.constraints.readInstructionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma bitwise_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
  :
    List.flatMap (VmAirWrapper_lt.constraints.bitwiseBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap Lt_instruction_fields.bitwise (get_instruction_fields air)
  := by
    unfold Lt_instruction_fields.bitwise
    unfold VmAirWrapper_lt.constraints.bitwiseBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma bus_from_instruction_fields_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (h_constraints : allHold_allRows air)
  :
    air.buses = bus_from_instruction_fields (get_instruction_fields air)
  := by
    have h_interactions := VmAirWrapper_lt.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_lt.constraints.constrain_interactions at h_interactions
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
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
  :
    (get_instruction_fields_row air row).non_imm = 0 ∨
    (get_instruction_fields_row air row).non_imm = 1
  := by
    simp [get_instruction_fields_row]
    have := Lt.ValidRows.essentials
      ExtF
      air
      row
      (by omega)
      (h_constraints ⟨row, by omega⟩)
      h_is_valid
      (h_bus_assumptions row (by omega))
      (h_bus_wellformedness row (by omega))

    exact this.2.2.2.1

  lemma get_instruction_fields_row_opcode_range [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
  :
    (get_instruction_fields_row air row).opcode ∈ Finset.Icc 520 521
  := by
    simp [get_instruction_fields_row]
    have := Lt.ValidRows.essentials
      ExtF
      air
      row
      (by omega)
      (h_constraints ⟨row, by omega⟩)
      h_is_valid
      (h_bus_assumptions row (by omega))
      (h_bus_wellformedness row (by omega))

    replace this := this.2.2.1
    grind

  lemma transpile_of_bus_wellformedness [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction a b,
    Transpiler.transpile_op instruction 1 (air.adapter.from_state.pc row 0) = some (a, b) ∧
      a = 1 ∧
        b[0] = air.adapter.from_state.pc row 0 ∧
          b[1] = (air.core.ctx row 0).instruction.opcode ∧
            b[2] = air.adapter.rd_ptr row 0 ∧
              b[3] = air.adapter.rs1_ptr row 0 ∧
                b[4] = air.adapter.rs2 row 0 ∧ b[5] = 1 ∧ b[6] = air.adapter.rs2_as row 0 ∧ b[7] = 0 ∧ b[8] = 0
  := by
    unfold VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
    simp [
      VmAirWrapper_lt.constraints.propertiesToAssume,
      Interaction.ReadInstructionBusEntry.operand_properties,
      VmAirWrapper_lt.constraints._readInstructionBus_row,
      VmAirWrapper_lt.constraints.readInstructionBus_row,
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
    exact h_bus_wellformedness

  lemma slt_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 520)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_cases := Transpiler.transpiler_opcode_520 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_slti =>
        exfalso
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_slti
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        rewrite [ite_cond_eq_true _ _ (eq_true h_pc_aligned)] at h_transpile
        dsimp at h_transpile
        split_ifs at h_transpile
        . have := Transpiler.extract_opcode h_transpile.1
          simp at this
          simp [this] at h_transpile
        . simp [-Vector.mk_eq] at h_transpile
          rewrite [h_non_imm] at h_transpile
          rewrite [←h_transpile.1.2] at h_transpile
          simp at h_transpile
      | inr h_slt =>
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_slt
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        rewrite [ite_cond_eq_true _ _ (eq_true h_pc_aligned)] at h_transpile
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

  lemma slt_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
  :
    ((get_instruction_fields_row air row).opcode = 520 →
        SltOutput_matches_Lt_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_slt_pure
            (SltInput_of_Lt_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SltOutput_matches_Lt_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_cmp_result,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= Lt.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_assumptions row (by omega))
        (h_bus_wellformedness row (by omega))
    split_ands
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
    . clear *-h_bus_assumptions h_row h_is_valid h_pc
      simp [PureSpec.execute_RTYPE_slt_pure, SltInput_of_Lt_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_cmp_result h_constraints h_non_imm
      simp [SltInput_of_Lt_instruction_fields, PureSpec.execute_RTYPE_slt_pure]
      have h_rd := slt_rd_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_non_imm
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_ind
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind
      simp [
        true_and,
        h_cmp_result,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_cmp_result h_rd_ind

      split_ands
      . have h_spec := Lt.ValidRows.spec_base_Lt_non_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row (by omega))
          (h_bus_wellformedness row (by omega))
          h_non_imm

        simp [
          Lt.ValidRows.rop_of_Lt_opcode, execute_RTYPE_pure,
          h_opcode
        ] at h_spec
        have (a) [Decidable a]:
          BitVec.setWidth 32 (if a then 1#1 else 0#1) =
          if a then 1#32 else 0#32
        := by
          by_cases a <;> simp [*]

        rewrite [this] at h_spec

        convert h_spec
        simp [BitVec.slt]
        have (a : FBB) (h) :
          @BitVec.ofFin 8 ⟨↑a % 256, h⟩ =
          BitVec.ofNat 8 ↑a
        := rfl
        simp [this]
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma sltu_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 521)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_cases := Transpiler.transpiler_opcode_521 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_sltiu =>
        exfalso
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_sltiu
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        rewrite [ite_cond_eq_true _ _ (eq_true h_pc_aligned)] at h_transpile
        dsimp at h_transpile
        split_ifs at h_transpile
        . have := Transpiler.extract_opcode h_transpile.1
          simp at this
          simp [this] at h_transpile
        . simp [-Vector.mk_eq] at h_transpile
          rewrite [h_non_imm] at h_transpile
          rewrite [←h_transpile.1.2] at h_transpile
          simp at h_transpile
      | inr h_sltu =>
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_sltu
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        rewrite [ite_cond_eq_true _ _ (eq_true h_pc_aligned)] at h_transpile
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

  lemma sltu_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
  :
    ((get_instruction_fields_row air row).opcode = 521 →
        SltuOutput_matches_Lt_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_sltu_pure
            (SltuInput_of_Lt_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SltuOutput_matches_Lt_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_cmp_result,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= Lt.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_assumptions row (by omega))
        (h_bus_wellformedness row (by omega))
    split_ands
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
    . clear *-h_bus_assumptions h_row h_is_valid h_pc
      simp [PureSpec.execute_RTYPE_sltu_pure, SltuInput_of_Lt_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_cmp_result h_constraints h_non_imm
      simp [SltuInput_of_Lt_instruction_fields, PureSpec.execute_RTYPE_sltu_pure]
      have h_rd := sltu_rd_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_non_imm
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_ind
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind
      simp [
        true_and,
        h_cmp_result,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_cmp_result h_rd_ind

      split_ands
      . have h_spec := Lt.ValidRows.spec_base_Lt_non_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row (by omega))
          (h_bus_wellformedness row (by omega))
          h_non_imm

        simp [
          Lt.ValidRows.rop_of_Lt_opcode, execute_RTYPE_pure,
          h_opcode
        ] at h_spec
        have (a) [Decidable a]:
          BitVec.setWidth 32 (if a then 1#1 else 0#1) =
          if a then 1#32 else 0#32
        := by
          by_cases a <;> simp [*]

        rewrite [this] at h_spec

        convert h_spec
        have (a : FBB) (h) :
          @BitVec.ofFin 8 ⟨↑a % 256, h⟩ =
          BitVec.ofNat 8 ↑a
        := rfl
        simp [this, BitVec.lt_def]
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma slti_register_properties [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 520)
  :
    ¬(wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0) ∧
    (∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd) ∧
    (∃ (imm: BitVec 12),
      (get_instruction_fields_row air row).rs2_ptr =
      Transpiler.utof (Transpiler.sign_extend_24 imm)
    )
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_cases := Transpiler.transpiler_opcode_520 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_slti =>
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_slti
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        rewrite [ite_cond_eq_true _ _ (eq_true h_pc_aligned)] at h_transpile
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
          . use imm
            obtain ⟨a, ⟨_, _, _, _, _, b, _, _, _⟩⟩ := h_transpile
            rewrite [←a.2] at b
            rewrite [←b]
            simp
      | inr h_slt =>
        exfalso
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_slt
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        rewrite [ite_cond_eq_true _ _ (eq_true h_pc_aligned)] at h_transpile
        dsimp at h_transpile
        split_ifs at h_transpile
        . have := Transpiler.extract_opcode h_transpile.1
          simp at this
          simp [this] at h_transpile
        . simp [-Vector.mk_eq] at h_transpile
          rewrite [h_imm] at h_transpile
          rewrite [←h_transpile.1.2] at h_transpile
          simp at h_transpile

  lemma slti_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
  :
    ((get_instruction_fields_row air row).opcode = 520 →
      SltiOutput_matches_Lt_instruction_fields (get_instruction_fields_row air row)
        (PureSpec.execute_ITYPE_slti_pure
          (SltiInput_of_Lt_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SltiOutput_matches_Lt_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_cmp_result,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= Lt.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_assumptions row (by omega))
        (h_bus_wellformedness row (by omega))
    split_ands
    . clear *-h_b0
      simp [get_instruction_fields_row, h_b0]
    . clear *-h_b1
      simp [get_instruction_fields_row, h_b1]
    . clear *-h_b2
      simp [get_instruction_fields_row, h_b2]
    . clear *-h_b3
      simp [get_instruction_fields_row, h_b3]
    . simp [get_instruction_fields_row]
      clear *-h_imm_op_properties h_imm
      specialize h_imm_op_properties h_imm
      refine BitVec.eq_of_toInt_eq ?_
      simp [BitVec.toInt_signExtend]
      refine (Int.bmod_eq_iff ?_).mpr ?_
      . trivial
      . grind
    . clear *-h_bus_assumptions h_row h_is_valid h_pc
      simp [PureSpec.execute_ITYPE_slti_pure, SltiInput_of_Lt_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_cmp_result h_constraints h_imm
      simp [SltiInput_of_Lt_instruction_fields, PureSpec.execute_ITYPE_slti_pure]
      have h_rd := slti_register_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_imm
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind, h_rs2⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_ind
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind
      simp [
        true_and,
        h_cmp_result,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_cmp_result h_rd_ind

      split_ands
      . have h_spec := Lt.ValidRows.spec_base_Lt_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row (by omega))
          (h_bus_wellformedness row (by omega))
          h_imm

        simp [
          Lt.ValidRows.iop_of_Lt_opcode, execute_ITYPE_pure,
          execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        have (a) [Decidable a]:
          BitVec.setWidth 32 (if a then 1#1 else 0#1) =
          if a then 1#32 else 0#32
        := by
          by_cases a <;> simp [*]

        rewrite [this] at h_spec

        convert h_spec
        simp [BitVec.slt]
        have (a : FBB) (h) :
          @BitVec.ofFin 8 ⟨↑a % 256, h⟩ =
          BitVec.ofNat 8 ↑a
        := rfl
        simp [this]
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma sltiu_register_properties [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 521)
  :
    ¬(wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0) ∧
    (∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd) ∧
    (∃ (imm: BitVec 12),
      (get_instruction_fields_row air row).rs2_ptr =
      Transpiler.utof (Transpiler.sign_extend_24 imm)
    )
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_cases := Transpiler.transpiler_opcode_521 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_sltiu =>
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_sltiu
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        rewrite [ite_cond_eq_true _ _ (eq_true h_pc_aligned)] at h_transpile
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
          . use imm
            obtain ⟨a, ⟨_, _, _, _, _, b, _, _, _⟩⟩ := h_transpile
            rewrite [←a.2] at b
            rewrite [←b]
            simp
      | inr h_sltu =>
        exfalso
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_sltu
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        rewrite [ite_cond_eq_true _ _ (eq_true h_pc_aligned)] at h_transpile
        dsimp at h_transpile
        split_ifs at h_transpile
        . have := Transpiler.extract_opcode h_transpile.1
          simp at this
          simp [this] at h_transpile
        . simp [-Vector.mk_eq] at h_transpile
          rewrite [h_imm] at h_transpile
          rewrite [←h_transpile.1.2] at h_transpile
          simp at h_transpile

  lemma sltiu_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
  :
    ((get_instruction_fields_row air row).opcode = 521 →
      SltiuOutput_matches_Lt_instruction_fields (get_instruction_fields_row air row)
        (PureSpec.execute_ITYPE_sltiu_pure
          (SltiuInput_of_Lt_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SltiuOutput_matches_Lt_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_cmp_result,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= Lt.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_assumptions row (by omega))
        (h_bus_wellformedness row (by omega))
    split_ands
    . clear *-h_b0
      simp [get_instruction_fields_row, h_b0]
    . clear *-h_b1
      simp [get_instruction_fields_row, h_b1]
    . clear *-h_b2
      simp [get_instruction_fields_row, h_b2]
    . clear *-h_b3
      simp [get_instruction_fields_row, h_b3]
    . simp [get_instruction_fields_row]
      clear *-h_imm_op_properties h_imm
      specialize h_imm_op_properties h_imm
      refine BitVec.eq_of_toInt_eq ?_
      simp [BitVec.toInt_signExtend]
      refine (Int.bmod_eq_iff ?_).mpr ?_
      . trivial
      . grind
    . clear *-h_bus_assumptions h_row h_is_valid h_pc
      simp [PureSpec.execute_ITYPE_sltiu_pure, SltiuInput_of_Lt_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_cmp_result h_constraints h_imm
      simp [SltiuInput_of_Lt_instruction_fields, PureSpec.execute_ITYPE_sltiu_pure]
      have h_rd := sltiu_register_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_imm
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind, h_rs2⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_ind
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind
      simp [
        true_and,
        h_cmp_result,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_cmp_result h_rd_ind

      split_ands
      . have h_spec := Lt.ValidRows.spec_base_Lt_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row (by omega))
          (h_bus_wellformedness row (by omega))
          h_imm

        simp [
          Lt.ValidRows.iop_of_Lt_opcode, execute_ITYPE_pure,
          execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        have (a) [Decidable a]:
          BitVec.setWidth 32 (if a then 1#1 else 0#1) =
          if a then 1#32 else 0#32
        := by
          by_cases a <;> simp [*]

        rewrite [this] at h_spec

        convert h_spec
        have (a : FBB) (h) :
          @BitVec.ofFin 8 ⟨↑a % 256, h⟩ =
          BitVec.ofNat 8 ↑a
        := rfl
        simp [this, BitVec.lt_def]
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma non_imm_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).non_imm = 1 →
    ((get_instruction_fields_row air row).opcode = 520 →
        SltOutput_matches_Lt_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_slt_pure
            (SltInput_of_Lt_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 521 →
          SltuOutput_matches_Lt_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_sltu_pure
              (SltuInput_of_Lt_instruction_fields (get_instruction_fields_row air row)))))
  := by
    intro h_non_imm
    simp [get_instruction_fields_row] at h_non_imm

    exact ⟨
      slt_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_non_imm,
      sltu_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_non_imm
    ⟩

  lemma imm_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).non_imm = 0 →
    ((get_instruction_fields_row air row).opcode = 520 →
        SltiOutput_matches_Lt_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_ITYPE_slti_pure
            (SltiInput_of_Lt_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 521 →
          SltiuOutput_matches_Lt_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_ITYPE_sltiu_pure
              (SltiuInput_of_Lt_instruction_fields (get_instruction_fields_row air row)))))
  := by
    intro h_imm
    simp [get_instruction_fields_row] at h_imm

    exact ⟨
      slti_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_imm,
      sltiu_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_imm
    ⟩

  lemma spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
  :
    List.Forall Lt_instruction_fields.spec (get_instruction_fields air)
  := by
    apply List.forall_iff_forall_mem.mpr
    intro instruction_fields h_instruction_fields
    unfold Lt_instruction_fields.spec

    intro h_is_valid

    simp [get_instruction_fields] at h_instruction_fields
    obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
    rewrite [←h_fields] at ⊢ h_is_valid; clear h_fields

    simp [get_instruction_fields_row] at h_is_valid

    exact ⟨
      get_instruction_fields_row_non_imm_binary air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness,
      ⟨
        get_instruction_fields_row_opcode_range air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness,
        ⟨
          non_imm_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness,
          imm_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness
        ⟩
      ⟩
    ⟩

  theorem lt_spec [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List Lt_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall Lt_instruction_fields.spec
  := by
    use get_instruction_fields air
    simp only [
      bus_from_instruction_fields_eq_air_buses air h_constraints,
      spec_of_get_instruction_fields air h_constraints h_bus_assumptions h_bus_wellformedness
    ]
    trivial

end Equivalence.Lt
