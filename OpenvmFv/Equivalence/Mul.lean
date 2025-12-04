import OpenvmFv.Spec.Mul

import OpenvmFv.Spec.MULH.mul

namespace Equivalence.Mul

  @[ext]
  structure MUL_instruction_fields where
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

    range_checked_vals : Vector FBB 6
    range_checked_tuples : Vector (Vector FBB 2) 4

  lemma MUL_instruction_fields_eq (a b : MUL_instruction_fields)
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
    a.range_checked_vals = b.range_checked_vals ∧
    a.range_checked_tuples = b.range_checked_tuples
      → a = b
  := by
    intro field_eq
    ext <;> grind

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val / 4 % 32, by grind⟩

  def MulInput_of_MUL_instruction_fields (row : MUL_instruction_fields) : PureSpec.MulInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.MulInput
  }

  def MulOutput_matches_MUL_instruction_fields (row : MUL_instruction_fields) (mul_output : PureSpec.MulOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    mul_output.nextPC = row.next_pc.toNat ∧
    match mul_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def MUL_instruction_fields.spec (row : MUL_instruction_fields) : Prop :=
    row.is_valid = 1 →
      row.opcode = 592 →
        MulOutput_matches_MUL_instruction_fields
          row
          (PureSpec.execute_MULH_mul_pure (MulInput_of_MUL_instruction_fields row))

  def MUL_instruction_fields.execution (row : MUL_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def MUL_instruction_fields.memory (row : MUL_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.prev_b_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.b_timestamp]),
    (-row.is_valid, [1, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.prev_c_timestamp]),
    ( row.is_valid, [1, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.c_timestamp]),
    (-row.is_valid, [1, row.rd_ptr, row.prev_a[0], row.prev_a[1], row.prev_a[2], row.prev_a[3], row.prev_a_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.a_timestamp]),
  ]

  def MUL_instruction_fields.range_checks (row : MUL_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
    (row.is_valid, [row.range_checked_vals[2], 17]),
    (row.is_valid, [row.range_checked_vals[3], 12]),
    (row.is_valid, [row.range_checked_vals[4], 17]),
    (row.is_valid, [row.range_checked_vals[5], 12]),
  ]

  def MUL_instruction_fields.read_instruction (row : MUL_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, row.rs1_ptr, row.rs2_ptr, 1, 0, 0, 0])
  ]

  def MUL_instruction_fields.range_check_tuples (row : MUL_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_tuples[0][0], row.range_checked_tuples[0][1]]),
    (row.is_valid, [row.range_checked_tuples[1][0], row.range_checked_tuples[1][1]]),
    (row.is_valid, [row.range_checked_tuples[2][0], row.range_checked_tuples[2][1]]),
    (row.is_valid, [row.range_checked_tuples[3][0], row.range_checked_tuples[3][1]])
  ]

  def bus_from_instruction_fields (rows : List MUL_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then              rows.flatMap MUL_instruction_fields.execution
      else if index = MemoryBus then            rows.flatMap MUL_instruction_fields.memory
      else if index = RangeCheckerBus then      rows.flatMap MUL_instruction_fields.range_checks
      else if index = ProgramBus then   rows.flatMap MUL_instruction_fields.read_instruction
      else if index = RangeTupleCheckerBus then rows.flatMap MUL_instruction_fields.range_check_tuples
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_mul FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_mul.constraints.allHold air row.1 (by grind)

  def get_instruction_fields_row (air : Valid_VmAirWrapper_mul FBB ExtF) (row : ℕ) : MUL_instruction_fields := {
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
    range_checked_vals :=
      #v[air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0,
         air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0,
         air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0]
    range_checked_tuples :=
      #v[
        #v[air.core.a_0 row 0, air.core.carry row 0 0],
        #v[air.core.a_1 row 0, air.core.carry row 0 1],
        #v[air.core.a_2 row 0, air.core.carry row 0 2],
        #v[air.core.a_3 row 0, air.core.carry row 0 3],
      ]
  }

  def get_instruction_fields (air : Valid_VmAirWrapper_mul FBB ExtF) : List MUL_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma execution_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mul.constraints.executionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MUL_instruction_fields.execution (get_instruction_fields air)
  := by
    unfold MUL_instruction_fields.execution
    unfold VmAirWrapper_mul.constraints.executionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma memory_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mul.constraints.memoryBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MUL_instruction_fields.memory (get_instruction_fields air)
  := by
    unfold MUL_instruction_fields.memory
    unfold VmAirWrapper_mul.constraints.memoryBus_row
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      h_neg_one
    ]

  lemma range_checks_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mul.constraints.rangeCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MUL_instruction_fields.range_checks (get_instruction_fields air)
  := by
    unfold MUL_instruction_fields.range_checks
    unfold VmAirWrapper_mul.constraints.rangeCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma read_instruction_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mul.constraints.programBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MUL_instruction_fields.read_instruction (get_instruction_fields air)
  := by
    unfold MUL_instruction_fields.read_instruction
    unfold VmAirWrapper_mul.constraints.programBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      ← Valid_MultiplicationCoreAir_4_8.ctx.instruction.opcode_def
    ]

  lemma range_check_tuples_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
  :
    List.flatMap (VmAirWrapper_mul.constraints.rangeTupleCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap MUL_instruction_fields.range_check_tuples (get_instruction_fields air)
  := by
    unfold MUL_instruction_fields.range_check_tuples
    unfold VmAirWrapper_mul.constraints.rangeTupleCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
    ]

  lemma bus_from_instruction_fields_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
    (h_constraints : allHold_allRows air)
  :
    air.buses = bus_from_instruction_fields (get_instruction_fields air)
  := by
    have h_interactions := VmAirWrapper_mul.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_mul.constraints.constrain_interactions at h_interactions
    rewrite [h_interactions]; clear h_interactions
    unfold bus_from_instruction_fields
    simp [
      execution_eq_air_buses,
      memory_eq_air_buses,
      range_checks_eq_air_buses,
      read_instruction_eq_air_buses,
      range_check_tuples_eq_air_buses
    ]

  lemma get_instruction_fields_row_opcode_range [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
    (row : ℕ)
  :
    (get_instruction_fields_row air row).opcode = 592
  := by
    simp [get_instruction_fields_row,
          ← Valid_MultiplicationCoreAir_4_8.ctx.instruction.opcode_def]

  lemma transpile_of_bus_wellformedness [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_mul.constraints.wf_propertiesToAssumePerRow air row)
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
    unfold VmAirWrapper_mul.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
    simp [
      VmAirWrapper_mul.constraints.propertiesToAssume,
      Interaction.ProgramBusEntry.operand_properties,
      VmAirWrapper_mul.constraints._programBus_row,
      VmAirWrapper_mul.constraints.programBus_row,
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

  lemma mul_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_mul.constraints.wf_propertiesToAssumePerRow air row)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 592)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile.1
    have h_bound := Transpiler.pc_bound_of_some h_transpile.1
    rewrite [h_opcode] at h_transpile
    have h_cases := Transpiler.transpiler_opcode_592 h_transpile.1 h_transpile.2.2.2.1
    obtain ⟨rs2, rs1, rd, srs1, srs2, h_instruction, h_rd⟩ := h_cases
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

  lemma mul_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_mul.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_mul.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 592 →
        MulOutput_matches_MUL_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_MULH_mul_pure
            (MulInput_of_MUL_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [MulOutput_matches_MUL_instruction_fields]

    obtain ⟨
      h_pc,
      ub_a0, ub_a1, ub_a2, ub_a3,
      ub_b0, ub_b1, ub_b2, ub_b3,
      ub_c0, ub_c1, ub_c2, ub_c3
    ⟩ :=
      Mul.ValidRows.essentials
        ExtF air row h_row
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_axioms row (by omega))
        (h_bus_wellformedness row (by omega))

    simp [get_instruction_fields_row, *]

    split_ands
    . clear *- h_bus_axioms h_row h_is_valid h_pc
      simp [PureSpec.execute_MULH_mul_pure, MulInput_of_MUL_instruction_fields]
      simp [← BitVec.toNat_inj]
      specialize h_bus_axioms row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . simp [MulInput_of_MUL_instruction_fields, PureSpec.execute_MULH_mul_pure]
      have h_rd := mul_rd_properties
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
      . have := Mul.ValidRows.spec_MUL
          ExtF
          air
          row
          (by omega)
          (h_bus_wellformedness row (by omega))
        trans (U32.toBV #v[(air.core.a_0 row 0).val, (air.core.a_1 row 0).val, (air.core.a_2 row 0).val, (air.core.a_3 row 0).val])
        . congr
        . rw [this]
          simp [h_opcode, Mul.ValidRows.rop_of_Mul_opcode]
          congr
      . rw [h_rd_ind]
        simp [Transpiler.ind, regidx_to_fin, wrap_to_regidx]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_mul FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_mul.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_mul.constraints.wf_propertiesToAssumePerRow air row)
  :
    List.Forall MUL_instruction_fields.spec (get_instruction_fields air)
  := by
    apply List.forall_iff_forall_mem.mpr
    intro instruction_fields h_instruction_fields
    unfold MUL_instruction_fields.spec

    intro h_is_valid

    simp [get_instruction_fields] at h_instruction_fields
    obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
    rewrite [←h_fields] at ⊢ h_is_valid; clear h_fields

    simp [get_instruction_fields_row] at h_is_valid
    exact mul_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness

end Equivalence.Mul
