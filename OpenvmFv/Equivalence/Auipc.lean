import OpenvmFv.Spec.Auipc

import OpenvmFv.Spec.ControlFlow.auipc

set_option maxHeartbeats 1_000_000_000

namespace Equivalence.Auipc

  structure Auipc_instruction_fields where
    is_valid : FBB

    pc : FBB
    next_pc : FBB

    opcode : FBB

    prev_rd_timestamp : FBB
    rd_timestamp : FBB
    timestamp : FBB
    next_timestamp : FBB

    rd_ptr : FBB
    imm : FBB

    prev_rd_data : Vector FBB 4
    rd_data : Vector FBB 4

    range_checked_vals : Vector FBB 2
    bitwise_vals : Vector (Vector FBB 3) 5

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val / 4 % 32, by grind⟩

  def AuipcInput_of_Auipc_instruction_fields (row : Auipc_instruction_fields) : PureSpec.AuipcInput := {
    rd := wrap_to_regidx row.rd_ptr
    imm := BitVec.ofNat 20 row.imm.val
    PC := row.pc.toNat
    : PureSpec.AuipcInput
  }

  def AuipcOutput_matches_Auipc_instruction_fields (row : Auipc_instruction_fields) (auipc_output : PureSpec.AuipcOutput) : Prop :=
    match auipc_output.rd with
      | .none =>
        row.rd_data = row.prev_rd_data ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.rd_data ∧
        BabyBear.toBV32 row.rd_data = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat ∧
        auipc_output.nextPC = row.next_pc.toNat

  def Auipc_instruction_fields.spec (row : Auipc_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode = 576 ∧
      AuipcOutput_matches_Auipc_instruction_fields
        row
        (PureSpec.execute_AUIPC_pure (AuipcInput_of_Auipc_instruction_fields row))
    )

  def Auipc_instruction_fields.execution (row : Auipc_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def Auipc_instruction_fields.memory (row : Auipc_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rd_ptr, row.prev_rd_data[0], row.prev_rd_data[1], row.prev_rd_data[2], row.prev_rd_data[3], row.prev_rd_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.rd_data[0], row.rd_data[1], row.rd_data[2], row.rd_data[3], row.rd_timestamp])
  ]

  def Auipc_instruction_fields.range_checks (row : Auipc_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
  ]

  def Auipc_instruction_fields.read_instruction (row : Auipc_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, 0, row.imm, 1, 0, 0, 0])
  ]

  def Auipc_instruction_fields.bitwise (row : Auipc_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.bitwise_vals[0][0], row.bitwise_vals[0][1], row.bitwise_vals[0][2], 0]),
    (row.is_valid, [row.bitwise_vals[1][0], row.bitwise_vals[1][1], row.bitwise_vals[1][2], 0]),
    (row.is_valid, [row.bitwise_vals[2][0], row.bitwise_vals[2][1], row.bitwise_vals[2][2], 0]),
    (row.is_valid, [row.bitwise_vals[3][0], row.bitwise_vals[3][1], row.bitwise_vals[3][2], 0]),
    (row.is_valid, [row.bitwise_vals[4][0], row.bitwise_vals[4][1], row.bitwise_vals[4][2], 0]),
  ]

  def bus_from_instruction_fields (rows : List Auipc_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then            rows.flatMap Auipc_instruction_fields.execution
      else if index = MemoryBus then          rows.flatMap Auipc_instruction_fields.memory
      else if index = RangeCheckerBus then    rows.flatMap Auipc_instruction_fields.range_checks
      else if index = ReadInstructionBus then rows.flatMap Auipc_instruction_fields.read_instruction
      else if index = BitwiseBus then         rows.flatMap Auipc_instruction_fields.bitwise
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_auipc FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_auipc.constraints.allHold air row.1 (by grind)

  def get_instruction_fields_row [Field ExtF] (air : Valid_VmAirWrapper_auipc FBB ExtF) (row : ℕ) : Auipc_instruction_fields := {
    is_valid := air.core.is_valid row 0

    pc := air.adapter.from_state.pc row 0
    next_pc := air.adapter.from_state.pc row 0 + 4

    opcode := 576

    prev_rd_timestamp := air.adapter.rd_aux_cols.base.prev_timestamp row 0
    rd_timestamp := air.adapter.from_state.timestamp row 0
    timestamp := air.adapter.from_state.timestamp row 0
    next_timestamp := air.adapter.from_state.timestamp row 0 + 1

    rd_ptr := air.adapter.rd_ptr row 0
    imm := air.core.imm row 0

    prev_rd_data := #v[air.adapter.rd_aux_cols.prev_data_0 row 0, air.adapter.rd_aux_cols.prev_data_1 row 0, air.adapter.rd_aux_cols.prev_data_2 row 0, air.adapter.rd_aux_cols.prev_data_3 row 0]
    rd_data := #v[air.core.rd_data_0 row 0, air.core.rd_data_1 row 0, air.core.rd_data_2 row 0, air.core.rd_data_3 row 0]

    range_checked_vals :=
      #v[air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0,
          air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0]
    bitwise_vals :=
      #v[
          #v[air.core.rd_data_0 row 0, air.core.rd_data_1 row 0, 0],
          #v[air.core.rd_data_2 row 0, air.core.rd_data_3 row 0, 0],
          #v[air.core.imm_limbs_0 row 0, air.core.imm_limbs_1 row 0, 0],
          #v[air.core.imm_limbs_2 row 0, air.core.pc_limbs_0 row 0, 0],
          #v[air.core.pc_limbs_1 row 0, air.core.pc_msl row 0 (air.adapter.from_state.pc row 0) * 4, 0]
      ]
    : Auipc_instruction_fields
  }

  def get_instruction_fields [Field ExtF] (air : Valid_VmAirWrapper_auipc FBB ExtF) : List Auipc_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma transpile_of_bus_wellformedness [Field ExtF]
    (air : Valid_VmAirWrapper_auipc FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_auipc.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction a b,
    Transpiler.transpile_op instruction 1 (air.adapter.from_state.pc row 0) = some (a, b) ∧
      a = 1 ∧
        b[0] = air.adapter.from_state.pc row 0 ∧
          b[1] = 576 ∧
            b[2] = air.adapter.rd_ptr row 0 ∧
              b[3] = 0 ∧
                b[4] = air.core.imm row 0 ∧
                  b[5] = 1 ∧ b[6] = 0 ∧ b[7] = 0 ∧ b[8] = 0
  := by
    unfold VmAirWrapper_auipc.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
    simp [
      VmAirWrapper_auipc.constraints.propertiesToAssume,
      Interaction.ReadInstructionBusEntry.operand_properties,
      VmAirWrapper_auipc.constraints._readInstructionBus_row,
      VmAirWrapper_auipc.constraints.readInstructionBus_row,
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

  lemma auipc_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_auipc FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_auipc.constraints.wf_propertiesToAssumePerRow air row)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    obtain ⟨ imm, rd, h_instruction, h_rd ⟩ := Transpiler.transpiler_opcode_576 h_transpile.1 h_transpile.2.2.2.1
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

  set_option maxRecDepth 1_000_000 in
  theorem auipc_spec [Field ExtF]
    (air : Valid_VmAirWrapper_auipc FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_auipc.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_auipc.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List Auipc_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall Auipc_instruction_fields.spec
  := by
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl

    have h_interactions := VmAirWrapper_auipc.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold allHold_allRows at h_constraints
    use get_instruction_fields air
    split_ands
    . unfold VmAirWrapper_auipc.constraints.constrain_interactions at h_interactions
      rewrite [h_interactions]; clear h_interactions
      unfold bus_from_instruction_fields Auipc_instruction_fields.execution Auipc_instruction_fields.memory Auipc_instruction_fields.range_checks Auipc_instruction_fields.read_instruction
      simp [
        get_instruction_fields,
        VmAirWrapper_auipc_constraint_and_interaction_simplification
      ]
      unfold VmAirWrapper_auipc.constraints.executionBus_row
      unfold VmAirWrapper_auipc.constraints.memoryBus_row
      unfold VmAirWrapper_auipc.constraints.rangeCheckerBus_row
      unfold VmAirWrapper_auipc.constraints.readInstructionBus_row
      unfold VmAirWrapper_auipc.constraints.bitwiseBus_row
      funext index
      by_cases h_index: index = ExecutionBus
      . simp [h_index, get_instruction_fields_row, List.flatMap_map]
      by_cases h_index: index = MemoryBus
      . simp [h_index, get_instruction_fields_row, List.flatMap_map]
        congr
        funext row
        congr
        all_goals simp [h_neg_one]
      by_cases h_index: index = RangeCheckerBus
      . simp [h_index, get_instruction_fields_row, List.flatMap_map]
      by_cases h_index: index = ReadInstructionBus
      . simp [h_index, get_instruction_fields_row, List.flatMap_map]
      by_cases h_index: index = BitwiseBus
      . simp [h_index, get_instruction_fields_row, List.flatMap_map, Auipc_instruction_fields.bitwise]
      . simp [*]
    . apply List.forall_iff_forall_mem.mpr
      intro instruction_fields h_instruction_fields
      unfold Auipc_instruction_fields.spec
      simp [get_instruction_fields] at h_instruction_fields
      obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
      rewrite [←h_fields]; clear h_fields
      simp [AuipcInput_of_Auipc_instruction_fields,
            AuipcOutput_matches_Auipc_instruction_fields,
            PureSpec.execute_AUIPC_pure]

      intro h_is_valid
      specialize h_constraints ⟨ row, by omega ⟩
      specialize h_bus_assumptions row (by omega)
      specialize h_bus_wellformedness row (by omega)

      have spec :=
        Auipc.ValidRows.spec_auipc
          ExtF
          air
          row
          (by omega)
          h_constraints
          h_is_valid
          h_bus_assumptions
          h_bus_wellformedness

      obtain ⟨ h_rd_nz, ⟨ rd', eq_rd' ⟩⟩ := auipc_rd_properties air row h_is_valid h_bus_wellformedness
      simp_all [get_instruction_fields_row,
                VmAirWrapper_auipc_constraint_and_interaction_simplification]
      split_ands
      . assumption
      . simp [wrap_to_regidx, Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd'.1
          simp
      . have := h_bus_assumptions.1.1.1
        simp [← BitVec.toNat_inj]
        omega

end Equivalence.Auipc
