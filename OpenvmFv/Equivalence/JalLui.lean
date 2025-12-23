import OpenvmFv.Spec.JalLui

import OpenvmFv.Spec.ControlFlow.jal
import OpenvmFv.Spec.ControlFlow.lui

set_option maxHeartbeats 1_000_000_000

namespace Equivalence.JalLui

  structure JalLui_instruction_fields where
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
    bitwise_vals : Vector (Vector FBB 3) 3

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val / 4 % 32, by grind⟩

  def JalLui_instruction_fields.execution (row : JalLui_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def JalLui_instruction_fields.memory (row : JalLui_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rd_ptr, row.prev_rd_data[0], row.prev_rd_data[1], row.prev_rd_data[2], row.prev_rd_data[3], row.prev_rd_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.rd_data[0], row.rd_data[1], row.rd_data[2], row.rd_data[3], row.rd_timestamp])
  ]

  def JalLui_instruction_fields.range_checks (row : JalLui_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
  ]

  def JalLui_instruction_fields.program (row : JalLui_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, 0, row.imm, 1, 0, row.is_valid, 0])
  ]

  def JalLui_instruction_fields.bitwise (row : JalLui_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.bitwise_vals[0][0], row.bitwise_vals[0][1], row.bitwise_vals[0][2], 0]),
    (row.is_valid, [row.bitwise_vals[1][0], row.bitwise_vals[1][1], row.bitwise_vals[1][2], 0]),
    (if row.is_valid = 1 ∧ row.opcode = 560 then 1 else 0, [row.bitwise_vals[2][0], row.bitwise_vals[2][1], row.bitwise_vals[2][2], 1])
  ]

  def bus_from_instruction_fields (rows : List JalLui_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then         rows.flatMap JalLui_instruction_fields.execution
      else if index = MemoryBus then       rows.flatMap JalLui_instruction_fields.memory
      else if index = RangeCheckerBus then rows.flatMap JalLui_instruction_fields.range_checks
      else if index = ProgramBus then      rows.flatMap JalLui_instruction_fields.program
      else if index = BitwiseBus then      rows.flatMap JalLui_instruction_fields.bitwise
      else []

  def get_instruction_fields_row [Field ExtF] (air : Valid_VmAirWrapper_jallui FBB ExtF) (row : ℕ) : JalLui_instruction_fields := {
    is_valid := air.core.is_valid row 0

    pc := air.adapter.inner.from_state.pc row 0
    next_pc := air.to_pc row 0

    opcode := air.core.expected_opcode row 0

    prev_rd_timestamp := air.adapter.inner.rd_aux_cols.base.prev_timestamp row 0
    rd_timestamp := air.adapter.inner.from_state.timestamp row 0
    timestamp := air.adapter.inner.from_state.timestamp row 0
    next_timestamp := air.adapter.inner.from_state.timestamp row 0 + 1

    rd_ptr := air.adapter.inner.rd_ptr row 0
    imm := air.core.imm row 0

    prev_rd_data := #v[air.adapter.inner.rd_aux_cols.prev_data_0 row 0, air.adapter.inner.rd_aux_cols.prev_data_1 row 0, air.adapter.inner.rd_aux_cols.prev_data_2 row 0, air.adapter.inner.rd_aux_cols.prev_data_3 row 0]
    rd_data := #v[air.core.rd_data_0 row 0, air.core.rd_data_1 row 0, air.core.rd_data_2 row 0, air.core.rd_data_3 row 0]

    range_checked_vals :=
      #v[air.adapter.inner.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.inner.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0]
    bitwise_vals :=
      #v[
          #v[air.core.rd_data_0 row 0, air.core.rd_data_1 row 0, 0],
          #v[air.core.rd_data_2 row 0, air.core.rd_data_3 row 0, 0],
          #v[air.core.rd_data_3 row 0, 192, air.core.rd_data_3 row 0 + 192]
      ]
    : JalLui_instruction_fields
  }

  def get_instruction_fields [Field ExtF] (air : Valid_VmAirWrapper_jallui FBB ExtF) : List JalLui_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma transpile_of_bus_wellformedness [Field ExtF]
    (air : Valid_VmAirWrapper_jallui FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_jallui.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction a b,
    Transpiler.transpile_op instruction 1 (air.adapter.inner.from_state.pc row 0) = some (a, b) ∧
      a = 1 ∧
        b[0] = air.adapter.inner.from_state.pc row 0 ∧
          b[1] = air.core.expected_opcode row 0 ∧
            b[2] = air.adapter.inner.rd_ptr row 0 ∧
              b[3] = 0 ∧
                b[4] = air.core.imm row 0 ∧
                  b[5] = 1 ∧ b[6] = 0 ∧ b[7] = air.adapter.needs_write row 0 ∧ b[8] = 0
  := by
    unfold VmAirWrapper_jallui.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
    simp [
      VmAirWrapper_jallui.constraints.propertiesToAssume,
      Interaction.ProgramBusEntry.operand_properties,
      VmAirWrapper_jallui.constraints._programBus_row,
      VmAirWrapper_jallui.constraints.programBus_row,
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

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_jallui FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_jallui.constraints.allHold air row.1 (by grind)

  lemma jallui_buses_spec [Field ExtF]
    (air : Valid_VmAirWrapper_jallui FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_jallui.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_jallui.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.buses = bus_from_instruction_fields (get_instruction_fields air)
  := by
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl

    have h_interactions := VmAirWrapper_jallui.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_jallui.constraints.constrain_interactions at h_interactions
    rewrite [h_interactions]; clear h_interactions
    unfold bus_from_instruction_fields JalLui_instruction_fields.execution JalLui_instruction_fields.memory JalLui_instruction_fields.range_checks JalLui_instruction_fields.program
    simp [
      get_instruction_fields,
      VmAirWrapper_jallui_constraint_and_interaction_simplification
    ]

    unfold VmAirWrapper_jallui.constraints.executionBus_row
    unfold VmAirWrapper_jallui.constraints.memoryBus_row
    unfold VmAirWrapper_jallui.constraints.rangeCheckerBus_row
    unfold VmAirWrapper_jallui.constraints.programBus_row
    unfold VmAirWrapper_jallui.constraints.bitwiseBus_row
    have h_nw := @JalLui.ValidRows.needs_write_eq_is_valid _ _ air
    funext index
    by_cases h_index: index = ExecutionBus
    . simp [h_index, get_instruction_fields_row, List.flatMap_map]
    by_cases h_index: index = MemoryBus
    . simp [h_index, get_instruction_fields_row, List.flatMap_map]
      simp [List.flatMap_def]; congr 1; simp [h_neg_one]
      intro row ub_row
      apply h_nw
      . specialize h_constraints ⟨ row, ub_row ⟩
        assumption
      . specialize h_bus_wellformedness row (by omega)
        assumption
    by_cases h_index: index = RangeCheckerBus
    . simp [h_index, get_instruction_fields_row, List.flatMap_map]
      simp [List.flatMap_def]; congr 1; simp
      intro row ub_row
      apply h_nw
      . specialize h_constraints ⟨ row, ub_row ⟩
        assumption
      . specialize h_bus_wellformedness row (by omega)
        assumption
    by_cases h_index: index = ProgramBus
    . simp [h_index, get_instruction_fields_row, List.flatMap_map]
      simp [List.flatMap_def]; congr 1; simp
      intro row ub_row
      apply h_nw
      . specialize h_constraints ⟨ row, ub_row ⟩
        assumption
      . specialize h_bus_wellformedness row (by omega)
        assumption
    by_cases h_index: index = BitwiseBus
    . simp [h_index, get_instruction_fields_row, List.flatMap_map, JalLui_instruction_fields.bitwise]
      simp [List.flatMap_def]; congr 1; simp
      intro row ub_row
      specialize h_constraints ⟨ row, ub_row ⟩
      specialize h_bus_wellformedness row (by omega)
      rw [VmAirWrapper_jallui.constraints.allHold_simplified_of_allHold] at h_constraints
      simp [VmAirWrapper_jallui_constraint_and_interaction_simplification] at h_constraints
      simp [← Rv32JalLuiCoreAir_4.is_valid_def,
            ← Rv32JalLuiCoreAir_4.expected_opcode_def] at *
      grind
    . simp [*]

  /-
     ***
     *** LUI
     ***
  -/

  def LuiInput_of_JalLui_instruction_fields (row : JalLui_instruction_fields) : PureSpec.LuiInput := {
    rd := wrap_to_regidx row.rd_ptr
    imm := BitVec.ofNat 21 (row.imm.val)
    PC := row.pc.toNat
    : PureSpec.LuiInput
  }

  def LuiOutput_matches_JalLui_instruction_fields (row : JalLui_instruction_fields) (lui_output : PureSpec.LuiOutput) : Prop :=
    match lui_output.rd with
      | .none =>
        row.rd_data = row.prev_rd_data ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.rd_data ∧
        BabyBear.toBV32 row.rd_data = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat ∧
        lui_output.nextPC = row.next_pc.toNat

  /-
     ***
     *** LUI
     ***
  -/

  def JalInput_of_JalLui_instruction_fields (row : JalLui_instruction_fields) : PureSpec.JalInput := {
    rd := wrap_to_regidx row.rd_ptr
    imm := BitVec.ofInt 21 (BabyBear.toInt row.imm)
    PC := row.pc.toNat
    misa := LeanRV32D.Functions.misa
    : PureSpec.JalInput
  }

  def JalOutput_matches_JalLui_instruction_fields (row : JalLui_instruction_fields) (jal_output : PureSpec.JalOutput) : Prop :=
    match jal_output.rd with
      | .none =>
        row.rd_data = row.prev_rd_data ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.rd_data ∧
        BabyBear.toBV32 row.rd_data = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat ∧
        jal_output.nextPC = .some row.next_pc.toNat

  /-
     ***
     *** Main specification
     ***
  -/

  def JalLui_instruction_fields.spec (row : JalLui_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode ∈ Finset.Icc 560 561 ∧
      (row.opcode = 561 →
        LuiOutput_matches_JalLui_instruction_fields
        row
        (PureSpec.execute_LUI_pure (LuiInput_of_JalLui_instruction_fields row))
      ) ∧
      (row.opcode = 560 →
        JalOutput_matches_JalLui_instruction_fields
        row
        (PureSpec.execute_JAL_pure (JalInput_of_JalLui_instruction_fields row))
      )
    )

  lemma jallui_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_jallui FBB ExtF)
    (row : ℕ)
    (row_in_range : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_constraints : VmAirWrapper_jallui.constraints.allHold air row row_in_range)
    (h_bus_wellformedness : VmAirWrapper_jallui.constraints.wf_propertiesToAssumePerRow air row)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_pc_bound := Transpiler.pc_bound_of_some h_transpile.1
    rw [VmAirWrapper_jallui.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_jallui_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨ c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 ⟩ := h_constraints
    simp [← Rv32JalLuiCoreAir_4.expected_opcode_def] at h_transpile
    obtain is_lui | is_lui := c1
    . simp_all
      obtain ⟨ imm, rd, h_instruction, h_rd ⟩ := Transpiler.transpiler_opcode_560 h_transpile.1 h_transpile.2.2.2.1
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
    . simp_all
      obtain ⟨ imm, rd, h_instruction, h_rd ⟩ := Transpiler.transpiler_opcode_561 h_transpile.1 h_transpile.2.2.2.1
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

  set_option maxRecDepth 1_000_000 in
  theorem jallui_spec [Field ExtF]
    (air : Valid_VmAirWrapper_jallui FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_jallui.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_jallui.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List JalLui_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall JalLui_instruction_fields.spec
  := by
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl

    have h_interactions := VmAirWrapper_jallui.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    use get_instruction_fields air
    split_ands
    . exact jallui_buses_spec air h_constraints h_bus_axioms h_bus_wellformedness
    . apply List.forall_iff_forall_mem.mpr
      intro instruction_fields h_instruction_fields
      unfold JalLui_instruction_fields.spec
      simp [get_instruction_fields] at h_instruction_fields
      obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
      rewrite [←h_fields]; clear h_fields

      intro h_is_valid
      specialize h_constraints ⟨ row, by omega ⟩
      specialize h_bus_axioms row (by omega)
      specialize h_bus_wellformedness row (by omega)

      split_ands
      . rw [VmAirWrapper_jallui.constraints.allHold_simplified_of_allHold] at h_constraints
        simp [get_instruction_fields_row,
              VmAirWrapper_jallui_constraint_and_interaction_simplification,
              ← Rv32JalLuiCoreAir_4.expected_opcode_def] at h_constraints ⊢
        grind
      . intro h_is_lui
        simp [LuiInput_of_JalLui_instruction_fields,
              LuiOutput_matches_JalLui_instruction_fields,
              PureSpec.execute_LUI_pure]

        have spec :=
          JalLui.ValidRows.spec_lui
            ExtF
            air
            row
            (by omega)
            h_constraints
            h_bus_axioms
            h_bus_wellformedness

        obtain ⟨ h_rd_nz, ⟨ rd', eq_rd' ⟩⟩ := jallui_rd_properties air row (by omega) h_is_valid h_constraints h_bus_wellformedness
        rw [VmAirWrapper_jallui.constraints.allHold_simplified_of_allHold] at h_constraints
        simp_all [get_instruction_fields_row,
                  VmAirWrapper_jallui_constraint_and_interaction_simplification]
        split_ands
        . assumption
        . simp [wrap_to_regidx, Transpiler.ind, regidx_to_fin]
          rewrite [Nat.mod_eq_of_lt]
          . simp [Nat.toNat, mul_comm]
          . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd'.1
            simp
        . simp [Valid_VmAirWrapper_jallui.to_pc]
          have := h_bus_axioms.1.1.1
          simp_all [← BitVec.toNat_inj, ← Rv32JalLuiCoreAir_4.is_valid_def]
          simp [← Rv32JalLuiCoreAir_4.expected_opcode_def] at h_is_lui
          have ⟨ h_lui, h_jal ⟩ : air.core.is_lui row 0 = 1 ∧ air.core.is_jal row 0 = 0
            := by omega
          simp_all
          grind
      . intro h_is_jal
        simp [JalInput_of_JalLui_instruction_fields,
              JalOutput_matches_JalLui_instruction_fields,
              PureSpec.execute_JAL_pure]

        simp [get_instruction_fields_row] at h_is_jal h_is_valid ⊢

        have ⟨ jspec_pc, jspec_rd ⟩ :=
          JalLui.ValidRows.spec_jal
            ExtF
            air
            row
            (by omega)
            h_constraints
            h_bus_axioms
            h_bus_wellformedness
            (by simp [VmAirWrapper_jallui_constraint_and_interaction_simplification]; assumption)
            h_is_jal

        obtain ⟨ h_rd_nz, ⟨ rd', eq_rd' ⟩⟩ := jallui_rd_properties air row (by omega) h_is_valid h_constraints h_bus_wellformedness
        simp [get_instruction_fields_row] at h_rd_nz eq_rd'
        simp [eq_rd'] at h_rd_nz

        have h_nw := @JalLui.ValidRows.needs_write_eq_is_valid _ _ air row (by omega) h_constraints h_bus_wellformedness

        simp [h_is_valid, VmAirWrapper_jallui_constraint_and_interaction_simplification, and_assoc] at h_bus_axioms
        obtain ⟨ ub_pc, al_pc, ub_npc, al_npc, rest ⟩ := h_bus_axioms
        clear rest
        simp [h_is_valid, VmAirWrapper_jallui_constraint_and_interaction_simplification] at h_bus_wellformedness
        obtain ⟨ h_mem, h_range, h_prog, h_bit ⟩ := h_bus_wellformedness
        simp [*] at h_mem h_range h_bit

        have hb0 :
          BitVec.ofBool
            (BitVec.ofNat 32 ↑(air.adapter.inner.from_state.pc row 0) +
              BitVec.signExtend 32 (BitVec.ofInt 21 (BabyBear.toInt (air.core.imm row 0))))[0] = 0#1
        := by
          rw [← jspec_rd, ← BitVec.toNat_inj, BitVec.getElem_eq_testBit_toNat]
          grind

        have hb1 :
          BitVec.ofBool
            (BitVec.ofNat 32 ↑(air.adapter.inner.from_state.pc row 0) +
              BitVec.signExtend 32 (BitVec.ofInt 21 (BabyBear.toInt (air.core.imm row 0))))[1] = 0#1
        := by
          rw [← jspec_rd, ← BitVec.toNat_inj, BitVec.getElem_eq_testBit_toNat]
          grind

        simp [*]

        split_ands
        . rw [← jspec_pc]
          congr
        . simp [wrap_to_regidx, Transpiler.ind, regidx_to_fin]
          rw [mul_comm]; congr
          apply Nat.mod_eq_of_lt
          omega

end Equivalence.JalLui
