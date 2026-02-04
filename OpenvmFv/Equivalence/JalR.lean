import OpenvmFv.RV32D.jalr

import OpenvmFv.Spec.JalR
import OpenvmFv.RV32D.BusEffect

set_option maxHeartbeats 1_000_000_000

namespace Equivalence.JalR

  structure JalR_instruction_fields where
    is_valid : FBB

    pc : FBB
    next_pc : FBB

    opcode : FBB

    prev_rs1_timestamp : FBB
    rs1_timestamp : FBB
    prev_rd_timestamp : FBB
    rd_timestamp : FBB
    timestamp : FBB
    next_timestamp : FBB

    rs1_ptr : FBB
    rd_ptr : FBB
    imm : FBB
    imm_sign : FBB

    rs1_data : Vector FBB 4
    prev_rd_data : Vector FBB 4
    rd_data : Vector FBB 4

    range_checked_vals : Vector FBB 8
    bitwise_vals : Vector (Vector FBB 3) 1


  def JalR_instruction_fields.execution (row : JalR_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def JalR_instruction_fields.memory (row : JalR_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.rs1_data[0], row.rs1_data[1], row.rs1_data[2], row.rs1_data[3], row.prev_rs1_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.rs1_data[0], row.rs1_data[1], row.rs1_data[2], row.rs1_data[3], row.rs1_timestamp]),
    (-row.is_valid, [1, row.rd_ptr, row.prev_rd_data[0], row.prev_rd_data[1], row.prev_rd_data[2], row.prev_rd_data[3], row.prev_rd_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.rd_data[0], row.rd_data[1], row.rd_data[2], row.rd_data[3], row.rd_timestamp])
  ]

  def JalR_instruction_fields.range_checks (row : JalR_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 8]),
    (row.is_valid, [row.range_checked_vals[1], 6]),
    (row.is_valid, [row.range_checked_vals[2], 14]),
    (row.is_valid, [row.range_checked_vals[3], 15]),
    (row.is_valid, [row.range_checked_vals[4], 17]),
    (row.is_valid, [row.range_checked_vals[5], 12]),
    (row.is_valid, [row.range_checked_vals[6], 17]),
    (row.is_valid, [row.range_checked_vals[7], 12]),
  ]

  def JalR_instruction_fields.program (row : JalR_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, row.rs1_ptr, row.imm, 1, 0, row.is_valid, row.imm_sign])
  ]

  def JalR_instruction_fields.bitwise (row : JalR_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.bitwise_vals[0][0], row.bitwise_vals[0][1], row.bitwise_vals[0][2], 0])
  ]

  def bus_from_instruction_fields (rows : List JalR_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then         rows.flatMap JalR_instruction_fields.execution
      else if index = MemoryBus then       rows.flatMap JalR_instruction_fields.memory
      else if index = RangeCheckerBus then rows.flatMap JalR_instruction_fields.range_checks
      else if index = ProgramBus then      rows.flatMap JalR_instruction_fields.program
      else if index = BitwiseBus then      rows.flatMap JalR_instruction_fields.bitwise
      else []

  def get_instruction_fields_row [Field ExtF] (air : Valid_VmAirWrapper_jalr FBB ExtF) (row : ℕ) : JalR_instruction_fields := {
    is_valid := air.core.is_valid row 0

    pc := air.adapter.from_state.pc row 0
    next_pc := air.core.to_pc row 0

    opcode := 565

    prev_rs1_timestamp := air.adapter.rs1_aux_cols.base.prev_timestamp row 0
    rs1_timestamp := air.adapter.from_state.timestamp row 0
    prev_rd_timestamp := air.adapter.rd_aux_cols.base.prev_timestamp row 0
    rd_timestamp := air.adapter.from_state.timestamp row 0 + 1
    timestamp := air.adapter.from_state.timestamp row 0
    next_timestamp := air.adapter.from_state.timestamp row 0 + 2

    rs1_ptr := air.adapter.rs1_ptr row 0
    rd_ptr := air.adapter.rd_ptr row 0
    imm := air.core.imm row 0
    imm_sign := air.core.imm_sign row 0

    rs1_data := #v[air.core.rs1_data_0 row 0, air.core.rs1_data_1 row 0, air.core.rs1_data_2 row 0, air.core.rs1_data_3 row 0]
    prev_rd_data := #v[air.adapter.rd_aux_cols.prev_data_0 row 0, air.adapter.rd_aux_cols.prev_data_1 row 0, air.adapter.rd_aux_cols.prev_data_2 row 0, air.adapter.rd_aux_cols.prev_data_3 row 0]
    rd_data := #v[air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 0, air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 1, air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 2, air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 3]

    range_checked_vals :=
      #v[air.core.rd_data_1 row 0,
         air.core.rd_data_2 row 0,
         air.core.to_pc_limbs_1 row 0,
         air.core.to_pc_limbs_0 row 0,
         air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0,
         air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0,
         air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0]

    bitwise_vals :=
      #v[
          #v[air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 0,
            air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 1, 0],
      ]
    : JalR_instruction_fields
  }

  def get_instruction_fields [Field ExtF] (air : Valid_VmAirWrapper_jalr FBB ExtF) : List JalR_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma transpile_of_bus_wellformedness [Field ExtF]
    (air : Valid_VmAirWrapper_jalr FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_jalr.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction a b,
    Transpiler.transpile_op instruction 1 (air.adapter.from_state.pc row 0) = some (a, b) ∧
      a = 1 ∧
        b[0] = air.adapter.from_state.pc row 0 ∧
          b[1] = 565 ∧
            b[2] = air.adapter.rd_ptr row 0 ∧
              b[3] = air.adapter.rs1_ptr row 0 ∧
                b[4] = air.core.imm row 0 ∧
                  b[5] = 1 ∧ b[6] = 0 ∧ b[7] = air.adapter.needs_write row 0 ∧ b[8] = air.core.imm_sign row 0
  := by
    unfold VmAirWrapper_jalr.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
    simp [
      VmAirWrapper_jalr.constraints.propertiesToAssume,
      Interaction.ProgramBusEntry.operand_properties,
      VmAirWrapper_jalr.constraints._programBus_row,
      VmAirWrapper_jalr.constraints.programBus_row,
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

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_jalr FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_jalr.constraints.allHold air row.1 (by grind)

  lemma jalr_buses_spec [Field ExtF]
    (air : Valid_VmAirWrapper_jalr FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_jalr.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.buses = bus_from_instruction_fields (get_instruction_fields air)
  := by
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl

    have h_interactions := VmAirWrapper_jalr.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_jalr.constraints.constrain_interactions at h_interactions
    rewrite [h_interactions]; clear h_interactions
    unfold bus_from_instruction_fields JalR_instruction_fields.execution JalR_instruction_fields.memory JalR_instruction_fields.range_checks JalR_instruction_fields.program
    simp [
      get_instruction_fields,
      VmAirWrapper_jalr_constraint_and_interaction_simplification
    ]

    unfold VmAirWrapper_jalr.constraints.executionBus_row
    unfold VmAirWrapper_jalr.constraints.memoryBus_row
    unfold VmAirWrapper_jalr.constraints.rangeCheckerBus_row
    unfold VmAirWrapper_jalr.constraints.programBus_row
    unfold VmAirWrapper_jalr.constraints.bitwiseBus_row
    have h_nw := @JalR.ValidRows.needs_write_eq_is_valid _ _ air
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
    . simp [h_index, get_instruction_fields_row, List.flatMap_map, JalR_instruction_fields.bitwise]
    . simp [*]

  /-
     ***
     *** JALR
     ***
  -/

  def JalrInput_of_JalR_instruction_fields (row : JalR_instruction_fields) : PureSpec.JalrInput := {
    rd := Transpiler.wrap_to_regidx row.rd_ptr
    rs1_val := BabyBear.toBV32 row.rs1_data
    imm := BitVec.ofNat 12 row.imm
    PC := row.pc.toNat
    : PureSpec.JalrInput
  }

  def JalrOutput_matches_JalR_instruction_fields (row : JalR_instruction_fields) (jalr_output : PureSpec.JalrOutput) : Prop :=
    match jalr_output.rd with
      | .none =>
        row.rd_data = row.prev_rd_data ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.rd_data ∧
        BabyBear.toBV32 row.rd_data = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat ∧
        jalr_output.nextPC = .some row.next_pc.toNat

  /-
     ***
     *** Main specification
     ***
  -/

  def JalR_instruction_fields.spec (row : JalR_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode = 565 ∧
      JalrOutput_matches_JalR_instruction_fields
        row
        (PureSpec.execute_JALR_pure (JalrInput_of_JalR_instruction_fields row))
    )

  lemma jalr_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_jalr FBB ExtF)
    (row : ℕ)
    (row_in_range : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_constraints : VmAirWrapper_jalr.constraints.allHold air row row_in_range)
    (h_bus_wellformedness : VmAirWrapper_jalr.constraints.wf_propertiesToAssumePerRow air row)
  :
    ¬Transpiler.wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [Transpiler.wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_pc_bound := Transpiler.pc_bound_of_some h_transpile.1
    rw [VmAirWrapper_jalr.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_jalr_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨ c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 ⟩ := h_constraints
    simp_all
    obtain ⟨ imm, rd, rs1, h_instruction, h_rd ⟩ := Transpiler.transpiler_opcode_565 h_transpile.1 h_transpile.2.2.2.1
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
  theorem jalr_spec [Field ExtF]
    (air : Valid_VmAirWrapper_jalr FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_jalr.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_jalr.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List JalR_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall JalR_instruction_fields.spec
  := by
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl

    have h_interactions := VmAirWrapper_jalr.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    use get_instruction_fields air
    split_ands
    . exact jalr_buses_spec air h_constraints h_bus_wellformedness
    . apply List.forall_iff_forall_mem.mpr
      intro instruction_fields h_instruction_fields
      unfold JalR_instruction_fields.spec
      simp [get_instruction_fields] at h_instruction_fields
      obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
      rewrite [←h_fields]; clear h_fields

      intro h_is_valid
      specialize h_constraints ⟨ row, by omega ⟩
      specialize h_bus_axioms row (by omega)
      specialize h_bus_wellformedness row (by omega)

      simp
        [JalrOutput_matches_JalR_instruction_fields,
         PureSpec.execute_JALR_pure,
         JalrInput_of_JalR_instruction_fields,
         -Fin.toNat_eq_val
        ]
      repeat rw [Fin.toNat_eq_val]

      simp [get_instruction_fields_row] at h_is_valid ⊢

      have ⟨ jspec_pc, jspec_rd ⟩ :=
        JalR.ValidRows.spec_jalr
          ExtF
          air
          row
          (by omega)
          h_constraints
          h_bus_axioms
          h_bus_wellformedness
          (by simp [VmAirWrapper_jalr_constraint_and_interaction_simplification]; assumption)

      obtain ⟨ h_rd_nz, ⟨ rd', eq_rd' ⟩⟩ := jalr_rd_properties air row (by omega) h_is_valid h_constraints h_bus_wellformedness
      simp [get_instruction_fields_row] at h_rd_nz eq_rd'
      simp [eq_rd'] at h_rd_nz

      have h_nw := @JalR.ValidRows.needs_write_eq_is_valid _ _ air row (by omega) h_constraints h_bus_wellformedness

      simp [h_is_valid, VmAirWrapper_jalr_constraint_and_interaction_simplification, and_assoc] at h_bus_axioms
      obtain ⟨ ub_pc, al_pc, ub_ts, ub_npc, al_npc, ub_nts ⟩ := h_bus_axioms
      simp [h_is_valid, VmAirWrapper_jalr_constraint_and_interaction_simplification] at h_bus_wellformedness
      obtain ⟨ h_mem, h_range, h_prog, h_bit ⟩ := h_bus_wellformedness
      simp [*] at h_mem h_range h_bit

      have hb1 :
        BitVec.ofBool
          (U32.toBV #v[(air.core.rs1_data_0 row 0).val,
                       (air.core.rs1_data_1 row 0).val,
                       (air.core.rs1_data_2 row 0).val,
                       (air.core.rs1_data_3 row 0).val] +
            BitVec.signExtend 32 (BitVec.ofNat 12 (air.core.imm row 0)))[1] = 0#1
      := by
        trans
          BitVec.ofBool
          (4294967294#32 &&&
            (U32.toBV #v[(air.core.rs1_data_0 row 0).val,
                         (air.core.rs1_data_1 row 0).val,
                         (air.core.rs1_data_2 row 0).val,
                         (air.core.rs1_data_3 row 0).val] +
             BitVec.signExtend 32 (BitVec.ofNat 12 (air.core.imm row 0))))[1]
        . simp
        . clear *- ub_npc al_npc jspec_rd
          rw [← jspec_rd]
          simp [← BitVec.toNat_inj, BitVec.ofNat, -BitVec.getElem_ofFin]
          rw [BitVec.getElem_ofFin]
          simp
          rw [Nat.mod_eq_of_lt (by omega)]
          simp [Nat.testBit_eq_decide_div_mod_eq]
          obtain ⟨ x, eq_x ⟩ : ∃ x, x = air.core.to_pc row 0 := by simp
          rw [← eq_x] at al_npc ⊢
          grind

      simp [*]

      split
      case h_1 w h_if =>
        simp [*] at h_if
        rw [← hb1] at h_if
        exfalso
        apply h_if
        rfl
      case h_2 w rd rd_val h_if =>
        simp at h_if
        obtain ⟨ ⟨ x, eq_rd ⟩, eq_rd_val ⟩ := h_if
        simp [*, Valid_Rv32JalrCoreAir_4.rd_data]
        split_ands
        . omega
        . simp [← eq_rd_val]
          rw [← jspec_pc]
          simp [*, Valid_Rv32JalrCoreAir_4.rd_data]
          congr
        . simp [← eq_rd]
          simp [Transpiler.wrap_to_regidx, Transpiler.ind, regidx_to_fin]
          rw [mul_comm]; congr
          omega
        . congr

  section RISC_V_equivalence

    open VmAirWrapper_jalr.constraints

    lemma rd_neq_0 [Field ExtF]
      (air : Valid_VmAirWrapper_jalr FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (_h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
    :
      ¬(Transpiler.wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0)
    := by
      have h_transpile := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
      obtain ⟨instr, mult, result, h_transpile⟩ := h_transpile

      have h_op' := Transpiler.transpiler_opcode_565 h_transpile.1 (by simp [h_transpile])
      obtain ⟨ imm, rd, rs1, h_instr, h_nrd ⟩ := h_op'
      subst instr; simp [Transpiler.transpile_op] at h_transpile
      have h_nrd' : ¬ ((rd == regidx.Regidx 0#5) = true) := by obtain ⟨ rd, prd ⟩ := rd; simp at h_nrd prd; interval_cases rd <;> simp at h_nrd ⊢ <;> rfl
      rw [if_neg h_nrd'] at h_transpile
      simp [-Vector.mk_eq, and_assoc] at h_transpile; simp [← h_transpile.2.2.2.1] at h_transpile
      simp [Transpiler.wrap_to_regidx, get_instruction_fields_row, ← h_transpile.2.2.2.2.1, Transpiler.ind, regidx_to_fin]
      rw [← h_transpile.2.2.2.1]
      obtain ⟨ rd, prd ⟩ := rd; simp at h_nrd prd ⊢
      clear *- h_nrd prd
      simp [← BitVec.toNat_inj] at h_nrd
      simp [Transpiler.ind, regidx_to_fin]; omega

    set_option maxHeartbeats 0 in
    lemma chip_bus_hypotheses [Field ExtF]
      (air : Valid_VmAirWrapper_jalr FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
    :
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1 =
      (
        Sail.readReg Register.PC state = EStateM.Result.ok (BitVec.ofNat 32 ↑(air.adapter.from_state.pc row 0)) state ∧
        read_xreg (Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0)) state =
          EStateM.Result.ok (U32.toBV #v[air.core.rs1_data_0 row 0, air.core.rs1_data_1 row 0, air.core.rs1_data_2 row 0, air.core.rs1_data_3 row 0]) state ∧
        read_xreg (Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0)) state =
          EStateM.Result.ok (U32.toBV #v[air.adapter.rd_aux_cols.prev_data_0 row 0, air.adapter.rd_aux_cols.prev_data_1 row 0, air.adapter.rd_aux_cols.prev_data_2 row 0, air.adapter.rd_aux_cols.prev_data_3 row 0]) state)
    := by
      have h_nw := @JalR.ValidRows.needs_write_eq_is_valid _ _ air row (by omega) h_constraints h_bus_wellformedness

      simp [
        bus_effect,
        _executionBus_row,
        _memoryBus_row,
        executionBus_row,
        memoryBus_row,
        h_is_valid,
        h_nw,
        show ((2013265920 : FBB) = -1) by decide,
      ]

      by_cases h_rs1 : Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0) = 0 <;> simp [h_rs1]
      . by_cases h_rd : Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0) = 0 <;> simp [h_rd, and_assoc]
        simp [write_xreg, Sail.writeReg, PreSail.writeReg, cast]
      . simp [write_xreg, Sail.writeReg, PreSail.writeReg, cast]
        by_cases h_rd : Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0) = 0 <;> simp [h_rd, and_assoc]
        . intro h_pc h_rs1
          rw [insert_reg_eq_self (by omega) h_rs1 (val := U32.toBV #v[air.core.rs1_data_0 row 0, air.core.rs1_data_1 row 0, air.core.rs1_data_2 row 0, air.core.rs1_data_3 row 0])]
        . intro h_pc h_rs1
          rw [insert_reg_eq_self (by omega) h_rs1 (val := U32.toBV #v[air.core.rs1_data_0 row 0, air.core.rs1_data_1 row 0, air.core.rs1_data_2 row 0, air.core.rs1_data_3 row 0])]

    set_option maxHeartbeats 0 in
    lemma chip_bus_effect [Field ExtF]
      (air : Valid_VmAirWrapper_jalr FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
      (h_constraints : allHold air row h_row)
      (h_is_valid : air.core.is_valid row 0 = 1)
      (h_bus_wellformedness : wf_propertiesToAssumePerRow air row)
      (h_bus : (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).1)
    :
      let val := U32.toBV #v[(air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 0),
                             (air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 1),
                             (air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 2),
                             (air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 3)]
      let reg_idx := Transpiler.wrap_to_regidx (air.adapter.rd_ptr row 0)
      (bus_effect (_executionBus_row air row) (_memoryBus_row air row) state).2 =
      EStateM.Result.ok
        (ExecutionResult.Retire_Success ())
        { state with
          regs :=
            (state.regs.insert (reg_of_fin reg_idx) ((register_type_reg_of_fin_equiv reg_idx) ▸ val)
            ).insert Register.nextPC (BitVec.ofNat 32 ↑(air.core.to_pc row 0)) }
    := by
      have h_nzd := rd_neq_0 air row h_row h_constraints h_is_valid h_bus_wellformedness
      simp [get_instruction_fields_row] at h_nzd

      have h_nw := @JalR.ValidRows.needs_write_eq_is_valid _ _ air row (by omega) h_constraints h_bus_wellformedness

      have := chip_bus_hypotheses (state := state) air row h_row h_constraints h_is_valid h_bus_wellformedness
      rw [this] at h_bus; clear this
      obtain ⟨ h_pc, h_rs1, h_rs2 ⟩ := h_bus

      simp [
        bus_effect,
        _executionBus_row,
        _memoryBus_row,
        executionBus_row,
        memoryBus_row,
        h_is_valid,
        h_nw,
        h_nzd,
        show ((2013265920 : FBB) = -1) by decide,
        write_xreg,
        Sail.writeReg,
        PreSail.writeReg,
        cast
      ]

      by_cases h_rs1_ptr : Transpiler.wrap_to_regidx (air.adapter.rs1_ptr row 0) = 0 <;> simp [h_rs1_ptr]
      rw [insert_reg_eq_self (by omega) h_rs1 (val := U32.toBV #v[air.core.rs1_data_0 row 0, air.core.rs1_data_1 row 0, air.core.rs1_data_2 row 0, air.core.rs1_data_3 row 0])]

  end RISC_V_equivalence

end Equivalence.JalR
