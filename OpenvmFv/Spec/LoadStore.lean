import Mathlib

import OpenvmFv.Constraints.VmAirWrapper_loadstore

namespace Load

  lemma inv_2
    (core: Valid_LoadStoreCoreAir_4 FBB)
  :
    a * core.inv_2 = 1 ↔ a = 2
  := by
    simp [
      Valid_LoadStoreCoreAir_4.inv_2
    ]
    grind

  lemma inv_65536
    (adapter: Valid_Rv32LoadStoreAdapterAir FBB)
  :
    a * adapter.inv = 1 ↔ a = 65536
  := by
    simp [
      Valid_Rv32LoadStoreAdapterAir.inv
    ]
    grind

  lemma x_mul_x_sub_1_eq_2
    {x: FBB}
    (h_x: x = 0 ∨ x = 1 ∨ x = 2)
  :
    x * (x-1) = 2 ↔ x = 2
  := by
    grind

  lemma needs_write_of_rd_0 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_opcode: air.core.expected_opcode row 0 = 528)
  :
    air.adapter.rd_rs2_ptr row 0 = 0 ↔
    air.adapter.needs_write row 0 = 0
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2 -- get readInstructionBus properties specifically
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ReadInstructionBusEntry.operand_properties
    ] at h_bus_wellformedness
    obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus_wellformedness
    have := Transpiler.transpiler_opcode_528 h_transpile
    simp [h_data.2.2.1, h_opcode] at this
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    obtain
      ⟨h_needs_write, imm, rs1, rd, h_instruction, h_rd⟩ |
      ⟨h_needs_write, imm, rs1, h_instruction⟩
       := this
    . rewrite [
        ←h_data.2.2.2.2.2.2.2.2.1,
        ←h_data.2.2.2.1,
        h_needs_write
      ]
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [
        ←h_transpile.2,
        Transpiler.ind,
        regidx_to_fin
      ]
      obtain ⟨⟨rd: Fin 32⟩⟩ := rd
      clear *- h_rd
      fin_cases rd <;> grind
    . rewrite [
        ←h_data.2.2.2.2.2.2.2.2.1,
        ←h_data.2.2.2.1,
        h_needs_write
      ]
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [
        ←h_transpile.2,
        Transpiler.ind,
        regidx_to_fin
      ]

  lemma needs_write_of_rd_neq_0 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_opcode: air.core.expected_opcode row 0 = 528)
  :
    air.adapter.rd_rs2_ptr row 0 ≠ 0 ↔
    air.adapter.needs_write row 0 = 1
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2 -- get readInstructionBus properties specifically
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ReadInstructionBusEntry.operand_properties
    ] at h_bus_wellformedness
    obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus_wellformedness
    have := Transpiler.transpiler_opcode_528 h_transpile
    simp [h_data.2.2.1, h_opcode] at this
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    obtain
      ⟨h_needs_write, imm, rs1, rd, h_instruction, h_rd⟩ |
      ⟨h_needs_write, imm, rs1, h_instruction⟩
       := this
    . rewrite [
        ←h_data.2.2.2.2.2.2.2.2.1,
        ←h_data.2.2.2.1,
        h_needs_write
      ]
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [
        ←h_transpile.2,
        Transpiler.ind,
        regidx_to_fin
      ]
      obtain ⟨⟨rd: Fin 32⟩⟩ := rd
      clear *- h_rd
      fin_cases rd <;> grind
    . rewrite [
        ←h_data.2.2.2.2.2.2.2.2.1,
        ←h_data.2.2.2.1,
        h_needs_write
      ]
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [
        ←h_transpile.2,
        Transpiler.ind,
        regidx_to_fin
      ]

  lemma imm_sign_of_opcode_528 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_opcode: air.core.expected_opcode row 0 = 528)
  : air.adapter.imm_sign row 0 =
    (BitVec.ofNat 16 (air.adapter.imm row 0)).msb.toNat
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2 -- get readInstructionBus properties specifically
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ReadInstructionBusEntry.operand_properties
    ] at h_bus_wellformedness
    obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus_wellformedness
    have := Transpiler.transpiler_opcode_528 h_transpile
    simp [h_data.2.2.1, h_opcode] at this
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    rewrite [←h_data.2.2.2.2.2.2.2.2.2]
    obtain
      ⟨h_needs_write, imm, rs1, rd, h_instruction, h_rd⟩ |
      ⟨h_needs_write, imm, rs1, h_instruction⟩
       := this
    all_goals {
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      rewrite [←h_data.2.2.2.2.2.1]
      simp [
        ←h_transpile.2,
        Transpiler.sign_of,
        Transpiler.utof,
        Transpiler.sign_extend_16
      ]
      rewrite [Nat.mod_eq_of_lt]
      . have : imm.msb = (BitVec.signExtend 16 imm).msb := by bv_decide
        simp [this]
      . omega
    }

  lemma opcode_flag_0_boolean[Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
  : air.core.opcode_flags row 0 0 = 0 ∨
    air.core.opcode_flags row 0 0 = 1
  := by
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      _,
      _,
      h_flag_le_2,
      _
    ⟩ := h_constraints
    dsimp [Valid_LoadStoreCoreAir_4.opcode_flags]
    obtain h_flag | h_flag | h_flag := h_flag_le_2
    . simp [h_flag]
    . simp [h_flag]
    . simp [h_flag, Valid_LoadStoreCoreAir_4.inv_2]

  lemma opcode_flag_1_boolean[Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
  : air.core.opcode_flags row 0 1 = 0 ∨
    air.core.opcode_flags row 0 1 = 1
  := by
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      _,
      _,
      _,
      h_flag_le_2,
      _
    ⟩ := h_constraints
    dsimp [Valid_LoadStoreCoreAir_4.opcode_flags]
    obtain h_flag | h_flag | h_flag := h_flag_le_2
    . simp [h_flag]
    . simp [h_flag]
    . simp [h_flag, Valid_LoadStoreCoreAir_4.inv_2]

  lemma opcode_flag_2_boolean[Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
  : air.core.opcode_flags row 0 2 = 0 ∨
    air.core.opcode_flags row 0 2 = 1
  := by
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      _,
      _,
      _,
      _,
      h_flag_le_2,
      _
    ⟩ := h_constraints
    dsimp [Valid_LoadStoreCoreAir_4.opcode_flags]
    obtain h_flag | h_flag | h_flag := h_flag_le_2
    . simp [h_flag]
    . simp [h_flag]
    . simp [h_flag, Valid_LoadStoreCoreAir_4.inv_2]

  lemma opcode_flag_3_boolean[Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
  : air.core.opcode_flags row 0 3 = 0 ∨
    air.core.opcode_flags row 0 3 = 1
  := by
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      _,
      _,
      _, _, _,
      h_flag_le_2,
      _
    ⟩ := h_constraints
    dsimp [Valid_LoadStoreCoreAir_4.opcode_flags]
    obtain h_flag | h_flag | h_flag := h_flag_le_2
    . simp [h_flag]
    . simp [h_flag]
    . simp [h_flag, Valid_LoadStoreCoreAir_4.inv_2]

  lemma opcode_flag_4_boolean[Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
  : air.core.opcode_flags row 0 4 = 0 ∨
    air.core.opcode_flags row 0 4 = 1 ∨
    air.core.opcode_flags row 0 4 = 2 ∨
    air.core.opcode_flags row 0 4 = 4
  := by
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      _,
      _,
      h_flag_0_le_2, _, _, _,
      h_flag_4_le_2,
      _
    ⟩ := h_constraints
    dsimp [Valid_LoadStoreCoreAir_4.opcode_flags]
    obtain h_flag_4 | h_flag_4 | h_flag_4 := h_flag_4_le_2
    all_goals obtain h_flag_0 | h_flag_0 | h_flag_0 := h_flag_0_le_2
    all_goals simp [h_flag_0, h_flag_4, Fin.isValue]
    all_goals decide

  lemma opcode_when_of_expected_opcode [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (opcode: Fin 14)
  :
    air.core.opcode_when row 0 [opcode] = if opcode = 0 then 1 else 0
  := by
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      h_interactions,
      h_is_valid_boolean,
      h_flag_0_le_2,
      h_flag_1_le_2,
      h_flag_2_le_2,
      h_flag_3_le_2,
      h_sum_le_2,
      h_sum_1_or_2_of_is_valid,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _
    ⟩ := h_constraints
    simp [h_is_valid] at *
    simp [Valid_LoadStoreCoreAir_4.sum] at h_sum_1_or_2_of_is_valid
    simp [
      Valid_LoadStoreCoreAir_4.opcode_when,
      Valid_LoadStoreCoreAir_4.opcode_flags,
      Valid_LoadStoreCoreAir_4.sum
    ]
    simp [
      Valid_LoadStoreCoreAir_4.expected_opcode,
      Valid_LoadStoreCoreAir_4.opcode_when,
      Valid_LoadStoreCoreAir_4.opcode_flags,
      Valid_LoadStoreCoreAir_4.sum
    ] at h_opcode
    obtain h_flag_0 | h_flag_0 | h_flag_0 := h_flag_0_le_2
    all_goals obtain h_flag_1 | h_flag_1 | h_flag_1 := h_flag_1_le_2
    all_goals obtain h_flag_2 | h_flag_2 | h_flag_2 := h_flag_2_le_2
    all_goals obtain h_flag_3 | h_flag_3 | h_flag_3 := h_flag_3_le_2
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3] at h_sum_1_or_2_of_is_valid
    all_goals simp at h_sum_1_or_2_of_is_valid
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3, Valid_LoadStoreCoreAir_4.inv_2.eq_def] at h_opcode
    all_goals simp at h_opcode
    rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3, Valid_LoadStoreCoreAir_4.inv_2.eq_def]
    dsimp
    fin_cases opcode <;> decide

  lemma expected_load_val_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.expected_load_val row 0 =
    λ idx => match idx with
    | 0 => air.core.read_data_0 row 0
    | 1 => air.core.read_data_1 row 0
    | 2 => air.core.read_data_2 row 0
    | 3 => air.core.read_data_3 row 0
  := by
    unfold Valid_LoadStoreCoreAir_4.expected_load_val
    funext idx
    have := opcode_when_of_expected_opcode air row h_opcode h_row h_constraints h_is_valid
    simp [Valid_LoadStoreCoreAir_4.opcode_when] at this ⊢
    simp [
      this,
      LS.LoadBu0, LS.LoadBu1, LS.LoadBu2, LS.LoadBu3,
      LS.LoadHu0, LS.LoadHu2
    ]
    rfl

  lemma expected_store_val_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (idx: Fin 4)
  :
    air.core.expected_store_val row 0 idx = 0
  := by
    unfold Valid_LoadStoreCoreAir_4.expected_store_val
    have := opcode_when_of_expected_opcode air row h_opcode h_row h_constraints h_is_valid
    simp [Valid_LoadStoreCoreAir_4.opcode_when] at this ⊢
    simp [
      this,
      LS.StoreW0, LS.StoreH0, LS.StoreB0,
      LS.StoreB1,
      LS.StoreH2, LS.StoreB2,
      LS.StoreB3
    ]
    fin_cases idx <;> rfl

  lemma expected_val_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.expected_val row 0 =
    λ idx => match idx with
    | 0 => air.core.read_data_0 row 0
    | 1 => air.core.read_data_1 row 0
    | 2 => air.core.read_data_2 row 0
    | 3 => air.core.read_data_3 row 0
  := by
    unfold Valid_LoadStoreCoreAir_4.expected_val
    funext idx
    rewrite [
      expected_store_val_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid idx,
      expected_load_val_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    ]
    simp

  lemma load_shift_amount_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.load_shift_amount row 0 = 0
  := by
    unfold Valid_LoadStoreCoreAir_4.load_shift_amount
    have := opcode_when_of_expected_opcode air row h_opcode h_row h_constraints h_is_valid
    simp [Valid_LoadStoreCoreAir_4.opcode_when] at this ⊢
    simp [this]

  lemma store_shift_amount_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.store_shift_amount row 0 = 0
  := by
    unfold Valid_LoadStoreCoreAir_4.store_shift_amount
    have := opcode_when_of_expected_opcode air row h_opcode h_row h_constraints h_is_valid
    simp [Valid_LoadStoreCoreAir_4.opcode_when] at this ⊢
    simp [this]

  -- constraint 0 is superseded by h_is_valid

  -- constraint 1
  lemma flags_0_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.core.flags_0 row 0 = 2
  := by
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      h_interactions,
      h_is_valid_boolean,
      h_flag_0_le_2,
      h_flag_1_le_2,
      h_flag_2_le_2,
      h_flag_3_le_2,
      h_sum_le_2,
      h_sum_1_or_2_of_is_valid,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _
    ⟩ := h_constraints
    simp [h_is_valid] at *
    simp [Valid_LoadStoreCoreAir_4.sum] at h_sum_1_or_2_of_is_valid
    simp [
      Valid_LoadStoreCoreAir_4.expected_opcode,
      Valid_LoadStoreCoreAir_4.opcode_when,
      Valid_LoadStoreCoreAir_4.opcode_flags,
      Valid_LoadStoreCoreAir_4.sum
    ] at h_opcode
    obtain h_flag_0 | h_flag_0 | h_flag_0 := h_flag_0_le_2
    all_goals obtain h_flag_1 | h_flag_1 | h_flag_1 := h_flag_1_le_2
    all_goals obtain h_flag_2 | h_flag_2 | h_flag_2 := h_flag_2_le_2
    all_goals obtain h_flag_3 | h_flag_3 | h_flag_3 := h_flag_3_le_2
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3] at h_sum_1_or_2_of_is_valid
    all_goals simp at h_sum_1_or_2_of_is_valid
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3, Valid_LoadStoreCoreAir_4.inv_2.eq_def] at h_opcode
    all_goals simp at h_opcode
    simp [h_flag_0]

  --constraint 2
  lemma flags_1_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.core.flags_1 row 0 = 0
  := by
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      h_interactions,
      h_is_valid_boolean,
      h_flag_0_le_2,
      h_flag_1_le_2,
      h_flag_2_le_2,
      h_flag_3_le_2,
      h_sum_le_2,
      h_sum_1_or_2_of_is_valid,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _
    ⟩ := h_constraints
    simp [h_is_valid] at *
    simp [Valid_LoadStoreCoreAir_4.sum] at h_sum_1_or_2_of_is_valid
    simp [
      Valid_LoadStoreCoreAir_4.expected_opcode,
      Valid_LoadStoreCoreAir_4.opcode_when,
      Valid_LoadStoreCoreAir_4.opcode_flags,
      Valid_LoadStoreCoreAir_4.sum
    ] at h_opcode
    obtain h_flag_0 | h_flag_0 | h_flag_0 := h_flag_0_le_2
    all_goals obtain h_flag_1 | h_flag_1 | h_flag_1 := h_flag_1_le_2
    all_goals obtain h_flag_2 | h_flag_2 | h_flag_2 := h_flag_2_le_2
    all_goals obtain h_flag_3 | h_flag_3 | h_flag_3 := h_flag_3_le_2
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3] at h_sum_1_or_2_of_is_valid
    all_goals simp at h_sum_1_or_2_of_is_valid
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3, Valid_LoadStoreCoreAir_4.inv_2.eq_def] at h_opcode
    all_goals simp at h_opcode
    simp [h_flag_1]

  -- constraint 3
  lemma flags_2_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.core.flags_2 row 0 = 0
  := by
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      h_interactions,
      h_is_valid_boolean,
      h_flag_0_le_2,
      h_flag_1_le_2,
      h_flag_2_le_2,
      h_flag_3_le_2,
      h_sum_le_2,
      h_sum_1_or_2_of_is_valid,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _
    ⟩ := h_constraints
    simp [h_is_valid] at *
    simp [Valid_LoadStoreCoreAir_4.sum] at h_sum_1_or_2_of_is_valid
    simp [
      Valid_LoadStoreCoreAir_4.expected_opcode,
      Valid_LoadStoreCoreAir_4.opcode_when,
      Valid_LoadStoreCoreAir_4.opcode_flags,
      Valid_LoadStoreCoreAir_4.sum
    ] at h_opcode
    obtain h_flag_0 | h_flag_0 | h_flag_0 := h_flag_0_le_2
    all_goals obtain h_flag_1 | h_flag_1 | h_flag_1 := h_flag_1_le_2
    all_goals obtain h_flag_2 | h_flag_2 | h_flag_2 := h_flag_2_le_2
    all_goals obtain h_flag_3 | h_flag_3 | h_flag_3 := h_flag_3_le_2
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3] at h_sum_1_or_2_of_is_valid
    all_goals simp at h_sum_1_or_2_of_is_valid
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3, Valid_LoadStoreCoreAir_4.inv_2.eq_def] at h_opcode
    all_goals simp at h_opcode
    simp [h_flag_2]

  -- constraint 4
  lemma flags_3_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.core.flags_3 row 0 = 0
  := by
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      h_interactions,
      h_is_valid_boolean,
      h_flag_0_le_2,
      h_flag_1_le_2,
      h_flag_2_le_2,
      h_flag_3_le_2,
      h_sum_le_2,
      h_sum_1_or_2_of_is_valid,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _,
      _
    ⟩ := h_constraints
    simp [h_is_valid] at *
    simp [Valid_LoadStoreCoreAir_4.sum] at h_sum_1_or_2_of_is_valid
    simp [
      Valid_LoadStoreCoreAir_4.expected_opcode,
      Valid_LoadStoreCoreAir_4.opcode_when,
      Valid_LoadStoreCoreAir_4.opcode_flags,
      Valid_LoadStoreCoreAir_4.sum
    ] at h_opcode
    obtain h_flag_0 | h_flag_0 | h_flag_0 := h_flag_0_le_2
    all_goals obtain h_flag_1 | h_flag_1 | h_flag_1 := h_flag_1_le_2
    all_goals obtain h_flag_2 | h_flag_2 | h_flag_2 := h_flag_2_le_2
    all_goals obtain h_flag_3 | h_flag_3 | h_flag_3 := h_flag_3_le_2
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3] at h_sum_1_or_2_of_is_valid
    all_goals simp at h_sum_1_or_2_of_is_valid
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3, Valid_LoadStoreCoreAir_4.inv_2.eq_def] at h_opcode
    all_goals simp at h_opcode
    simp [h_flag_3]

  lemma sum_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : VmAirWrapper_loadstore.constraints.constraint_5 air row ↔
    air.core.sum row 0 = 2
  := by
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
    simp [Valid_LoadStoreCoreAir_4.sum]
    rewrite [
      flags_0_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      flags_1_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      flags_2_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      flags_3_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    ]
    simp

  -- constraint 6 has no extra meaning over constraint 5 in these circumstances

  -- constraint 7
  lemma is_load_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.is_load row 0 = 1
  := by
    have := opcode_when_of_expected_opcode air row h_opcode h_row h_constraints h_is_valid
    simp [Valid_LoadStoreCoreAir_4.opcode_when] at this ⊢
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_7_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_7] at h_constraints
    rewrite [h_constraints.2.2.2.2.2.2.2.2.1]
    simp [Valid_LoadStoreCoreAir_4.opcode_when] at this ⊢
    simp [this]

  -- constraint 8 has nothing extra when is_valid is 1

  -- constraint 9
  lemma write_data_0_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.core.write_data_0 row 0 =
    air.core.read_data_0 row 0
  := by
    have := expected_val_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_9_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_9] at h_constraints
    rewrite [h_constraints.2.2.2.2.2.2.2.2.2.2.1]
    simp [this]

  -- constraint 10
  lemma write_data_1_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.core.write_data_1 row 0 =
    air.core.read_data_1 row 0
  := by
    have := expected_val_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_10_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_10] at h_constraints
    rewrite [h_constraints.2.2.2.2.2.2.2.2.2.2.2.1]
    simp [this]

  -- constraint 11
  lemma write_data_2_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.core.write_data_2 row 0 =
    air.core.read_data_2 row 0
  := by
    have := expected_val_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_11_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_11] at h_constraints
    rewrite [h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.1]
    simp [this]

  -- constraint 12
  lemma write_data_3_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.core.write_data_3 row 0 =
    air.core.read_data_3 row 0
  := by
    have := expected_val_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_12_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_12] at h_constraints
    rewrite [h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    simp [this]

  -- constraint 13 is already simplified
  -- constraint 14 gives nothing when is_valid is 1
  -- constraint 15 gives nothing when is_load is 1
  -- constraint 16 is subsumed by the readInstruction bus assumptions

  -- constraint 17
  lemma rs1_timestamp_diff_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.adapter.from_state.timestamp row 0 - air.adapter.rs1_aux_cols.base.prev_timestamp row 0 - 1 =
      air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072
  := by
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_17_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_17] at h_constraints
    have := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rewrite [h_is_valid] at this
    clear *- this
    grind

  -- constraint 18
  lemma carry_boolean_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.adapter.carry row 0 = 0 ∨
    air.adapter.carry row 0 = 1
  := by
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_18_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_18] at h_constraints
    have := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rewrite [h_is_valid] at this
    clear *- this
    grind

  -- constraint 19
  lemma imm_sign_boolean_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.adapter.imm_sign row 0 = 0 ∨
    air.adapter.imm_sign row 0 = 1
  := by
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_19_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_19] at h_constraints
    have := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rewrite [h_is_valid] at this
    clear *- this
    grind

  -- constraint 20
  lemma carry'_boolean_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.adapter.carry' row 0 = 0 ∨
    air.adapter.carry' row 0 = 1
  := by
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_20_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_20] at h_constraints
    have := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rewrite [h_is_valid] at this
    clear *- this
    grind

  -- constraint 21
  lemma mem_as_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.adapter.mem_as row 0 = 0 ∨
    air.adapter.mem_as row 0 = 1 ∨
    air.adapter.mem_as row 0 = 2
  := by
    have h_is_load := is_load_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_21_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_21] at h_constraints
    have := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simp [
      Valid_VmAirWrapper_loadstore.is_store,
      h_is_valid,
      h_is_load,
      or_assoc
    ] at this
    exact this

  -- constraint 22 does nothing when is_valid is 1

  -- constraint 23
  lemma read_data_timestamp_diff_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.adapter.from_state.timestamp row 0 + 1 - air.adapter.read_data_aux.base.prev_timestamp row 0 - 1 =
      air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072
  := by
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_23_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_23] at h_constraints
    have := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rewrite [h_is_valid] at this
    clear *- this
    grind

  -- constraint 24
  lemma write_timestamp_diff_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rd_rs2_ptr row 0 ≠ 0 →
    air.adapter.from_state.timestamp row 0 + 2 - air.adapter.write_base_aux.prev_timestamp row 0 - 1 =
      air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_1 row 0 * 131072
  := by
    unfold VmAirWrapper_loadstore.constraints.allHold at h_constraints
    unfold VmAirWrapper_loadstore.constraints.extracted_row_constraint_list at h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.constraint_24_of_extraction] at h_constraints
    dsimp only [List.Forall, VmAirWrapper_loadstore.constraints.constraint_24] at h_constraints
    have := h_constraints.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    intro h_rd
    rewrite [(needs_write_of_rd_neq_0 air row h_bus_wellformedness h_is_valid h_opcode).mp h_rd] at this
    simp at this
    exact this

  lemma is_store_of_opcode_528 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.is_store row 0 = 0
  := by
    have h_is_load := is_load_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    unfold Valid_VmAirWrapper_loadstore.is_store
    simp [h_is_valid, h_is_load]

  lemma shift_amount_of_opcode_528 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.shift_amount row 0 = 0
  := by
    have h_load_shift_amount := load_shift_amount_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_store_shift_amount := store_shift_amount_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    unfold Valid_VmAirWrapper_loadstore.shift_amount
    simp [h_load_shift_amount, h_store_shift_amount]

  lemma read_as_of_opcode_528 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.read_as row 0 = air.adapter.mem_as row 0
  := by
    have h_is_load := is_load_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    unfold Valid_VmAirWrapper_loadstore.read_as
    simp [h_is_load]

  lemma read_ptr_of_opcode_528 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.read_ptr row 0 = air.adapter.mem_ptr row 0
  := by
    unfold Valid_VmAirWrapper_loadstore.read_ptr
    have h_is_load := is_load_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_load_shift_amount := load_shift_amount_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    simp [h_is_load, h_load_shift_amount]

  lemma write_as_of_opcode_528 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.write_as row 0 = 1
  := by
    unfold Valid_VmAirWrapper_loadstore.write_as
    have h_is_load := is_load_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    simp [h_is_load]

  lemma write_ptr_of_opcode_528 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.write_ptr row 0 = air.adapter.rd_rs2_ptr row 0
  := by
    unfold Valid_VmAirWrapper_loadstore.write_ptr
    have h_is_load := is_load_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_store_shift_amount := store_shift_amount_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    simp [h_is_load, h_store_shift_amount]

  lemma rangeCheckerBus_row_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : VmAirWrapper_loadstore.constraints.rangeCheckerBus_row air row = [
    (1, [air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (1, [air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
    (1, [air.adapter.mem_ptr_limbs_0 row 0 * 1509949441, 14]),
    (1, [air.adapter.mem_ptr_limbs_1 row 0, 13]),
    (1, [air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (1, [air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
    (if air.adapter.rd_rs2_ptr row 0 = 0 then 0 else 1, [air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (if air.adapter.rd_rs2_ptr row 0 = 0 then 0 else 1, [air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_1 row 0, 12])
  ] := by
    unfold VmAirWrapper_loadstore.constraints.rangeCheckerBus_row
    simp [
      h_is_valid,
      shift_amount_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    ]
    split_ifs with h_rd
    . simp [(needs_write_of_rd_0 air row h_bus_wellformedness h_is_valid h_opcode).mp h_rd]
    . simp [(needs_write_of_rd_neq_0 air row h_bus_wellformedness h_is_valid h_opcode).mp h_rd]

  lemma mem_ptr_limbs_0_range_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.adapter.mem_ptr_limbs_0 row 0 < 2^16
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      shift_amount_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    ] at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.1
    clear *- h_bus_wellformedness

    have : (1509949441: FBB) = 4⁻¹ := eq_inv_of_mul_eq_one_left rfl

    rewrite [this] at h_bus_wellformedness
    clear this

    rewrite [show 16384 = (16384: FBB).val by simp, ←Fin.lt_def] at h_bus_wellformedness
    rewrite [
      show air.adapter.mem_ptr_limbs_0 row 0 = air.adapter.mem_ptr_limbs_0 row 0 * 4⁻¹ * 4 by simp
    ]
    grind

  lemma mem_ptr_limbs_1_range_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.adapter.mem_ptr_limbs_1 row 0 < 2^13
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      shift_amount_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    ] at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
    grind

  lemma rs1_data_0_range [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rs1_data_0 row 0 < 256
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920: FBB) = -1 by decide
    ] at h_bus_wellformedness
    rewrite [
      show 256 = (256:FBB).val by decide,
    ] at h_bus_wellformedness
    exact Fin.lt_def.mpr h_bus_wellformedness.1.2.1

  lemma rs1_data_1_range [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rs1_data_1 row 0 < 256
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920: FBB) = -1 by decide
    ] at h_bus_wellformedness
    rewrite [
      show 256 = (256:FBB).val by decide,
    ] at h_bus_wellformedness
    exact Fin.lt_def.mpr h_bus_wellformedness.1.2.2.1

  lemma rs1_data_2_range [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rs1_data_2 row 0 < 256
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920: FBB) = -1 by decide
    ] at h_bus_wellformedness
    rewrite [
      show 256 = (256:FBB).val by decide,
    ] at h_bus_wellformedness
    exact Fin.lt_def.mpr h_bus_wellformedness.1.2.2.2.1

  lemma rs1_data_3_range [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rs1_data_3 row 0 < 256
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920: FBB) = -1 by decide
    ] at h_bus_wellformedness
    rewrite [
      show 256 = (256:FBB).val by decide,
    ] at h_bus_wellformedness
    exact Fin.lt_def.mpr h_bus_wellformedness.1.2.2.2.2

  lemma rs1_lower_half_range [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rs1_data_0 row 0 + air.adapter.rs1_data_1 row 0 * 256 < 65536
  := by
    have h_data_0 := rs1_data_0_range air row h_is_valid h_bus_wellformedness
    have h_data_1 := rs1_data_1_range air row h_is_valid h_bus_wellformedness
    clear *- h_data_0 h_data_1
    grind

  lemma imm_range_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.imm row 0 < 65536
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2 -- get readInstructionBus properties specifically
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ReadInstructionBusEntry.operand_properties
    ] at h_bus_wellformedness
    obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus_wellformedness
    have := Transpiler.transpiler_opcode_528 h_transpile
    simp [h_data.2.2.1, h_opcode] at this
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    obtain
      ⟨h_needs_write, imm, rs1, rd, h_instruction, h_rd⟩ |
      ⟨h_needs_write, imm, rs1, h_instruction⟩
      := this
    all_goals {
      rewrite [←h_data.2.2.2.2.2.1]
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [
        ←h_transpile.2,
        Transpiler.sign_extend_16,
        Transpiler.utof,
        Fin.lt_def
      ]
      rewrite [Nat.mod_eq_of_lt (by omega)]
      omega
    }

lemma imm_extend_range_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.imm_extended_limb row 0 < 65536
  := by
    have := imm_sign_boolean_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    rw [← Rv32LoadStoreAdapterAir.imm_extended_limb_def]
    omega

  lemma imm_sign_extend_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : BitVec.signExtend 32 (BitVec.ofNat 16 (air.adapter.imm row 0)) =
    BitVec.ofNat 16 (air.adapter.imm_extended_limb row 0) ++
    BitVec.ofNat 16 (air.adapter.imm row 0)
  := by
    simp [
      Valid_Rv32LoadStoreAdapterAir.imm_extended_limb,
      imm_sign_of_opcode_528 air row h_bus_wellformedness h_is_valid h_opcode,
      Fin.val_mul
    ]
    rewrite [Nat.mod_eq_of_lt]
    . simp [BitVec.ofNat_mul]
      by_cases h_msb: (BitVec.ofNat 16 ↑(air.adapter.imm row 0)).msb
      all_goals {
        simp [h_msb]
        bv_decide
      }
    . cases (BitVec.ofNat 16 ↑(air.adapter.imm row 0)).msb <;> simp

  set_option maxHeartbeats 1_000_000_000 in
  example [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : BitVec.ofNat 32 (air.adapter.mem_ptr row 0) =
    BitVec.signExtend 32 (BitVec.ofNat 16 (air.adapter.imm row 0)) +
    U32.toBV #v[
      (air.adapter.rs1_data_0 row 0).val,
      (air.adapter.rs1_data_1 row 0).val,
      (air.adapter.rs1_data_2 row 0).val,
      (air.adapter.rs1_data_3 row 0).val
    ]
  := by
    have h_carry_def := Rv32LoadStoreAdapterAir.carry_def air.adapter row 0
    have h_carry'_def := Rv32LoadStoreAdapterAir.carry'_def air.adapter row 0
    have h_rs1_data_0 := rs1_data_0_range air row h_is_valid h_bus_wellformedness
    have h_rs1_data_1 := rs1_data_1_range air row h_is_valid h_bus_wellformedness
    have h_rs1_data_2 := rs1_data_2_range air row h_is_valid h_bus_wellformedness
    have h_rs1_data_3 := rs1_data_3_range air row h_is_valid h_bus_wellformedness
    have h_imm_range := imm_range_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
    have h_imm_ext_range := imm_extend_range_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    have h_mem_ptr_0_range := mem_ptr_limbs_0_range_of_opcode_528 air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
    have h_mem_ptr_1_range := mem_ptr_limbs_1_range_of_opcode_528 air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
    simp at h_mem_ptr_0_range h_mem_ptr_1_range
    have b_carry := carry_boolean_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have b_carry' := carry'_boolean_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    rw [← Rv32LoadStoreAdapterAir.mem_ptr_def, imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness]
    simp [U32.toBV]
    rw [← BitVec.toNat_inj]
    repeat rw [BitVec.toNat_add]
    repeat rw [BitVec.toNat_mul]
    simp
    rw [Nat.mod_eq_of_lt (by omega)]
    repeat (rw [BitVec.toNat_append]; simp; rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)])
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
    repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)]
    repeat rw [Nat.shiftLeft_eq_mul_pow]
    ring_nf
    trans
      (((air.adapter.limbs_01 row 0).val + (air.adapter.imm row 0).val)) +
       ((air.adapter.limbs_23 row 0).val + (air.adapter.imm_extended_limb row 0).val) * 65536) % 4294967296
    . have ub_l01 : air.adapter.limbs_01 row 0 < 65536
        := by rw [← Rv32LoadStoreAdapterAir.limbs_01_def]; grind
      have ub_l23 : air.adapter.limbs_23 row 0 < 65536
        := by rw [← Rv32LoadStoreAdapterAir.limbs_23_def]; grind
      clear h_rs1_data_0 h_rs1_data_1 h_rs1_data_2 h_rs1_data_3
            h_constraints h_bus_wellformedness h_is_valid h_row h_opcode
      rw [← h_carry_def] at h_carry'_def
      rcases b_carry with hc | hc <;> rcases b_carry' with hc' | hc' <;> simp_all
      . rw [sub_eq_zero] at h_carry_def h_carry'_def
        symm at h_carry_def h_carry'_def
        simp [h_carry_def, h_carry'_def] at *
        simp [Fin.val_add, Fin.val_mul]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      . rw [sub_eq_zero] at h_carry_def
        replace h_carry'_def := eq_add_of_sub_eq h_carry'_def
        symm at h_carry_def
        simp [Fin.ext_iff, Fin.val_add] at h_carry'_def
        repeat rw [Nat.mod_eq_of_lt (by omega)] at h_carry'_def
        rw [h_carry_def, h_carry'_def]
        ring_nf
        rw [Nat.mod_eq_sub_mod (by omega)]
        omega
      . rw [sub_eq_zero] at h_carry'_def
        replace h_carry_def := eq_add_of_sub_eq h_carry_def
        symm at h_carry'_def
        simp [Fin.ext_iff, Fin.val_add] at h_carry_def
        repeat rw [Nat.mod_eq_of_lt (by omega)] at h_carry_def
        rw [h_carry_def, h_carry'_def]
        ring_nf
        rw [Nat.mod_eq_sub_mod (by omega)]
        omega

    . rw [← Rv32LoadStoreAdapterAir.limbs_01_def, ← Rv32LoadStoreAdapterAir.limbs_23_def]
      simp [Fin.val_add, Fin.val_mul]
      repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      ring_nf




















#exit

  : (air.adapter.mem_ptr row 0).val =
    (BitVec.signExtend 32 (BitVec.ofNat 16 (air.adapter.imm row 0)) +
    (
      BitVec.ofNat 8 (air.adapter.rs1_data_3 row 0) ++
      BitVec.ofNat 8 (air.adapter.rs1_data_2 row 0) ++
      BitVec.ofNat 8 (air.adapter.rs1_data_1 row 0) ++
      BitVec.ofNat 8 (air.adapter.rs1_data_0 row 0)
    )).toNat

    rewrite [show 2013235201 = air.adapter.inv by rfl] at h_carry_def h_carry'_def
    rewrite [←h_carry_def] at h_carry'_def
    have h_carry'_boolean := carry'_boolean_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    simp [
      ←h_carry'_def,
      sub_eq_zero,
      Valid_Rv32LoadStoreAdapterAir.imm_extended_limb,
      inv_65536,
    ] at h_carry'_boolean
    have : (air.adapter.limbs_23 row 0 + air.adapter.imm_sign row 0 * 65535 +
        (air.adapter.limbs_01 row 0 + air.adapter.imm row 0 - air.adapter.mem_ptr_limbs_0 row 0) * air.adapter.inv -
      air.adapter.mem_ptr_limbs_1 row 0 =
    65536) = (air.adapter.limbs_23 row 0 + air.adapter.imm_sign row 0 * 65535 +
        (air.adapter.limbs_01 row 0 + air.adapter.imm row 0 - air.adapter.mem_ptr_limbs_0 row 0) * air.adapter.inv -
      65536 =
    air.adapter.mem_ptr_limbs_1 row 0)
    := by
      grind
    rewrite [this] at h_carry'_boolean; clear this
    simp [show air.adapter.inv ≠ 0 by simp[Valid_Rv32LoadStoreAdapterAir.inv]] at h_carry'_boolean
    have h_carry_boolean := carry_boolean_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    simp [
      ←h_carry_def,
      sub_eq_zero,
      show air.adapter.inv ≠ 0 by simp[Valid_Rv32LoadStoreAdapterAir.inv],
      inv_65536
    ] at h_carry_boolean
    have : (
        air.adapter.limbs_01 row 0 +
        air.adapter.imm row 0 -
        air.adapter.mem_ptr_limbs_0 row 0 =
        65536
      ) = (
        air.adapter.limbs_01 row 0 +
        air.adapter.imm row 0 -
        65536 =
        air.adapter.mem_ptr_limbs_0 row 0
      )
    := by grind
    rewrite [this] at h_carry_boolean; clear this
    simp [
      Valid_Rv32LoadStoreAdapterAir.limbs_01,
      Valid_Rv32LoadStoreAdapterAir.limbs_23
    ] at h_carry_boolean h_carry'_boolean
    simp [
      imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness,
      Valid_Rv32LoadStoreAdapterAir.imm_extended_limb,
      Valid_Rv32LoadStoreAdapterAir.mem_ptr
    ]
    have h_imm_sign_boolean := imm_sign_boolean_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have : (
        (BitVec.setWidth 32 (BitVec.ofNat 16 ↑(air.adapter.imm_sign row 0 * 65535))) * 65536#32 +
        BitVec.setWidth 32 (BitVec.ofNat 16 ↑(air.adapter.imm row 0))
      ) = (
        BitVec.ofNat 16 ↑(air.adapter.imm_sign row 0 * 65535) ++
        BitVec.ofNat 16 ↑(air.adapter.imm row 0)
      )
    := by bv_decide
    rewrite [←this]; clear this
    simp

    ) := by bv_decide
    rewrite [←this]; clear this







  example [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : (air.adapter.mem_ptr_limbs_0 row 0).toNat =
    (BitVec.ofNat 16 (air.adapter.imm row 0) +
    (BitVec.ofNat 8 (air.adapter.rs1_data_1 row 0) ++
    BitVec.ofNat 8 (air.adapter.rs1_data_0 row 0))).toNat
  := by
    have h_carry := carry_boolean_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_rs1_data_0 := rs1_data_0_range air row h_is_valid h_bus_wellformedness
    have h_rs1_data_1 := rs1_data_1_range air row h_is_valid h_bus_wellformedness
    have h_imm_range := imm_range_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
    unfold Valid_Rv32LoadStoreAdapterAir.carry at h_carry
    have :
      BitVec.ofNat 16 (air.adapter.rs1_data_0 row 0 + air.adapter.rs1_data_1 row 0 * 256: FBB) =
      BitVec.ofNat 8 (air.adapter.rs1_data_1 row 0) ++
      BitVec.ofNat 8 (air.adapter.rs1_data_0 row 0)
    := by
      have :
        (BitVec.setWidth 16 (BitVec.ofNat 8 (air.adapter.rs1_data_0 row 0))) +
        (BitVec.setWidth 16 (BitVec.ofNat 8 (air.adapter.rs1_data_1 row 0))) * 256 =
        BitVec.ofNat 8 (air.adapter.rs1_data_1 row 0) ++
        BitVec.ofNat 8 (air.adapter.rs1_data_0 row 0)
      := by bv_decide
      rewrite [←this]; clear this
      rewrite [Fin.val_add, Fin.val_mul]
      simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        BitVec.ofNat_add
      ]
      congr 3
      . rewrite [BitVec.toNat_eq]
        simp
        omega
      . simp
        rw [
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)
        ]
    have h_mem_ptr_0 := mem_ptr_limbs_0_range_of_opcode_528 air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
    simp at h_mem_ptr_0
    obtain h_carry | h_carry := h_carry
    . simp [Valid_Rv32LoadStoreAdapterAir.inv, sub_eq_zero] at h_carry
      rewrite [←h_carry]
      unfold Valid_Rv32LoadStoreAdapterAir.limbs_01
      rewrite [←this]; clear this
      simp
      rewrite [add_comm]
      simp [←h_carry] at h_mem_ptr_0
      rewrite [add_comm] at h_mem_ptr_0
      simp [Valid_Rv32LoadStoreAdapterAir.limbs_01] at h_mem_ptr_0
      rewrite [Nat.mod_eq_of_lt]
      . simp [
          Fin.val_add,
          Fin.val_mul
        ]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      . simp [
          Fin.val_add,
          Fin.val_mul
        ]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        rewrite [Fin.lt_def] at h_mem_ptr_0
        simp at h_mem_ptr_0
        convert h_mem_ptr_0
        grind
    . simp [inv_65536] at h_carry
      apply eq_add_of_sub_eq at h_carry
      have h_carry :
        air.adapter.mem_ptr_limbs_0 row 0 % 65536 =
        (air.adapter.limbs_01 row 0 + air.adapter.imm row 0) % 65536
      := by
        rewrite [
          h_carry,
          Fin.mod_def,
          Fin.mod_def
        ]
        simp
        rewrite [
          Nat.mod_eq_of_lt,
          Fin.val_add,
          @Nat.mod_eq_of_lt _ BB_prime,
          Nat.add_mod
        ]
        simp
        rw [Nat.mod_eq_of_lt]
        . convert h_mem_ptr_0
        . omega
        . convert (Fin.lt_def.mp h_mem_ptr_0)
      simp
      simp [Fin.mod_def] at h_carry
      rewrite [Nat.mod_eq_of_lt] at h_carry
      rewrite [h_carry, Fin.val_add, add_comm]
      rewrite [@Nat.mod_eq_of_lt _ BB_prime]
      . congr 2
        rewrite [←this]
        simp [Valid_Rv32LoadStoreAdapterAir.limbs_01]
        simp [
          Fin.val_add,
          Fin.val_mul
        ]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      . simp [
          Valid_Rv32LoadStoreAdapterAir.limbs_01,
          Fin.val_add,
          Fin.val_mul
        ]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        apply Fin.lt_def.mp at h_rs1_data_0
        apply Fin.lt_def.mp at h_rs1_data_1
        apply Fin.lt_def.mp at h_imm_range
        omega
      . apply Fin.lt_def.mp at h_mem_ptr_0
        convert h_mem_ptr_0


  lemma mem_ptr_eq_rs1_plus_imm_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.mem_ptr row 0 =
    sorry
  := by
    have h_carry := carry_boolean_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_carry' := carry'_boolean_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_imm_sign := imm_sign_of_opcode_528 air row h_bus_wellformedness h_is_valid h_opcode
    unfold Valid_Rv32LoadStoreAdapterAir.carry at h_carry
    unfold Valid_Rv32LoadStoreAdapterAir.carry' at h_carry'
    unfold Valid_Rv32LoadStoreAdapterAir.imm_extended_limb at h_carry'
    unfold Valid_Rv32LoadStoreAdapterAir.mem_ptr
    obtain h_carry | h_carry := h_carry
    . simp [Valid_Rv32LoadStoreAdapterAir.carry, h_carry] at h_carry'
      simp [Valid_Rv32LoadStoreAdapterAir.inv, sub_eq_zero] at h_carry
      rewrite [←h_carry]
      unfold Valid_Rv32LoadStoreAdapterAir.limbs_01
      obtain h_carry' | h_carry' := h_carry'
      . simp [Valid_Rv32LoadStoreAdapterAir.inv, sub_eq_zero] at h_carry'
        rewrite [←h_carry']
        unfold Valid_Rv32LoadStoreAdapterAir.limbs_23
        simp [add_mul, mul_assoc]
        grind
      . simp [
          inv_65536,
          Valid_Rv32LoadStoreAdapterAir.limbs_23
        ] at h_carry'
        apply eq_add_of_sub_eq at h_carry'
        rewrite [add_comm 65536] at h_carry'
        apply sub_eq_of_eq_add at h_carry'
        rewrite [←h_carry']
        simp [sub_mul, add_mul, mul_assoc]

        have h_mem_ptr_0 := mem_ptr_limbs_0_range_of_opcode_528 air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
        have h_mem_ptr_1 := mem_ptr_limbs_1_range_of_opcode_528 air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
        simp [←h_carry, Valid_Rv32LoadStoreAdapterAir.limbs_01] at h_mem_ptr_0
        simp [←h_carry'] at h_mem_ptr_1
        have h_rs1_2_range := rs1_data_2_range air row h_is_valid h_bus_wellformedness
        have h_rs1_3_range := rs1_data_3_range air row h_is_valid h_bus_wellformedness
        have h_imm_sign_boolean := imm_sign_boolean_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
        obtain h_imm_sign_0 | h_imm_sign_1 := h_imm_sign_boolean
        . exfalso
          simp [h_imm_sign_0] at h_mem_ptr_1
          clear *- h_rs1_2_range h_rs1_3_range h_mem_ptr_1
          grind
        simp [h_imm_sign_1, ←add_sub] at h_carry' h_mem_ptr_1 ⊢
        simp [show (2013265920: FBB) = -1 by decide] at h_carry h_carry'
        simp [show (2013200385: FBB) = -65536 by decide]


        done
      done
    . done
    done

  lemma executionBus_row_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : VmAirWrapper_loadstore.constraints.executionBus_row air row = [
      (-1, [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0]),
      (1, [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3])
    ]
  := by
    unfold VmAirWrapper_loadstore.constraints.executionBus_row
    simp [h_is_valid, Valid_VmAirWrapper_loadstore.to_pc]

  lemma memoryBus_row_of_opcode_528 [Field ExtF]
    (air: Valid_VmAirWrapper_loadstore FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 528)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : VmAirWrapper_loadstore.constraints.memoryBus_row air row = sorry
    -- [
    --   (-1,
    --     [
    --       1, air.adapter.rs1_ptr row 0,
    --       air.adapter.rs1_data_0 row 0, air.adapter.rs1_data_1 row 0, air.adapter.rs1_data_2 row 0, air.adapter.rs1_data_3 row 0,
    --       air.adapter.rs1_aux_cols.base.prev_timestamp row 0
    --     ]
    --   ),
    --   (1,
    --     [
    --       1, air.adapter.rs1_ptr row 0,
    --       air.adapter.rs1_data_0 row 0, air.adapter.rs1_data_1 row 0, air.adapter.rs1_data_2 row 0, air.adapter.rs1_data_3 row 0,
    --       air.adapter.from_state.timestamp row 0
    --     ]
    --   ),
    --   (-1,
    --     [
    --       air.adapter.mem_as row 0, air.adapter.mem_ptr row 0,
    --       air.core.read_data_0 row 0, air.core.read_data_1 row 0, air.core.read_data_2 row 0, air.core.read_data_3 row 0,
    --       air.adapter.read_data_aux.base.prev_timestamp row 0
    --     ]
    --   ),
    --   (1,
    --     [
    --       air.adapter.mem_as row 0, air.adapter.mem_ptr row 0,
    --       air.core.read_data_0 row 0, air.core.read_data_1 row 0, air.core.read_data_2 row 0, air.core.read_data_3 row 0,
    --       air.adapter.from_state.timestamp row 0 + 1
    --     ]
    --   ),
    --   (if air.adapter.rd_rs2_ptr row 0 = 0 then 0 else -1,
    --     [
    --       1, air.adapter.rd_rs2_ptr row 0,
    --       air.core.prev_data_0 row 0, air.core.prev_data_1 row 0, air.core.prev_data_2 row 0, air.core.prev_data_3 row 0,
    --       air.adapter.write_base_aux.prev_timestamp row 0
    --     ]
    --   ),
    --   (if air.adapter.rd_rs2_ptr row 0 = 0 then 0 else 1,
    --     [
    --       1, air.adapter.rd_rs2_ptr row 0,
    --       air.core.read_data_0 row 0, air.core.read_data_1 row 0, air.core.read_data_2 row 0, air.core.read_data_3 row 0,
    --       air.adapter.from_state.timestamp row 0 + 2
    --     ]
    --   )
    -- ]
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2 --read instruction bus
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ReadInstructionBusEntry.operand_properties
    ] at h_bus_wellformedness
    obtain ⟨
      instruction,
      multiplicity,
      data,
      h_transpile,
      h_multiplicity,
      h_from_pc,
      h_opcode',
      h_rd,
      h_rs1,
      h_imm,
      h_5,
      h_mem_as,
      h_needs_write,
      h_imm_sign
    ⟩ := h_bus_wellformedness
    have h_instruction := Transpiler.transpiler_opcode_528 h_transpile
    simp [h_opcode', h_opcode] at h_instruction
    unfold VmAirWrapper_loadstore.constraints.memoryBus_row
    simp [
      h_is_valid,
      read_as_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      read_ptr_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      write_as_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      write_ptr_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      write_data_0_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      write_data_1_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      write_data_2_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      write_data_3_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid,
      show (2013265920: FBB) = -1 by grind
    ]
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    obtain
      ⟨h_needs_write', imm, rs1, rd, h_instruction, h_rd'⟩ |
      ⟨h_needs_write', im, rs1, h_instruction⟩ := h_instruction
    all_goals (
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
    )
    . simp [
        ←h_rd,
        ←h_rs1,
        ←h_mem_as,
        ←h_needs_write,
        ←h_transpile.2
      ]
      rewrite [ite_cond_eq_false]

      done
    . done
    -- split_ifs with h_rd
    -- . simp[(needs_write_of_rd_0 air row h_bus_wellformedness h_is_valid h_opcode).mp h_rd]
    --   grind
    -- . simp[(needs_write_of_rd_neq_0 air row h_bus_wellformedness h_is_valid h_opcode).mp h_rd]
    --   grind



end Load
