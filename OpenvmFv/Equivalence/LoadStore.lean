import OpenvmFv.Spec.Load.lw
import OpenvmFv.Spec.Load

namespace Equivalence.LoadStore

  @[ext]
  structure LoadStore_instruction_fields where
    is_valid : FBB

    opcode : FBB

    pc : FBB
    next_pc : FBB

    timestamp : FBB
    next_timestamp : FBB
    rs1_prev_timestamp : FBB
    read_prev_timestamp : FBB
    rd_prev_timestamp : FBB

    rs1 : FBB
    rd : FBB
    imm_lower_half : FBB
    imm_sign : FBB

    -- the value for read and write address space that corresponds to memory
    memory_address_space : FBB

    -- for load, this is the read from memory
    -- for store, it is the read from rs2
    read_address_space : FBB
    read_ptr : FBB
    -- for load this is the write to rd
    -- for store it is the write to memory
    -- in both cases, needs_write is 0 if the write should not occur, 1 if it should
    needs_write : FBB
    write_address_space : FBB
    write_ptr : FBB


    imm : Vector FBB 4
    rs1_val : Vector FBB 4
    prev_read_data : Vector FBB 4
    read_data : Vector FBB 4
    prev_write_data : Vector FBB 4
    write_data : Vector FBB 4

    range_checked_vals : Vector FBB 8

  lemma LoadStore_instruction_fields_eq (a b : LoadStore_instruction_fields)
  :
    a.is_valid = b.is_valid ∧
    a.opcode = b.opcode ∧
    a.pc = b.pc ∧
    a.next_pc = b.next_pc ∧
    a.timestamp = b.timestamp ∧
    a.next_timestamp = b.next_timestamp ∧
    a.rs1_prev_timestamp = b.rs1_prev_timestamp ∧
    a.read_prev_timestamp = b.read_prev_timestamp ∧
    a.rd_prev_timestamp = b.rd_prev_timestamp ∧
    a.rs1 = b.rs1 ∧
    a.rd = b.rd ∧
    a.imm_lower_half = b.imm_lower_half ∧
    a.imm_sign = b.imm_sign ∧
    a.memory_address_space = b.memory_address_space ∧
    a.read_address_space = b.read_address_space ∧
    a.read_ptr = b.read_ptr ∧
    a.needs_write = b.needs_write ∧
    a.write_address_space = b.write_address_space ∧
    a.write_ptr = b.write_ptr ∧
    a.imm = b.imm ∧
    a.rs1_val = b.rs1_val ∧
    a.prev_read_data = b.prev_read_data ∧
    a.read_data = b.read_data ∧
    a.prev_write_data = b.prev_write_data ∧
    a.write_data = b.write_data ∧
    a.range_checked_vals = b.range_checked_vals
      → a = b
  := by
    intro field_eq
    ext <;> grind

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val / 4 % 32, by grind⟩

  structure RVConfig where
    mstatus : BitVec 64
    cur_privielge : Privilege
    plat_clint_base : BitVec 34
    plat_clint_size : BitVec 34
    plat_ram_base : BitVec 34
    plat_ram_size : BitVec 34
    plat_rom_base : BitVec 34
    plat_rom_size : BitVec 34
    htif_tohost_base : Option (BitVec 34)

  def config : RVConfig := {
    mstatus := 0
    cur_privielge := Privilege.Machine
    plat_clint_base := 0
    plat_clint_size := 0
    plat_ram_base := 0
    plat_ram_size := 2^32-1
    plat_rom_base := 0
    plat_rom_size := 0
    htif_tohost_base := .none
  }

  def LwInput_of_LoadStore_instruction_fields (row : LoadStore_instruction_fields) : PureSpec.LwInput := {
    r1 := BitVec.ofFin (wrap_to_regidx row.rs1)
    imm := BabyBear.toBV32 row.imm
    rd := BitVec.ofFin (wrap_to_regidx row.rd)
    r1_val := BabyBear.toBV32 row.rs1_val
    PC := row.pc.toNat
    mstatus := config.mstatus
    cur_privilege := config.cur_privielge
    plat_clint_base := config.plat_clint_base
    plat_clint_size := config.plat_clint_size
    plat_ram_base := config.plat_ram_base
    plat_ram_size := config.plat_ram_size
    plat_rom_base := config.plat_rom_base
    plat_rom_size := config.plat_rom_size
    htif_tohost_base := config.htif_tohost_base
    data0 := row.prev_read_data[0]
    data1 := row.prev_read_data[1]
    data2 := row.prev_read_data[2]
    data3 := row.prev_read_data[3]
    : PureSpec.LwInput
  }

  def LwOutput_matches_LoadStore_instruction_fields (row : LoadStore_instruction_fields) (lw_output : PureSpec.LwOutput) : Prop :=
    BabyBear.isU32 row.imm ∧
    BabyBear.isU32 row.rs1_val ∧
    BabyBear.isU32 row.prev_read_data ∧
    BabyBear.isU32 row.read_data ∧
    (row.needs_write = 1 → BabyBear.isU32 row.prev_write_data) ∧
    (row.needs_write = 1 → BabyBear.isU32 row.write_data) ∧
    lw_output.nextPC = row.next_pc.toNat ∧
    row.read_address_space = row.memory_address_space ∧
    row.write_address_space = 1 ∧
    row.read_ptr.val = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat ∧
    row.write_ptr = row.rd ∧
    row.prev_read_data = row.read_data ∧
    BitVec.signExtend 32 (BitVec.setWidth 12 (BabyBear.toBV32 row.imm)) = BabyBear.toBV32 row.imm ∧
    BabyBear.toBV32 row.imm = BitVec.signExtend 32 (BitVec.ofNat 16 row.imm_lower_half) ∧
    row.imm_sign = (BabyBear.toBV32 row.imm).msb.toNat ∧
    match lw_output.rd with
      | .none =>
        row.rd = 0 ∧
        row.needs_write = 0
      | .some (rd, rd_val) =>
        BabyBear.toBV32 row.write_data = rd_val ∧
        rd.1.toNat * 4 = row.rd.toNat ∧
        row.needs_write = 1

  def LoadStore_instruction_fields.spec (row : LoadStore_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode ∈ Finset.Icc 528 533 ∧
      (row.opcode = 528 →
        LwOutput_matches_LoadStore_instruction_fields
          row
          (PureSpec.execute_LOAD_lw_pure (LwInput_of_LoadStore_instruction_fields row))
      )
    )

  def LoadStore_instruction_fields.execution (row : LoadStore_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def LoadStore_instruction_fields.memory (row : LoadStore_instruction_fields) : List (FBB × List FBB) := [
      (-row.is_valid,
        [
          1,
          row.rs1,
          row.rs1_val[0],
          row.rs1_val[1],
          row.rs1_val[2],
          row.rs1_val[3],
          row.rs1_prev_timestamp
        ]
      ),
      (row.is_valid,
        [
          1,
          row.rs1,
          row.rs1_val[0],
          row.rs1_val[1],
          row.rs1_val[2],
          row.rs1_val[3],
          row.timestamp
        ]
      ),
      (-row.is_valid,
        [
          row.read_address_space,
          row.read_ptr,
          row.prev_read_data[0],
          row.prev_read_data[1],
          row.prev_read_data[2],
          row.prev_read_data[3],
          row.read_prev_timestamp
        ]
      ),
      (row.is_valid,
        [
          row.read_address_space,
          row.read_ptr,
          row.read_data[0],
          row.read_data[1],
          row.read_data[2],
          row.read_data[3],
          row.timestamp + 1
        ]
      ),
      (-row.needs_write,
        [
          row.write_address_space,
          row.write_ptr,
          row.prev_write_data[0],
          row.prev_write_data[1],
          row.prev_write_data[2],
          row.prev_write_data[3],
          row.rd_prev_timestamp
        ]
      ),
      (row.needs_write,
        [
          row.write_address_space,
          row.write_ptr,
          row.write_data[0],
          row.write_data[1],
          row.write_data[2],
          row.write_data[3],
          row.timestamp + 2
        ]
      )
    ]

  def LoadStore_instruction_fields.range_checks (row : LoadStore_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
    (row.is_valid, [row.range_checked_vals[2], 14]),
    (row.is_valid, [row.range_checked_vals[3], 13]),
    (row.is_valid, [row.range_checked_vals[4], 17]),
    (row.is_valid, [row.range_checked_vals[5], 12]),
    (row.needs_write, [row.range_checked_vals[6], 17]),
    (row.needs_write, [row.range_checked_vals[7], 12])
  ]

  def LoadStore_instruction_fields.read_instruction (row : LoadStore_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [
      row.pc, row.opcode,
      row.rd, row.rs1,
      row.imm_lower_half,
      1,
      row.memory_address_space,
      row.needs_write,
      row.imm_sign
    ])
  ]

  def bus_from_instruction_fields (rows : List LoadStore_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then
        rows.flatMap LoadStore_instruction_fields.execution
      else if index = MemoryBus then
        rows.flatMap LoadStore_instruction_fields.memory
      else if index = RangeCheckerBus then
        rows.flatMap LoadStore_instruction_fields.range_checks
      else if index = ReadInstructionBus then
        rows.flatMap LoadStore_instruction_fields.read_instruction
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_loadstore FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_loadstore.constraints.allHold air row.1 (by grind)

  def get_instruction_fields_row [Field ExtF] (air : Valid_VmAirWrapper_loadstore FBB ExtF) (row : ℕ) : LoadStore_instruction_fields := {
    is_valid := air.core.is_valid row 0
    opcode := air.core.expected_opcode row 0
    pc := air.adapter.from_state.pc row 0
    next_pc := air.to_pc row 0
    timestamp := air.adapter.from_state.timestamp row 0
    next_timestamp := air.adapter.from_state.timestamp row 0 + 3
    rs1_prev_timestamp := air.adapter.rs1_aux_cols.base.prev_timestamp row 0
    read_prev_timestamp := air.adapter.read_data_aux.base.prev_timestamp row 0
    rd_prev_timestamp := air.adapter.write_base_aux.prev_timestamp row 0
    rs1 := air.adapter.rs1_ptr row 0
    rd := air.adapter.rd_rs2_ptr row 0
    imm_lower_half := air.adapter.imm row 0
    imm_sign := air.adapter.imm_sign row 0
    memory_address_space := air.adapter.mem_as row 0
    read_address_space := air.read_as row 0
    read_ptr := air.read_ptr row 0
    needs_write := air.adapter.needs_write row 0
    write_address_space := air.write_as row 0
    write_ptr := air.write_ptr row 0
    imm := #v[
      (air.adapter.imm row 0).val % 256,
      (air.adapter.imm row 0).val / 256,
      (air.adapter.imm_extended_limb row 0).val % 256,
      (air.adapter.imm_extended_limb row 0).val / 256,
    ]
    rs1_val := #v[
      air.adapter.rs1_data_0 row 0,
      air.adapter.rs1_data_1 row 0,
      air.adapter.rs1_data_2 row 0,
      air.adapter.rs1_data_3 row 0
    ]
    prev_read_data := #v[
      air.core.read_data_0 row 0,
      air.core.read_data_1 row 0,
      air.core.read_data_2 row 0,
      air.core.read_data_3 row 0
    ]
    read_data := #v[
      air.core.read_data_0 row 0,
      air.core.read_data_1 row 0,
      air.core.read_data_2 row 0,
      air.core.read_data_3 row 0
    ]
    prev_write_data := #v[
      air.core.prev_data_0 row 0,
      air.core.prev_data_1 row 0,
      air.core.prev_data_2 row 0,
      air.core.prev_data_3 row 0
    ]
    write_data := #v[
      air.core.write_data_0 row 0,
      air.core.write_data_1 row 0,
      air.core.write_data_2 row 0,
      air.core.write_data_3 row 0
    ]
    range_checked_vals := #v[
      air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0,
      air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0,
      (air.adapter.mem_ptr_limbs_0 row 0 - air.shift_amount row 0) * 1509949441,
      air.adapter.mem_ptr_limbs_1 row 0,
      air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_0 row 0,
      air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_1 row 0,
      air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_0 row 0,
      air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_1 row 0
    ]
    : LoadStore_instruction_fields
  }

  def get_instruction_fields [Field ExtF] (air : Valid_VmAirWrapper_loadstore FBB ExtF) : List LoadStore_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma execution_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
  :
    List.flatMap (VmAirWrapper_loadstore.constraints.executionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap LoadStore_instruction_fields.execution (get_instruction_fields air)
  := by
    unfold LoadStore_instruction_fields.execution
    unfold VmAirWrapper_loadstore.constraints.executionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma memory_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
  :
    List.flatMap (VmAirWrapper_loadstore.constraints.memoryBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap LoadStore_instruction_fields.memory (get_instruction_fields air)
  := by
    unfold LoadStore_instruction_fields.memory
    unfold VmAirWrapper_loadstore.constraints.memoryBus_row
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      h_neg_one
    ]

  lemma range_checks_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
  :
    List.flatMap (VmAirWrapper_loadstore.constraints.rangeCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap LoadStore_instruction_fields.range_checks (get_instruction_fields air)
  := by
    unfold LoadStore_instruction_fields.range_checks
    unfold VmAirWrapper_loadstore.constraints.rangeCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma read_instruction_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
  :
    List.flatMap (VmAirWrapper_loadstore.constraints.readInstructionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap LoadStore_instruction_fields.read_instruction (get_instruction_fields air)
  := by
    unfold LoadStore_instruction_fields.read_instruction
    unfold VmAirWrapper_loadstore.constraints.readInstructionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma bus_from_instruction_fields_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (h_constraints : allHold_allRows air)
  :
    air.buses = bus_from_instruction_fields (get_instruction_fields air)
  := by
    have h_interactions := VmAirWrapper_loadstore.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_loadstore.constraints.constrain_interactions at h_interactions
    rewrite [h_interactions]; clear h_interactions
    unfold bus_from_instruction_fields
    simp [
      execution_eq_air_buses,
      memory_eq_air_buses,
      range_checks_eq_air_buses,
      read_instruction_eq_air_buses,
    ]

  set_option maxHeartbeats 0 in
  lemma get_instruction_fields_row_opcode_range [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
  :
    (get_instruction_fields_row air row).opcode ∈ Finset.Icc 528 533
  := by
    simp [
      get_instruction_fields_row,
      Valid_LoadStoreCoreAir_4.expected_opcode,
      Valid_LoadStoreCoreAir_4.opcode_when,
      Valid_LoadStoreCoreAir_4.opcode_flags
    ]
    rewrite [
      allHold_allRows
    ] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    rewrite [
      VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold
    ] at h_constraints
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
    obtain ⟨
      _,
      _,
      h_flag_0_le_2,
      h_flag_1_le_2,
      h_flag_2_le_2,
      h_flag_3_le_2,
      _,
      h_sum_1_or_2,
      _
    ⟩ := h_constraints
    simp [h_is_valid] at h_sum_1_or_2
    unfold Valid_LoadStoreCoreAir_4.sum at h_sum_1_or_2 ⊢
    obtain h_flag_0 | h_flag_0 | h_flag_0 := h_flag_0_le_2 <;>
    obtain h_flag_1 | h_flag_1 | h_flag_1 := h_flag_1_le_2 <;>
    obtain h_flag_2 | h_flag_2 | h_flag_2 := h_flag_2_le_2 <;>
    obtain h_flag_3 | h_flag_3 | h_flag_3 := h_flag_3_le_2
    all_goals rewrite [h_flag_0, h_flag_1, h_flag_2, h_flag_3] at ⊢ h_sum_1_or_2
    all_goals simp at h_sum_1_or_2
    all_goals unfold Valid_LoadStoreCoreAir_4.inv_2
    all_goals decide

  lemma transpile_of_bus_wellformedness [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction a b,
    Transpiler.transpile_op instruction 1 (air.adapter.from_state.pc row 0) = some (a, b) ∧
      a = 1 ∧
      b[0] = air.adapter.from_state.pc row 0 ∧
      b[1] = air.core.expected_opcode row 0 ∧
      b[2] = air.adapter.rd_rs2_ptr row 0 ∧
      b[3] = air.adapter.rs1_ptr row 0 ∧
      b[4] = air.adapter.imm row 0 ∧
      b[5] = 1 ∧
      b[6] = air.adapter.mem_as row 0 ∧
      b[7] = air.adapter.needs_write row 0 ∧
      b[8] = air.adapter.imm_sign row 0
  := by
    unfold VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2
    simp [
      VmAirWrapper_loadstore.constraints.propertiesToAssume,
      Interaction.ReadInstructionBusEntry.operand_properties,
      VmAirWrapper_loadstore.constraints._readInstructionBus_row,
      VmAirWrapper_loadstore.constraints.readInstructionBus_row,
      -List.map_nil, -Vector.toList_mk, -List.attach_cons
    ] at h_bus_wellformedness
    unfold Interaction.ReadInstructionBusEntry.deserialise at h_bus_wellformedness
    dsimp [List.attach] at h_bus_wellformedness
    rewrite [h_is_valid] at h_bus_wellformedness
    simp only [
      Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.cast_one,
      Fin.cast_val_eq_self,
      Interaction.ReadInstructionBusEntry.mk.injEq,
      forall_const
    ] at h_bus_wellformedness
    exact h_bus_wellformedness

  -- lemma add_rd_properties [Field ExtF]
  --   (air : Valid_VmAirWrapper_loadstore FBB ExtF)
  --   (row : ℕ)
  --   (h_is_valid : air.core.is_valid row 0 = 1)
  --   (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  --   (h_non_imm : air.adapter.rs2_as row 0 = 1)
  --   (h_opcode : (air.core.ctx row 0).instruction.opcode = 512)
  -- :
  --   ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
  --   ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  -- := by
  --   replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
  --   simp [wrap_to_regidx, get_instruction_fields_row]
  --   obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
  --   rewrite [h_opcode] at h_transpile
  --   have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
  --   have h_cases := Transpiler.transpiler_opcode_512 h_transpile.1 h_transpile.2.2.2.1
  --   cases h_cases with
  --     | inl h_addi =>
  --       exfalso
  --       obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_addi
  --       rewrite [h_instruction] at h_transpile
  --       unfold Transpiler.transpile_op at h_transpile
  --       rewrite [ite_cond_eq_true _ _ (eq_true h_pc_aligned)] at h_transpile
  --       dsimp at h_transpile
  --       split_ifs at h_transpile
  --       . have := Transpiler.extract_opcode h_transpile.1
  --         simp at this
  --         simp [this] at h_transpile
  --       . simp [-Vector.mk_eq] at h_transpile
  --         rewrite [h_non_imm] at h_transpile
  --         rewrite [←h_transpile.1.2] at h_transpile
  --         simp at h_transpile
  --     | inr h_add =>
  --       obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_add
  --       rewrite [h_instruction] at h_transpile
  --       unfold Transpiler.transpile_op at h_transpile
  --       rewrite [ite_cond_eq_true _ _ (eq_true h_pc_aligned)] at h_transpile
  --       dsimp at h_transpile
  --       split_ifs at h_transpile
  --       . have := Transpiler.extract_opcode h_transpile.1
  --         simp at this
  --         exfalso
  --         simp [this] at h_transpile
  --       . simp [-Vector.mk_eq] at h_transpile
  --         rewrite [←h_transpile.2.2.2.2.1, ←h_transpile.1.2]
  --         simp [Transpiler.ind, regidx_to_fin]
  --         rewrite [Nat.mod_eq_of_lt (by omega)]
  --         split_ands
  --         . by_cases h_contr : rd.1 = 0
  --           . simp [h_contr] at h_rd
  --           . simp [BitVec.toNat_eq_nat]
  --             convert h_contr
  --         . use rd

  -- lemma split_bitvec_16_to_8s
  --   (h_a : a < 65536)
  -- :
  --   { toFin := ⟨a, by omega⟩: BitVec 16} =
  --   { toFin := ⟨a / 256, by omega⟩: BitVec 8} ++
  --   { toFin := ⟨a % 256, by omega⟩: BitVec 8}
  -- := by
  --   unfold_projs
  --   unfold BitVec.append BitVec.shiftLeftZeroExtend
  --   simp [Nat.shiftLeft_eq]
  --   bv_decide
  --   done

  lemma split_bitvec_16_to_8s
    (h_a : a < 65536)
  :
    BitVec.ofNat 16 a =
    BitVec.ofNat 8 (a/256) ++
    BitVec.ofNat 8 (a%256)
  := by
    rewrite (occs := .pos [1]) [←Nat.div_add_mod a 256]
    simp [BitVec.ofNat_add, BitVec.ofNat_mul]
    have :
      256#16 * BitVec.setWidth 16 (BitVec.ofNat 8 (a / 256)) +
      BitVec.ofNat 8 (a % 256) =
      BitVec.ofNat 8 (a / 256) ++ BitVec.ofNat 8 (a % 256)
    := by bv_decide
    rewrite [←this]; clear this
    congr
    . unfold BitVec.setWidth BitVec.setWidth'
      simp
      simp (disch := omega) [Nat.mod_eq_of_lt]
      grind
    . unfold BitVec.setWidth BitVec.setWidth'
      simp
      grind

  lemma lw_spec_of_get_instruction_fields_part_1 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.imm row 0).val % 256 < 256
  := by
    omega

  lemma lw_spec_of_get_instruction_fields_part_2 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.imm row 0).val / 256 < 256
  := by
    have := Load.imm_range_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
    omega

  lemma lw_spec_of_get_instruction_fields_part_3 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.imm_extended_limb row 0).val % 256 < 256
  := by
    omega

  lemma lw_spec_of_get_instruction_fields_part_4 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.imm_extended_limb row 0).val / 256 < 256
  := by
    have := Load.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
    omega

  lemma lw_spec_of_get_instruction_fields_part_5 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_0 row 0).val < 256
  := by
    have := Load.rs1_data_0_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lw_spec_of_get_instruction_fields_part_6 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_1 row 0).val < 256
  := by
    have := Load.rs1_data_1_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lw_spec_of_get_instruction_fields_part_7 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_2 row 0).val < 256
  := by
    have := Load.rs1_data_2_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lw_spec_of_get_instruction_fields_part_8 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_3 row 0).val < 256
  := by
    have := Load.rs1_data_3_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lw_spec_of_get_instruction_fields_part_9 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data_0 row 0).val < 256
  := by
    have h_memory := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920 : FBB) = (-1 : FBB) by decide
    ] at h_memory
    exact h_memory.2.1.2.2.1

  lemma lw_spec_of_get_instruction_fields_part_10 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data_1 row 0).val < 256
  := by
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.1

  lemma lw_spec_of_get_instruction_fields_part_11 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data_2 row 0).val < 256
  := by
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.2.1

  lemma lw_spec_of_get_instruction_fields_part_12 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data_3 row 0).val < 256
  := by
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.2.2

  lemma lw_spec_of_get_instruction_fields_part_13 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.adapter.needs_write row 0 = 1 →
    (air.core.prev_data_0 row 0).val < 256 ∧
    (air.core.prev_data_1 row 0).val < 256 ∧
    (air.core.prev_data_2 row 0).val < 256 ∧
    (air.core.prev_data_3 row 0).val < 256
  := by
    intro h_needs_write
    have h_memory := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920 : FBB) = (-1 : FBB) by decide,
      h_needs_write
    ] at h_memory
    split_ands
    . exact h_memory.2.2.2.2.1
    . exact h_memory.2.2.2.2.2.1
    . exact h_memory.2.2.2.2.2.2.1
    . exact h_memory.2.2.2.2.2.2.2

  lemma lw_spec_of_get_instruction_fields_part_14 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_assumptions : VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.adapter.needs_write row 0 = 1 →
    (air.core.write_data_0 row 0).val < 256 ∧
    (air.core.write_data_1 row 0).val < 256 ∧
    (air.core.write_data_2 row 0).val < 256 ∧
    (air.core.write_data_3 row 0).val < 256
  := by
    intro h_needs_write
    have h_memory := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920 : FBB) = (-1 : FBB) by decide,
      h_needs_write
    ] at h_memory
    have h_0 := Load.write_data_0_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_1 := Load.write_data_1_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_2 := Load.write_data_2_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_3 := Load.write_data_3_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    rewrite [h_0, h_1, h_2, h_3]
    split_ands
    . exact h_memory.2.1.2.2.1
    . exact h_memory.2.1.2.2.2.1
    . exact h_memory.2.1.2.2.2.2.1
    . exact h_memory.2.1.2.2.2.2.2

  set_option maxHeartbeats 0 in
  lemma lw_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 528 →
        LwOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_LOAD_lw_pure
            (LwInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [
      LwOutput_matches_LoadStore_instruction_fields,
      get_instruction_fields_row,
      -BitVec.toNat_add
    ]
    rw [BitVec.toNat_add]
    simp

    rewrite [allHold_allRows] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    specialize h_bus_assumptions row h_row
    specialize h_bus_wellformedness row h_row
    simp [LwInput_of_LoadStore_instruction_fields, PureSpec.execute_LOAD_lw_pure]

    split_ands
    . exact lw_spec_of_get_instruction_fields_part_1 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_2 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_3 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_4 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_5 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_6 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_7 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_8 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_9 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_10 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_11 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_12 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_13 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_14 air row h_row h_is_valid h_opcode h_constraints h_bus_assumptions h_bus_wellformedness
    . simp [
        Valid_VmAirWrapper_loadstore.to_pc
      ]
      have h_execution := h_bus_assumptions.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid
      ] at h_execution
      rewrite [Fin.val_add, Nat.mod_eq_of_lt, BitVec.ofNat_add]
      . simp
      . omega
    . exact Load.read_as_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    . exact Load.write_as_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    . have := Load.read_ptr_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
      rewrite [this]; clear this
      have h_mem_ptr := Load.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
      have h_imm_sign_extend := Load.imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [h_imm_sign_extend] at h_mem_ptr
      rewrite [BitVec.toNat_eq] at h_mem_ptr
      simp [-BitVec.toNat_add] at h_mem_ptr
      rw [BitVec.toNat_add] at h_mem_ptr
      simp at h_mem_ptr
      rewrite [Nat.mod_eq_of_lt (by omega)] at h_mem_ptr
      rewrite [h_mem_ptr]; clear h_mem_ptr
      congr
      simp only [
        U32.toNat,
        Vector.getElem_mk,
        List.getElem_toArray,
        List.getElem_cons_zero,
        List.getElem_cons_succ
      ]
      repeat rw [BitVec.toNat_ofFin]
      simp
      have (x y: ℕ) :
        (BitVec.setWidth 32 (BitVec.ofNat 16 x)) <<< 16 +
        (BitVec.setWidth 32 (BitVec.ofNat 16 y)) =
        (BitVec.ofNat 16 x) ++ (BitVec.ofNat 16 y)
      := by bv_decide
      rewrite [←this]; clear this
      rw [BitVec.toNat_add]
      simp
      have (x: ℕ) :
        x % 65536 =
        256 * (x / 256) % 65536 + x % 256
      := by
        rewrite (occs := .pos [1]) [
          ←Nat.div_add_mod x 256
        ]
        rw [
          Nat.add_mod,
          Nat.mod_eq_of_lt (by omega),
          @Nat.mod_eq_of_lt (x % 256) _ (by omega)
        ]
      rewrite [@Nat.mod_eq_of_lt (_ % 65536)]
      simp [Nat.shiftLeft_eq]
      rewrite [@Nat.mod_eq_of_lt _ 4294967296 (by omega)]
      rewrite [this]
      . omega
      . omega
    . exact Load.write_ptr_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    . have := Load.imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
      simp [U32.toBV]
      have (bv1 bv2 bv3 bv4: BitVec 8) :
        BitVec.setWidth 12 (bv1 ++ bv2 ++ bv3 ++ bv4) =
        BitVec.setWidth 12 (bv3 ++ bv4)
      := by bv_decide
      rewrite [this]; clear this
      -- combine the two halves of imm into BitVec.ofNat 16 imm
      have h_imm_range := Load.imm_range_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
      have h_split_imm := split_bitvec_16_to_8s h_imm_range
      simp [BitVec.ofNat, Nat.cast] at h_split_imm
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm
      dsimp at h_split_imm
      simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm
      simp (disch := omega) [Nat.mod_eq_of_lt]
      have (a b c d: BitVec 8) : a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d) := by grind
      rewrite [this]
      simp [←h_split_imm]
      have :
        BitVec.signExtend 32 (BitVec.setWidth 12 (BitVec.ofNat 16 (air.adapter.imm row 0))) =
        BitVec.signExtend 32 (BitVec.ofNat 16 (air.adapter.imm row 0))
      := by
        have h_transpile := h_bus_wellformedness.2.2.2
        simp [
          VmAirWrapper_loadstore_constraint_and_interaction_simplification,
          h_is_valid,
          Interaction.ReadInstructionBusEntry.operand_properties
        ] at h_transpile
        obtain ⟨
          instruction,
          multiplciity,
          data,
          ⟨h_instruction, _, _, h_data_opcode, _, _, h_data_imm, _⟩
        ⟩ := h_transpile
        rewrite [←h_data_imm]
        have := Transpiler.transpiler_opcode_528 h_instruction
        simp [h_data_opcode, h_opcode] at this
        have h_alignment := Transpiler.pc_aligned_of_some h_instruction
        obtain
          ⟨_, imm, rs1, rd, h_instruction_load, _⟩ |
          ⟨_, imm, rs1, h_instruction_load⟩
        := this
        all_goals {
          rewrite [h_instruction_load] at h_instruction
          unfold Transpiler.transpile_op at h_instruction
          rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_instruction
          dsimp at h_instruction
          simp [-Vector.mk_eq] at h_instruction
          simp (disch := omega) [←h_instruction.2, Transpiler.utof, Transpiler.sign_extend_16, Nat.mod_eq_of_lt]
          bv_decide
        }
      convert this using 1
      . simp [BitVec.ofNat, Nat.cast]
        unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
        dsimp
        simp (disch := omega) [Nat.mod_eq_of_lt]
      . have h_imm_extended_range := Load.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
        have h_split_imm_extended := split_bitvec_16_to_8s h_imm_extended_range
        simp [BitVec.ofNat, Nat.cast] at h_split_imm_extended
        unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm_extended
        dsimp at h_split_imm_extended
        simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm_extended
        simp (disch := omega) [Nat.mod_eq_of_lt]
        rewrite [←h_split_imm_extended]
        have := Load.imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
        rewrite [this]
        simp [BitVec.ofNat, Nat.cast]
        unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
        dsimp
        simp (disch := omega) [Nat.mod_eq_of_lt]
    . simp [U32.toBV]
      have := Load.imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [this]
      have (a b c d: BitVec 8) : a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d) := by grind
      rewrite [this]; clear this
      congr
      . have := Nat.div_add_mod (air.adapter.imm_extended_limb row 0).val 256
        have :
          BitVec.ofNat 16 (air.adapter.imm_extended_limb row 0).val =
          BitVec.ofNat 16 (
            256 * ((air.adapter.imm_extended_limb row 0).val / 256) +
            (air.adapter.imm_extended_limb row 0).val % 256
          )
        := by
          rw (occs := .pos [1]) [←this]
        rewrite [this]; clear this; clear this; clear this
        rewrite [BitVec.ofNat_add, BitVec.ofNat_mul]
        have : (air.adapter.imm_extended_limb row 0).val / 256 < 256 := by
          have := Load.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
          omega
        simp [Nat.mod_eq_of_lt this]
        have (bv1 bv2: BitVec 8) :
          256#16 * BitVec.setWidth 16 bv1 + BitVec.setWidth 16 bv2 =
          bv1 ++ bv2
        := by bv_decide
        rewrite [←this]
        congr
        . simp [
            ← BitVec.toNat_inj,
            - BitVec.toNat_ofFin
          ]
          rw [BitVec.toNat_ofFin]
        . simp [
            ← BitVec.toNat_inj,
            - BitVec.toNat_ofFin
          ]
          rw [BitVec.toNat_ofFin]
      . have := Nat.div_add_mod (air.adapter.imm row 0).val 256
        have :
          BitVec.ofNat 16 (air.adapter.imm row 0).val =
          BitVec.ofNat 16 (
            256 * ((air.adapter.imm row 0).val / 256) +
            (air.adapter.imm row 0).val % 256
          )
        := by
          rw (occs := .pos [1]) [←this]
        rewrite [this]; clear this; clear this; clear this
        rewrite [BitVec.ofNat_add, BitVec.ofNat_mul]
        have : (air.adapter.imm row 0).val / 256 < 256 := by
          have := Load.imm_range_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
          omega
        simp [Nat.mod_eq_of_lt this]
        have (bv1 bv2: BitVec 8) :
          256#16 * BitVec.setWidth 16 bv1 + BitVec.setWidth 16 bv2 =
          bv1 ++ bv2
        := by bv_decide
        rewrite [←this]
        congr <;> {
          unfold BitVec.setWidth BitVec.setWidth' BitVec.toNat
          simp [BitVec.ofNat]
          refine BitVec.eq_of_toNat_eq ?_
          simp
          omega
          done
        }
      done


    all_goals
      sorry

#exit

    . have := Load.imm_sign_of_opcode_528 air row h_bus_wellformedness h_is_valid h_opcode
      rewrite [this]; clear this
      simp [U32.toBV]
      have (bv1 bv2 bv3 bv4: BitVec 8) : (bv1 ++ bv2 ++ bv3 ++ bv4).msb = bv1.msb := by bv_decide
      simp [this]
      have := Load.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
      have :
        (air.adapter.imm_extended_limb row 0).val / 256 % 256 =
        (air.adapter.imm_extended_limb row 0).val / 256
      := by
        omega
      simp [this]
      have h_sign_extend := Load.imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
      have (bv1 bv2: BitVec 32): bv1 = bv2 → bv1.msb = bv2.msb := by intro h; grind
      apply this at h_sign_extend
      have (bv: BitVec 16) : (bv.signExtend 32).msb = bv.msb := by bv_decide
      rewrite [this] at h_sign_extend
      rewrite [h_sign_extend]
      have (bv1 bv2: BitVec 16): (bv1 ++ bv2).msb = bv1.msb := by bv_decide
      rewrite [this]
      simp [BitVec.ofNat, BitVec.msb, BitVec.getMsbD, Nat.testBit]
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.shiftRight_eq_div_pow,
        Nat.shiftRight_eq_div_pow,
      ]
      simp
      rewrite [Nat.div_div_eq_div_mul]
      simp
      done
    . have h_transpile := h_bus_wellformedness.2.2.2
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        Interaction.ReadInstructionBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨instruction, multiplicity, data, h_instruction⟩ := h_transpile
      have h_aligned := Transpiler.pc_aligned_of_some h_instruction.1
      have h_rd := Transpiler.transpiler_opcode_528 h_instruction.1
      simp [h_instruction, h_opcode] at h_rd
      obtain ⟨
        h_needs_write,
        imm,
        rs1,
        rd,
        h_instruction_load,
        h_rd
      ⟩ | ⟨
        h_needs_write,
        imm,
        rs1,
        h_instruction_load
      ⟩ := h_rd
      . rewrite [h_instruction_load] at h_instruction
        unfold Transpiler.transpile_op at h_instruction
        dsimp at h_instruction
        rewrite [ite_cond_eq_true _ _ (eq_true h_aligned)] at h_instruction
        simp [-Vector.mk_eq] at h_instruction
        rewrite [←h_instruction.2.2.2.2.1, ←h_instruction.1.2]
        simp [Transpiler.ind, wrap_to_regidx, regidx_to_fin]
        rewrite [dite_cond_eq_false]
        . simp
          rewrite [←h_instruction.2.2.2.2.2.2.2.2.2.1, ←h_instruction.1.2]
          simp
          obtain ⟨⟨rd: Fin 32⟩⟩ := rd
          split_ands
          . simp [U32.toBV]
            have := Load.write_data_3_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := Load.write_data_2_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := Load.write_data_1_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := Load.write_data_0_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            done
          . grind
            done
          . clear *-h_rd
            fin_cases rd
            . simp_all
            all_goals decide
          done
        . clear *-h_rd
          obtain ⟨⟨rd: Fin 32⟩⟩ := rd
          simp
          convert h_rd
          omega
      . rewrite [h_instruction_load] at h_instruction
        unfold Transpiler.transpile_op at h_instruction
        dsimp at h_instruction
        rewrite [ite_cond_eq_true _ _ (eq_true h_aligned)] at h_instruction
        simp [-Vector.mk_eq] at h_instruction
        rewrite [←h_instruction.2.2.2.2.1, ←h_instruction.1.2]
        simp [Transpiler.ind, wrap_to_regidx, regidx_to_fin]
        rewrite [←h_instruction.2.2.2.2.2.2.2.2.2.1, ←h_instruction.1.2]
        simp
        decide
      done

  lemma non_imm_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).non_imm = 1 →
    ((get_instruction_fields_row air row).opcode = 512 →
        AddOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_add_pure
            (AddInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 513 →
          SubOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_sub_pure
              (SubInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 514 →
          XorOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_xor_pure
              (XorInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 515 →
          OrOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_or_pure
              (OrInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 516 →
          AndOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_and_pure
              (AndInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row)))))
  := by
    intro h_non_imm
    simp [get_instruction_fields_row] at h_non_imm

    exact ⟨
      add_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_non_imm, ⟨
        sub_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_non_imm, ⟨
          xor_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_non_imm, ⟨
            or_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_non_imm,
            and_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_non_imm
          ⟩
        ⟩
      ⟩
    ⟩

  lemma imm_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).non_imm = 0 →
    ((get_instruction_fields_row air row).opcode = 512 →
        AddiOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_ITYPE_addi_pure
            (AddiInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode ≠ 513) ∧
      ((get_instruction_fields_row air row).opcode = 514 →
          XoriOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_ITYPE_xori_pure
              (XoriInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 515 →
          OriOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_ITYPE_ori_pure
              (OriInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 516 →
          AndiOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_ITYPE_andi_pure
              (AndiInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row)))))
  := by
    intro h_imm
    simp [get_instruction_fields_row] at h_imm

    exact ⟨
      addi_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_imm, ⟨
        subi_spec_of_get_instruction_fields air row h_row h_is_valid h_bus_wellformedness h_imm, ⟨
          xori_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_imm, ⟨
            ori_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_imm,
            andi_spec_of_get_instruction_fields air row h_row h_constraints h_is_valid h_bus_assumptions h_bus_wellformedness h_imm
          ⟩
        ⟩
      ⟩
    ⟩

  lemma spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    List.Forall LoadStore_instruction_fields.spec (get_instruction_fields air)
  := by
    apply List.forall_iff_forall_mem.mpr
    intro instruction_fields h_instruction_fields
    unfold LoadStore_instruction_fields.spec

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
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List LoadStore_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall LoadStore_instruction_fields.spec
  := by
    use get_instruction_fields air
    simp only [
      bus_from_instruction_fields_eq_air_buses air h_constraints,
      spec_of_get_instruction_fields air h_constraints h_bus_assumptions h_bus_wellformedness
    ]
    trivial

end Equivalence.BaseLoadStore
