import OpenvmFv.Spec.LoadStore.lw
import OpenvmFv.Spec.LoadStore.lhu
import OpenvmFv.Spec.LoadStore.lbu
import OpenvmFv.Spec.LoadStore.sw
import OpenvmFv.Spec.LoadStore.sh
import OpenvmFv.Spec.LoadStore.sb
import OpenvmFv.Spec.LoadW
import OpenvmFv.Spec.LoadHU
import OpenvmFv.Spec.LoadBU
import OpenvmFv.Spec.StoreW
import OpenvmFv.Spec.StoreH
import OpenvmFv.Spec.StoreB

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

    shift : FBB

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
    a.shift = b.shift ∧
    a.range_checked_vals = b.range_checked_vals
      → a = b
  := by
    intro field_eq
    ext <;> grind

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val / 4 % 32, by grind⟩

  structure RVConfig where
    mstatus : BitVec 64
    cur_privilege : Privilege
    plat_clint_base : BitVec 34
    plat_clint_size : BitVec 34
    plat_ram_base : BitVec 34
    plat_ram_size : BitVec 34
    plat_rom_base : BitVec 34
    plat_rom_size : BitVec 34
    htif_tohost_base : Option (BitVec 34)

  opaque plat_ram_size : BitVec 34
  opaque plat_rom_size : BitVec 34

  def config : RVConfig := {
    mstatus := 0
    cur_privilege := Privilege.Machine
    plat_clint_base := 0
    plat_clint_size := 0
    plat_ram_base := 0
    plat_ram_size := plat_ram_size
    plat_rom_base := 0
    plat_rom_size := plat_rom_size
    htif_tohost_base := .none
  }

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
      else if index = ProgramBus then
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
    shift := air.shift_amount row 0,
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
    List.flatMap (VmAirWrapper_loadstore.constraints.programBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap LoadStore_instruction_fields.read_instruction (get_instruction_fields air)
  := by
    unfold LoadStore_instruction_fields.read_instruction
    unfold VmAirWrapper_loadstore.constraints.programBus_row
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
      Interaction.ProgramBusEntry.operand_properties,
      VmAirWrapper_loadstore.constraints._programBus_row,
      VmAirWrapper_loadstore.constraints.programBus_row,
      -List.map_nil, -Vector.toList_mk, -List.attach_cons
    ] at h_bus_wellformedness
    unfold Interaction.ProgramBusEntry.deserialise at h_bus_wellformedness
    dsimp [List.attach] at h_bus_wellformedness
    rewrite [h_is_valid] at h_bus_wellformedness
    simp only [
      Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.cast_one,
      Fin.cast_val_eq_self,
      Interaction.ProgramBusEntry.mk.injEq,
      forall_const
    ] at h_bus_wellformedness
    exact h_bus_wellformedness

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

  /-
     ***
     *** SW
     ***
  -/

  def SwInput_of_LoadStore_instruction_fields (row : LoadStore_instruction_fields) : PureSpec.SwInput := {
    r1 := BitVec.ofFin (wrap_to_regidx row.rs1)
    imm := BabyBear.toBV32 row.imm
    r2 := BitVec.ofFin (wrap_to_regidx row.rd)
    r1_val := BabyBear.toBV32 row.rs1_val
    r2_val := BabyBear.toBV32 row.prev_read_data
    PC := row.pc.toNat
    mstatus := config.mstatus
    cur_privilege := config.cur_privilege
    plat_clint_base := config.plat_clint_base
    plat_clint_size := config.plat_clint_size
    plat_ram_base := config.plat_ram_base
    plat_ram_size := config.plat_ram_size
    plat_rom_base := config.plat_rom_base
    plat_rom_size := config.plat_rom_size
    htif_tohost_base := config.htif_tohost_base
    : PureSpec.SwInput
  }

  def SwOutput_matches_LoadStore_instruction_fields (row : LoadStore_instruction_fields) (sw_output : PureSpec.SwOutput) : Prop :=
    BabyBear.isU32 row.imm ∧
    BabyBear.isU32 row.rs1_val ∧
    BabyBear.isU32 row.prev_read_data ∧
    BabyBear.isU32 row.read_data ∧
    row.needs_write = 1 ∧
    sw_output.nextPC = row.next_pc.toNat ∧
    row.read_address_space = 1 ∧
    row.read_ptr = row.rd ∧
    row.write_address_space = row.memory_address_space ∧
    row.write_ptr.val = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat ∧
    sw_output.data0.1 = row.write_ptr.val ∧
    row.prev_read_data = row.read_data ∧
    BitVec.signExtend 32 (BitVec.setWidth 12 (BabyBear.toBV32 row.imm)) = BabyBear.toBV32 row.imm ∧
    BabyBear.toBV32 row.imm = BitVec.signExtend 32 (BitVec.ofNat 16 row.imm_lower_half) ∧
    row.imm_sign = (BabyBear.toBV32 row.imm).msb.toNat ∧
    row.write_data = #v[
      ↑sw_output.data0.2.toNat,
      ↑sw_output.data1.2.toNat,
      ↑sw_output.data2.2.toNat,
      ↑sw_output.data3.2.toNat
    ]

  lemma imm_12_bits_of_opcode_531 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_opcode : air.core.expected_opcode row 0 = 531)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    BitVec.signExtend 32 (BitVec.setWidth 12 (BitVec.ofNat 16 (air.adapter.imm row 0))) =
    BitVec.signExtend 32 (BitVec.ofNat 16 (air.adapter.imm row 0))
  := by
    have h_transpile := h_bus_wellformedness.2.2.2
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ProgramBusEntry.operand_properties
    ] at h_transpile
    obtain ⟨
      instruction,
      multiplciity,
      data,
      ⟨h_instruction, _, _, h_data_opcode, _, _, h_data_imm, _⟩
    ⟩ := h_transpile
    rewrite [←h_data_imm]
    have := Transpiler.transpiler_opcode_531 h_instruction
    simp [h_data_opcode, h_opcode] at this
    have h_alignment := Transpiler.pc_aligned_of_some h_instruction
    have h_bound := Transpiler.pc_bound_of_some h_instruction
    obtain ⟨imm, rs2, rs1, h_instruction_store⟩ := this
    rewrite [h_instruction_store] at h_instruction
    unfold Transpiler.transpile_op at h_instruction
    rewrite [if_pos (by constructor <;> assumption)] at h_instruction
    dsimp at h_instruction
    simp [-Vector.mk_eq] at h_instruction
    simp (disch := omega) [←h_instruction.2, Transpiler.utof, Transpiler.sign_extend_16, Nat.mod_eq_of_lt]
    bv_decide

  lemma imm_extended_limb_upper_mod_of_opcode_531 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
  :
    (air.adapter.imm_extended_limb row 0).val / 256 % 256 =
    (air.adapter.imm_extended_limb row 0).val / 256
  := by
    have := StoreW.imm_extend_range_of_opcode_531 air row h_row h_constraints h_is_valid
    omega

  set_option maxHeartbeats 0 in
  lemma sw_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 531 →
        SwOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_STORE_sw_pure
            (SwInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode

    simp [
      SwOutput_matches_LoadStore_instruction_fields,
      get_instruction_fields_row,
      -BitVec.toNat_add
    ]
    repeat rw [BitVec.toNat_add]
    simp
    rewrite [allHold_allRows] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    specialize h_bus_axioms row h_row
    specialize h_bus_wellformedness row h_row
    simp [
      SwInput_of_LoadStore_instruction_fields,
      PureSpec.execute_STORE_sw_pure,
      -BitVec.toNat_add
    ]
    repeat rw [BitVec.toNat_add]
    simp
    split_ands
    . omega
    . have := StoreW.imm_range_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
      omega
    . omega
    . have := StoreW.imm_extend_range_of_opcode_531 air row h_row h_constraints h_is_valid
      omega
    . have := StoreW.rs1_data_0_range air row h_is_valid h_bus_wellformedness
      apply Fin.lt_def.mp at this
      convert this
    . have := StoreW.rs1_data_1_range air row h_is_valid h_bus_wellformedness
      apply Fin.lt_def.mp at this
      convert this
    . have := StoreW.rs1_data_2_range air row h_is_valid h_bus_wellformedness
      apply Fin.lt_def.mp at this
      convert this
    . have := StoreW.rs1_data_3_range air row h_is_valid h_bus_wellformedness
      apply Fin.lt_def.mp at this
      convert this
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.1
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.1
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.2.1
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.2.2
    . have := StoreW.needs_write_of_opcode_531 air row h_bus_wellformedness
      exact this h_is_valid h_opcode
    . simp [
        Valid_VmAirWrapper_loadstore.to_pc
      ]
      have h_execution := h_bus_axioms.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid
      ] at h_execution
      rewrite [Fin.val_add, Nat.mod_eq_of_lt, BitVec.ofNat_add]
      . simp
      . omega
    . exact StoreW.read_as_of_opcode_531 air row h_opcode h_row h_constraints h_is_valid
    . exact StoreW.read_ptr_of_opcode_531 air row h_opcode h_row h_constraints h_is_valid
    . exact StoreW.write_as_of_opcode_531 air row h_opcode h_row h_constraints h_is_valid
    . simp only [U32.toNat]
      rewrite [
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
      ]
      simp
      have := StoreW.write_ptr_of_opcode_531 air row h_opcode h_row h_constraints h_is_valid
      rewrite [this]; clear this
      have h_mem_ptr := StoreW.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
      have h_imm_sign_extend := StoreW.imm_sign_extend_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [h_imm_sign_extend] at h_mem_ptr
      rewrite [BitVec.toNat_eq] at h_mem_ptr
      simp [-BitVec.toNat_add] at h_mem_ptr
      rewrite [BitVec.toNat_add] at h_mem_ptr
      simp at h_mem_ptr
      rewrite [Nat.mod_eq_of_lt (by omega)] at h_mem_ptr
      rewrite [h_mem_ptr]; clear h_mem_ptr
      congr
      rewrite [BitVec.toNat_ofFin]
      simp
      have (x y: ℕ) :
        (BitVec.setWidth 32 (BitVec.ofNat 16 x)) <<< 16 +
        (BitVec.setWidth 32 (BitVec.ofNat 16 y)) =
        (BitVec.ofNat 16 x) ++ (BitVec.ofNat 16 y)
      := by bv_decide
      rewrite [←this]; clear this
      rewrite [BitVec.toNat_add]
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
    . have := StoreW.write_ptr_of_opcode_531 air row h_opcode h_row h_constraints h_is_valid
      rewrite [this]; clear this
      have := StoreW.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
      rewrite [←BitVec.toNat_inj] at this
      simp at this
      rewrite [Nat.mod_eq_of_lt (by omega)] at this
      rewrite [this]; clear this
      rewrite [add_comm]
      simp [
        U32.toBV,
        U32.toNat
      ]
      have (a b c d: BitVec 8) :
        BitVec.setWidth 12 (a ++ b ++ c ++ d) =
        BitVec.setWidth 12 (c ++ d)
      := by
        bv_decide
      rewrite [this]; clear this
      have
        (h1 : (air.adapter.imm row 0).val / 256 % 256 < 256)
        (h2 : (air.adapter.imm row 0).val % 256 < 256)
      :
        (
          BitVec.ofNat 16 (air.adapter.imm row 0)
        ) =
         ({ toFin := ⟨(air.adapter.imm row 0).val / 256 % 256, h1⟩} : BitVec 8) ++
         ({ toFin := ⟨(air.adapter.imm row 0).val % 256, h2⟩} : BitVec 8)
      := by
        rewrite (occs := .pos [1]) [←Nat.div_add_mod (air.adapter.imm row 0).val 256]
        rewrite [BitVec.ofNat_add, BitVec.ofNat_mul]
        have (a b: BitVec 8) :
          256#16 * BitVec.setWidth 16 a +
          BitVec.setWidth 16 b =
          a ++ b
        := by
          bv_decide
        rewrite [←this]; clear this
        congr
        . rewrite [←BitVec.toNat_inj]
          simp
          have := StoreW.imm_range_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
          omega
        . rewrite [←BitVec.toNat_inj]
          simp
      rewrite [←this]; clear this
      simp
      have := imm_12_bits_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
      simp at this
      rewrite [this]
      clear this
      rfl
    . have := StoreW.imm_sign_extend_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
      simp [U32.toBV]
      have (bv1 bv2 bv3 bv4: BitVec 8) :
        BitVec.setWidth 12 (bv1 ++ bv2 ++ bv3 ++ bv4) =
        BitVec.setWidth 12 (bv3 ++ bv4)
      := by bv_decide
      rewrite [this]; clear this
      -- combine the two halves of imm into BitVec.ofNat 16 imm
      have h_imm_range := StoreW.imm_range_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
      have h_split_imm := split_bitvec_16_to_8s h_imm_range
      simp [BitVec.ofNat, Nat.cast] at h_split_imm
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm
      dsimp at h_split_imm
      simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm
      simp (disch := omega) [Nat.mod_eq_of_lt]
      have (a b c d: BitVec 8) : a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d) := by grind
      rewrite [this]
      simp [←h_split_imm]
      have := imm_12_bits_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
      convert this using 1
      . simp [BitVec.ofNat, Nat.cast]
        unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
        dsimp
        simp (disch := omega) [Nat.mod_eq_of_lt]
      . have h_imm_extended_range := LoadW.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
        have h_split_imm_extended := split_bitvec_16_to_8s h_imm_extended_range
        simp [BitVec.ofNat, Nat.cast] at h_split_imm_extended
        unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm_extended
        dsimp at h_split_imm_extended
        simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm_extended
        simp (disch := omega) [Nat.mod_eq_of_lt]
        rewrite [←h_split_imm_extended]
        have := StoreW.imm_sign_extend_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
        rewrite [this]
        simp [BitVec.ofNat, Nat.cast]
        unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
        dsimp
        simp (disch := omega) [Nat.mod_eq_of_lt]
    . simp [U32.toBV]
      have := StoreW.imm_sign_extend_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
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
          have := StoreW.imm_extend_range_of_opcode_531 air row h_row h_constraints h_is_valid
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
          have := StoreW.imm_range_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
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
        }
    . have := StoreW.imm_sign_of_opcode_531 air row h_bus_wellformedness h_is_valid h_opcode
      rewrite [this]; clear this
      simp [U32.toBV]
      have (bv1 bv2 bv3 bv4: BitVec 8) : (bv1 ++ bv2 ++ bv3 ++ bv4).msb = bv1.msb := by bv_decide
      simp [this]
      have := imm_extended_limb_upper_mod_of_opcode_531 air row h_row h_constraints h_is_valid
      simp [this]
      have h_sign_extend := StoreW.imm_sign_extend_of_opcode_531 air row h_opcode h_is_valid h_bus_wellformedness
      have (bv1 bv2: BitVec 32): bv1 = bv2 → bv1.msb = bv2.msb := by intro h; grind
      apply this at h_sign_extend
      have (bv: BitVec 16) : (bv.signExtend 32).msb = bv.msb := by bv_decide
      rewrite [this] at h_sign_extend
      rewrite [h_sign_extend]
      have (bv1 bv2: BitVec 16): (bv1 ++ bv2).msb = bv1.msb := by bv_decide
      rewrite [this]
      have (a b : Bool) : (a.toNat: FBB) = (b.toNat: FBB) ↔ a = b := by cases a <;> cases b <;> decide
      rewrite [this]
      simp [BitVec.msb, BitVec.getMsbD, Nat.testBit]
      rewrite [Nat.mod_eq_of_lt (by omega)]
      unfold getElem BitVec.instGetElemNatBoolLt
      simp only [BitVec.getLsb, Nat.testBit]
      simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.shiftRight_eq_div_pow,
        Nat.shiftRight_eq_div_pow,
      ]
      simp
      rewrite [Nat.div_div_eq_div_mul]
      simp
    . have := StoreW.write_data_0_of_opcode_531 air row h_opcode h_row h_constraints h_is_valid
      rewrite [this]; clear this
      simp [U32.toNat]
      have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      have h_range := h_memory.2.1.2.2.1
      simp [Nat.add_mod]
      have (a: ℕ) : a * 65536 % 256 = 0 := by omega
      simp [this]
      have (a: ℕ) : a * 16777216 % 256 = 0 := by omega
      simp [Nat.add_mod]
      simp [this]
      rewrite [Nat.mod_eq_of_lt h_range]
      exact Eq.symm (Fin.cast_val_eq_self (air.core.read_data_0 row 0))
    . have := StoreW.write_data_1_of_opcode_531 air row h_opcode h_row h_constraints h_is_valid
      rewrite [this]; clear this
      simp [U32.toNat]
      have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      have h_range := h_memory.2.1.2.2.2.1
      simp [
        Nat.shiftRight_eq_div_pow,
        Nat.add_div,
        Nat.add_mod
      ]
      rewrite [
        ite_cond_eq_false _ _ (by simp; omega),
        ite_cond_eq_false _ _ (by simp; omega),
        ite_cond_eq_false _ _ (by simp; omega)
      ]
      simp [
        Nat.add_mod
      ]
      have (a : ℕ) : a % 256 * 65536 / 256 % 256 = 0 := by omega
      simp [this]; clear this
      have (a : ℕ) : a % 256 * 16777216 / 256 % 256 = 0 := by omega
      simp [Nat.add_mod, this]
      rewrite [Nat.mod_eq_of_lt (by omega)]
      exact Eq.symm (Fin.cast_val_eq_self (air.core.read_data_1 row 0))
    . have := StoreW.write_data_2_of_opcode_531 air row h_opcode h_row h_constraints h_is_valid
      rewrite [this]; clear this
      simp [U32.toNat]
      have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      have h_range := h_memory.2.1.2.2.2.2.1
      simp [
        Nat.shiftRight_eq_div_pow,
        Nat.add_div,
        Nat.add_mod
      ]
      rewrite [
        ite_cond_eq_false _ _ (by simp; omega),
        ite_cond_eq_false _ _ (by simp; omega),
        ite_cond_eq_false _ _ (by simp; omega)
      ]
      simp [
        Nat.add_mod
      ]
      have (a : ℕ) : a % 256 / 65536 = 0 := by omega
      simp [this]; clear this
      have (a : ℕ) : a % 256 * 256 / 65536 = 0 := by omega
      simp [this]; clear this
      have (a : ℕ) : a % 256 * 16777216 / 65536 % 256 = 0 := by omega
      simp [Nat.add_mod, this]
      rewrite [Nat.mod_eq_of_lt (by omega)]
      exact Eq.symm (Fin.cast_val_eq_self (air.core.read_data_2 row 0))
    . have := StoreW.write_data_3_of_opcode_531 air row h_opcode h_row h_constraints h_is_valid
      rewrite [this]; clear this
      simp [U32.toNat]
      have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      have h_range := h_memory.2.1.2.2.2.2.2
      simp [
        Nat.shiftRight_eq_div_pow,
        Nat.add_div,
        Nat.add_mod
      ]
      rewrite [
        ite_cond_eq_false _ _ (by simp; omega),
        ite_cond_eq_false _ _ (by simp; omega),
        ite_cond_eq_false _ _ (by simp; omega)
      ]
      simp [
        Nat.add_mod
      ]
      have (a : ℕ) : a % 256 / 16777216 = 0 := by omega
      simp [this]; clear this
      have (a : ℕ) : a % 256 * 256 / 16777216 = 0 := by omega
      simp [this]; clear this
      have (a : ℕ) : a % 256 * 65536 / 16777216 = 0 := by omega
      simp [this]
      rewrite [Nat.mod_eq_of_lt (by omega)]
      exact Eq.symm (Fin.cast_val_eq_self (air.core.read_data_3 row 0))

  /-
     ***
     *** SH
     ***
  -/

  def ShInput_of_LoadStore_instruction_fields (row : LoadStore_instruction_fields) : PureSpec.ShInput := {
      r1 := BitVec.ofFin (wrap_to_regidx row.rs1)
      imm := BabyBear.toBV32 row.imm
      r2 := BitVec.ofFin (wrap_to_regidx row.rd)
      r1_val := BabyBear.toBV32 row.rs1_val
      r2_val := BabyBear.toBV32 row.prev_read_data
      PC := row.pc.toNat
      mstatus := config.mstatus
      cur_privilege := config.cur_privilege
      plat_clint_base := config.plat_clint_base
      plat_clint_size := config.plat_clint_size
      plat_ram_base := config.plat_ram_base
      plat_ram_size := config.plat_ram_size
      plat_rom_base := config.plat_rom_base
      plat_rom_size := config.plat_rom_size
      htif_tohost_base := config.htif_tohost_base
      : PureSpec.ShInput
    }

  def ShOutput_matches_LoadStore_instruction_fields (row : LoadStore_instruction_fields) (sh_output : PureSpec.ShOutput) : Prop :=
    BabyBear.isU32 row.imm ∧
    BabyBear.isU32 row.rs1_val ∧
    BabyBear.isU32 row.prev_read_data ∧
    BabyBear.isU32 row.read_data ∧
    row.needs_write = 1 ∧
    row.read_address_space = 1 ∧
    row.read_ptr = row.rd ∧
    row.write_address_space = row.memory_address_space ∧
    row.prev_read_data = row.read_data ∧
    (row.shift.val = 0 ∨ row.shift.val = 2) ∧
    BitVec.signExtend 32 (BitVec.setWidth 12 (BabyBear.toBV32 row.imm)) = BabyBear.toBV32 row.imm ∧
    BabyBear.toBV32 row.imm = BitVec.signExtend 32 (BitVec.ofNat 16 row.imm_lower_half) ∧
    row.imm_sign = (BabyBear.toBV32 row.imm).msb.toNat ∧
    row.write_data = #v[
      if (row.shift = 0) then row.read_data[0] else row.prev_write_data[0],
      if (row.shift = 0) then row.read_data[1] else row.prev_write_data[1],
      if (row.shift = 0) then row.prev_write_data[2] else row.read_data[0],
      if (row.shift = 0) then row.prev_write_data[3] else row.read_data[1],
    ] ∧
    -- Actual output characterisation
    sh_output.nextPC = row.next_pc.toNat ∧
    row.write_ptr.val = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat - row.shift.val ∧
    sh_output.data0.1 = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat ∧
    sh_output.data0.2 = row.read_data[0].toNat ∧
    sh_output.data1.1 = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat + 1 ∧
    sh_output.data1.2 = row.read_data[1].toNat

  lemma sh_spec_imm_eq [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 532)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    BitVec.signExtend 32
    (BitVec.setWidth 12
      (U32.toBV
        #v[
          { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
          { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
        ]
      )
    ) =
    U32.toBV
      #v[
        { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
        { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
      ]
  := by
    have := StoreH.imm_sign_extend_of_opcode_532 air row h_opcode h_is_valid h_bus_wellformedness
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) :
      BitVec.setWidth 12 (bv1 ++ bv2 ++ bv3 ++ bv4) =
      BitVec.setWidth 12 (bv3 ++ bv4)
    := by bv_decide
    rewrite [this]; clear this
    -- combine the two halves of imm into BitVec.ofNat 16 imm
    have h_imm_range := StoreH.imm_range_of_opcode_532 air row h_opcode h_is_valid h_bus_wellformedness
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
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨
        instruction,
        multiplciity,
        data,
        ⟨h_instruction, _, _, h_data_opcode, _, _, h_data_imm, _⟩
      ⟩ := h_transpile
      rewrite [←h_data_imm]
      have := Transpiler.transpiler_opcode_532 h_instruction
      simp [h_data_opcode, h_opcode] at this
      have h_alignment := Transpiler.pc_aligned_of_some h_instruction
      have h_bound := Transpiler.pc_bound_of_some h_instruction
      obtain
        ⟨_, imm, rs1, h_instruction_load⟩
      := this
      all_goals {
        rewrite [h_instruction_load] at h_instruction
        unfold Transpiler.transpile_op at h_instruction
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
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
    . have h_imm_extended_range := LoadW.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
      have h_split_imm_extended := split_bitvec_16_to_8s h_imm_extended_range
      simp [BitVec.ofNat, Nat.cast] at h_split_imm_extended
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm_extended
      dsimp at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt]
      rewrite [←h_split_imm_extended]
      have := StoreH.imm_sign_extend_of_opcode_532 air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [this]
      simp [BitVec.ofNat, Nat.cast]
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
      dsimp
      simp (disch := omega) [Nat.mod_eq_of_lt]

lemma sh_spec_sign_extend_eq_imm [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 532)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    U32.toBV
    #v[
      { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
      { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
      { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
      { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
    ] =
    BitVec.signExtend 32 (BitVec.ofNat 16 ↑(air.adapter.imm row 0))
  := by
    simp [U32.toBV]
    have := StoreH.imm_sign_extend_of_opcode_532 air row h_opcode h_is_valid h_bus_wellformedness
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
        have := LoadW.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
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
        have := StoreH.imm_range_of_opcode_532 air row h_opcode h_is_valid h_bus_wellformedness
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
      }

lemma sh_spec_imm_sign [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 532)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    air.adapter.imm_sign row 0 =
    ↑(
      U32.toBV
        #v[
          { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
          { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
        ]
    ).msb.toNat
  := by
    have := StoreH.imm_sign_of_opcode_532 air row h_bus_wellformedness h_is_valid h_opcode
    rewrite [this]; clear this
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) : (bv1 ++ bv2 ++ bv3 ++ bv4).msb = bv1.msb := by bv_decide
    simp [this]
    have := StoreH.imm_extend_range_of_opcode_532 air row h_row h_constraints h_is_valid
    have :
      (air.adapter.imm_extended_limb row 0).val / 256 % 256 =
      (air.adapter.imm_extended_limb row 0).val / 256
    := by
      omega
    simp [this]
    have h_sign_extend := StoreH.imm_sign_extend_of_opcode_532 air row h_opcode h_is_valid h_bus_wellformedness
    have (bv1 bv2: BitVec 32): bv1 = bv2 → bv1.msb = bv2.msb := by intro h; grind
    apply this at h_sign_extend
    have (bv: BitVec 16) : (bv.signExtend 32).msb = bv.msb := by bv_decide
    rewrite [this] at h_sign_extend
    rewrite [h_sign_extend]
    have (bv1 bv2: BitVec 16): (bv1 ++ bv2).msb = bv1.msb := by bv_decide
    rewrite [this]
    have (a b : Bool) : (a.toNat: FBB) = (b.toNat: FBB) ↔ a = b := by cases a <;> cases b <;> decide
    rewrite [this]
    simp [BitVec.msb, BitVec.getMsbD, Nat.testBit]
    rewrite [Nat.mod_eq_of_lt (by omega)]
    unfold getElem BitVec.instGetElemNatBoolLt
    simp only [BitVec.getLsb, Nat.testBit]
    simp
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow,
    ]
    simp
    rewrite [Nat.div_div_eq_div_mul]
    simp

set_option maxHeartbeats 0 in
  lemma sh_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 532 →
        ShOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_STOREH_sh_pure
            (ShInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode

    simp [
      ShOutput_matches_LoadStore_instruction_fields,
      get_instruction_fields_row,
      -BitVec.toNat_add
    ]
    repeat rw [BitVec.toNat_add]
    simp
    rewrite [allHold_allRows] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    specialize h_bus_axioms row h_row
    specialize h_bus_wellformedness row h_row
    simp [
      ShInput_of_LoadStore_instruction_fields,
      PureSpec.execute_STOREH_sh_pure,
      -BitVec.toNat_add
    ]
    have h_needs_write := StoreH.needs_write_of_opcode_532 air row h_bus_wellformedness h_is_valid h_opcode
    have h_bus_wellformedness' := h_bus_wellformedness
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification,
          h_is_valid,
          h_needs_write,
          show (((-1) : FBB) = 2013265920) by native_decide,
          and_assoc] at h_bus_wellformedness'
    obtain ⟨ hwf01, hwf02, hwf03, hwf04, hwf05, hwf06, hwf07, hwf08, hwf09, hwf10,
             hwf11, hwf12, hwf13, hwf14, hwf15, hwf16, hwf17, hwf18, hwf19, hwf20,
             hwf21, hwf22, hwf23, hwf24, hwf25, hwf26 ⟩ := h_bus_wellformedness'
    have h_constraints' := h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints'
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints'
    simp [h_is_valid, h_needs_write] at h_constraints'
    obtain ⟨
      h_interactions,
      h_flag_0_le_2,
      h_flag_1_le_2,
      h_flag_2_le_2,
      h_flag_3_le_2,
      h_sum_le_2,
      h_sum_1_or_2_of_is_valid,
      h_is_load_def,
      h_wd_0,
      h_wd_1,
      h_wd_2,
      h_wd_3,
      h_ts_0,
      h_carry_boolean,
      h_imm_sign_boolean,
      h_carry'_boolean,
      h_mem_as,
      h_ts_1,
      h_ts_2
    ⟩ := h_constraints'
    have h_imm_range        := StoreH.imm_range_of_opcode_532 air row h_opcode h_is_valid h_bus_wellformedness
    have h_imm_extend_range := StoreH.imm_extend_range_of_opcode_532 air row h_row h_constraints h_is_valid
    have h_read_as          := StoreH.read_as_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid
    have h_read_ptr         := StoreH.read_ptr_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid
    have h_write_as         := StoreH.write_as_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid
    have h_shift_amount     := StoreH.shift_amount_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid
    have h_ptr_range        := StoreH.mem_ptr_range_of_opcode_532 air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
    have h_eq_shift : air.core.store_shift_amount row 0 = air.shift_amount row 0 := by
      rewrite [h_shift_amount]
      exact StoreH.store_shift_amount_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid
    have h_imm_upper : (air.adapter.imm row 0).val / 256 % 256 = (air.adapter.imm row 0).val / 256
      := by clear *- h_imm_range; rw [Nat.mod_eq_of_lt (by omega)]
    have h_imm_ext_upper : (air.adapter.imm_extended_limb row 0).val / 256 % 256 = (air.adapter.imm_extended_limb row 0).val / 256
      := by clear *- h_imm_extend_range; rw [Nat.mod_eq_of_lt (by omega)]
    simp [U32.toBV, h_imm_upper, h_imm_ext_upper, -BitVec.toNat_add]
    split_ands <;> try assumption
    . clear *-; omega
    . clear *- h_imm_range; omega
    . clear *-; omega
    . clear *- h_imm_extend_range; omega
    . clear *- h_shift_amount; grind
    . have := sh_spec_imm_eq air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness (by omega) (by omega) (by omega) (by omega)
      clear *- this
      simp [U32.toBV, h_imm_upper, h_imm_ext_upper] at this
      rw [this]
    . have := sh_spec_sign_extend_eq_imm air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness (by omega) (by omega) (by omega) (by omega)
      clear *- this
      simp [U32.toBV, h_imm_upper, h_imm_ext_upper] at this
      rw [← this]
    . have := sh_spec_imm_sign air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness (by omega) (by omega) (by omega) (by omega)
      clear *- this
      simp [this, h_imm_upper, h_imm_ext_upper]
      simp_all [U32.toBV]
    . rw [StoreH.write_data_0_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid, h_shift_amount]
      clear *-; split_ifs <;> grind
    . rw [StoreH.write_data_1_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid, h_shift_amount]
      clear *-; split_ifs <;> grind
    . rw [StoreH.write_data_2_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid, h_shift_amount]
      clear *-; split_ifs <;> grind
    . rw [StoreH.write_data_3_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid, h_shift_amount]
      clear *-; split_ifs <;> grind
    . simp [
        Valid_VmAirWrapper_loadstore.to_pc
      ]
      have h_execution := h_bus_axioms.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid
      ] at h_execution
      rewrite [Fin.val_add, Nat.mod_eq_of_lt, BitVec.ofNat_add]
      . simp
      . omega
    . have h_shift_eq : air.shift_amount row 0 = air.core.store_shift_amount row 0
        := by rw [h_shift_amount, StoreH.store_shift_amount_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid]
      simp only [U32.toNat]
      rewrite [
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
      ]
      simp
      have := StoreH.write_ptr_of_opcode_532 air row h_opcode h_row h_constraints h_is_valid
      rewrite [this]; clear this
      have h_mem_ptr := StoreH.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
      have h_imm_sign_extend := StoreH.imm_sign_extend_of_opcode_532 air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [h_imm_sign_extend] at h_mem_ptr
      rewrite [BitVec.toNat_eq] at h_mem_ptr
      simp [-BitVec.toNat_add] at h_mem_ptr
      rewrite [BitVec.toNat_add] at h_mem_ptr
      simp at h_mem_ptr
      rewrite [Nat.mod_eq_of_lt (by omega)] at h_mem_ptr
      rw [← h_shift_eq]
      rw [Fin.sub_val_of_le
          (by simp [h_shift_amount] at h_ptr_range ⊢
              clear *- h_ptr_range
              split_ifs with h_if <;>
              simp_all;
              clear h_if;
              omega)]
      rewrite [h_mem_ptr]; clear h_mem_ptr
      congr
      rewrite [BitVec.toNat_ofFin]
      simp
      have (x y: ℕ) :
        (BitVec.setWidth 32 (BitVec.ofNat 16 x)) <<< 16 +
        (BitVec.setWidth 32 (BitVec.ofNat 16 y)) =
        (BitVec.ofNat 16 x) ++ (BitVec.ofNat 16 y)
      := by bv_decide
      rewrite [←this]; clear this
      rewrite [BitVec.toNat_add]
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
    . rw [BitVec.toNat_add]
      rw [add_comm]; congr
      . rw [← U32.toBV_toNat, BitVec.toNat_inj]
        simp [U32.toBV]
        have := sh_spec_imm_eq air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness (by omega) (by omega) (by omega) (by omega)
        clear *- this
        simp [U32.toBV, h_imm_upper, h_imm_ext_upper] at this
        rw [this]
      . rw [← U32.toBV_toNat, BitVec.toNat_inj]
        simp [U32.toBV]
    . simp [BitVec.extractLsb]
      rw [BitVec.extractLsb'_append_eq_of_add_le (by simp)]
      simp; rfl
    . rw [BitVec.toNat_add]
      rw [add_comm]; congr
      . rw [← U32.toBV_toNat, BitVec.toNat_inj]
        simp [U32.toBV]
        have := sh_spec_imm_eq air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness (by omega) (by omega) (by omega) (by omega)
        clear *- this
        simp [U32.toBV, h_imm_upper, h_imm_ext_upper] at this
        rw [this]
      . rw [← U32.toBV_toNat, BitVec.toNat_inj]
        simp [U32.toBV]
    . simp [BitVec.extractLsb]
      rw [BitVec.extractLsb'_append_eq_of_le (by simp)]
      rw [BitVec.extractLsb'_append_eq_of_add_le (by simp)]
      simp; rfl

  /-
     ***
     *** SB
     ***
  -/

  def SbInput_of_LoadStore_instruction_fields (row : LoadStore_instruction_fields) : PureSpec.SbInput := {
      r1 := BitVec.ofFin (wrap_to_regidx row.rs1)
      imm := BabyBear.toBV32 row.imm
      r2 := BitVec.ofFin (wrap_to_regidx row.rd)
      r1_val := BabyBear.toBV32 row.rs1_val
      r2_val := BabyBear.toBV32 row.prev_read_data
      PC := row.pc.toNat
      mstatus := config.mstatus
      cur_privilege := config.cur_privilege
      plat_clint_base := config.plat_clint_base
      plat_clint_size := config.plat_clint_size
      plat_ram_base := config.plat_ram_base
      plat_ram_size := config.plat_ram_size
      plat_rom_base := config.plat_rom_base
      plat_rom_size := config.plat_rom_size
      htif_tohost_base := config.htif_tohost_base
      : PureSpec.SbInput
    }

  def SbOutput_matches_LoadStore_instruction_fields (row : LoadStore_instruction_fields) (sh_output : PureSpec.SbOutput) : Prop :=
    BabyBear.isU32 row.imm ∧
    BabyBear.isU32 row.rs1_val ∧
    BabyBear.isU32 row.prev_read_data ∧
    BabyBear.isU32 row.read_data ∧
    row.needs_write = 1 ∧
    row.read_address_space = 1 ∧
    row.read_ptr = row.rd ∧
    row.write_address_space = row.memory_address_space ∧
    row.prev_read_data = row.read_data ∧
    (row.shift.val < 4) ∧
    BitVec.signExtend 32 (BitVec.setWidth 12 (BabyBear.toBV32 row.imm)) = BabyBear.toBV32 row.imm ∧
    BabyBear.toBV32 row.imm = BitVec.signExtend 32 (BitVec.ofNat 16 row.imm_lower_half) ∧
    row.imm_sign = (BabyBear.toBV32 row.imm).msb.toNat ∧
    row.write_data = #v[
      if (row.shift = 0) then row.read_data[0] else row.prev_write_data[0],
      if (row.shift = 1) then row.read_data[0] else row.prev_write_data[1],
      if (row.shift = 2) then row.read_data[0] else row.prev_write_data[2],
      if (row.shift = 3) then row.read_data[0] else row.prev_write_data[3]
    ] ∧
    -- Actual output characterisation
    sh_output.nextPC = row.next_pc.toNat ∧
    row.write_ptr.val = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat - row.shift.val ∧
    sh_output.data0.1 = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat ∧
    sh_output.data0.2 = row.read_data[0].toNat

  lemma sb_spec_imm_eq [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 533)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    BitVec.signExtend 32
    (BitVec.setWidth 12
      (U32.toBV
        #v[
          { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
          { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
        ]
      )
    ) =
    U32.toBV
      #v[
        { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
        { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
      ]
  := by
    have := StoreB.imm_sign_extend_of_opcode_533 air row h_opcode h_is_valid h_bus_wellformedness
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) :
      BitVec.setWidth 12 (bv1 ++ bv2 ++ bv3 ++ bv4) =
      BitVec.setWidth 12 (bv3 ++ bv4)
    := by bv_decide
    rewrite [this]; clear this
    -- combine the two halves of imm into BitVec.ofNat 16 imm
    have h_imm_range := StoreB.imm_range_of_opcode_533 air row h_opcode h_is_valid h_bus_wellformedness
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
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨
        instruction,
        multiplciity,
        data,
        ⟨h_instruction, _, _, h_data_opcode, _, _, h_data_imm, _⟩
      ⟩ := h_transpile
      rewrite [←h_data_imm]
      have := Transpiler.transpiler_opcode_533 h_instruction
      simp [h_data_opcode, h_opcode] at this
      have h_alignment := Transpiler.pc_aligned_of_some h_instruction
      have h_bound := Transpiler.pc_bound_of_some h_instruction
      obtain
        ⟨_, imm, rs1, h_instruction_load⟩
      := this
      all_goals {
        rewrite [h_instruction_load] at h_instruction
        unfold Transpiler.transpile_op at h_instruction
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
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
    . have h_imm_extended_range := LoadW.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
      have h_split_imm_extended := split_bitvec_16_to_8s h_imm_extended_range
      simp [BitVec.ofNat, Nat.cast] at h_split_imm_extended
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm_extended
      dsimp at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt]
      rewrite [←h_split_imm_extended]
      have := StoreB.imm_sign_extend_of_opcode_533 air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [this]
      simp [BitVec.ofNat, Nat.cast]
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
      dsimp
      simp (disch := omega) [Nat.mod_eq_of_lt]

lemma sb_spec_sign_extend_eq_imm [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 533)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    U32.toBV
    #v[
      { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
      { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
      { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
      { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
    ] =
    BitVec.signExtend 32 (BitVec.ofNat 16 ↑(air.adapter.imm row 0))
  := by
    simp [U32.toBV]
    have := StoreB.imm_sign_extend_of_opcode_533 air row h_opcode h_is_valid h_bus_wellformedness
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
        have := LoadW.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
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
        have := StoreB.imm_range_of_opcode_533 air row h_opcode h_is_valid h_bus_wellformedness
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
      }

lemma sb_spec_imm_sign [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 533)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    air.adapter.imm_sign row 0 =
    ↑(
      U32.toBV
        #v[
          { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
          { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
        ]
    ).msb.toNat
  := by
    have := StoreB.imm_sign_of_opcode_533 air row h_bus_wellformedness h_is_valid h_opcode
    rewrite [this]; clear this
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) : (bv1 ++ bv2 ++ bv3 ++ bv4).msb = bv1.msb := by bv_decide
    simp [this]
    have := StoreB.imm_extend_range_of_opcode_533 air row h_row h_constraints h_is_valid
    have :
      (air.adapter.imm_extended_limb row 0).val / 256 % 256 =
      (air.adapter.imm_extended_limb row 0).val / 256
    := by
      omega
    simp [this]
    have h_sign_extend := StoreB.imm_sign_extend_of_opcode_533 air row h_opcode h_is_valid h_bus_wellformedness
    have (bv1 bv2: BitVec 32): bv1 = bv2 → bv1.msb = bv2.msb := by intro h; grind
    apply this at h_sign_extend
    have (bv: BitVec 16) : (bv.signExtend 32).msb = bv.msb := by bv_decide
    rewrite [this] at h_sign_extend
    rewrite [h_sign_extend]
    have (bv1 bv2: BitVec 16): (bv1 ++ bv2).msb = bv1.msb := by bv_decide
    rewrite [this]
    have (a b : Bool) : (a.toNat: FBB) = (b.toNat: FBB) ↔ a = b := by cases a <;> cases b <;> decide
    rewrite [this]
    simp [BitVec.msb, BitVec.getMsbD, Nat.testBit]
    rewrite [Nat.mod_eq_of_lt (by omega)]
    unfold getElem BitVec.instGetElemNatBoolLt
    simp only [BitVec.getLsb, Nat.testBit]
    simp
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow,
    ]
    simp
    rewrite [Nat.div_div_eq_div_mul]
    simp

set_option maxHeartbeats 0 in
  lemma sb_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 533 →
        SbOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_STOREB_sb_pure
            (SbInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode

    simp [
      SbOutput_matches_LoadStore_instruction_fields,
      get_instruction_fields_row,
      -BitVec.toNat_add
    ]
    repeat rw [BitVec.toNat_add]
    simp
    rewrite [allHold_allRows] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    specialize h_bus_axioms row h_row
    specialize h_bus_wellformedness row h_row
    simp [
      SbInput_of_LoadStore_instruction_fields,
      PureSpec.execute_STOREB_sb_pure,
      -BitVec.toNat_add
    ]
    have h_needs_write := StoreB.needs_write_of_opcode_533 air row h_bus_wellformedness h_is_valid h_opcode
    have h_bus_wellformedness' := h_bus_wellformedness
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification,
          h_is_valid,
          h_needs_write,
          show (((-1) : FBB) = 2013265920) by native_decide,
          and_assoc] at h_bus_wellformedness'
    obtain ⟨ hwf01, hwf02, hwf03, hwf04, hwf05, hwf06, hwf07, hwf08, hwf09, hwf10,
             hwf11, hwf12, hwf13, hwf14, hwf15, hwf16, hwf17, hwf18, hwf19, hwf20,
             hwf21, hwf22, hwf23, hwf24, hwf25, hwf26 ⟩ := h_bus_wellformedness'
    have h_constraints' := h_constraints
    rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints'
    simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints'
    simp [h_is_valid, h_needs_write] at h_constraints'
    obtain ⟨
      h_interactions,
      h_flag_0_le_2,
      h_flag_1_le_2,
      h_flag_2_le_2,
      h_flag_3_le_2,
      h_sum_le_2,
      h_sum_1_or_2_of_is_valid,
      h_is_load_def,
      h_wd_0,
      h_wd_1,
      h_wd_2,
      h_wd_3,
      h_ts_0,
      h_carry_boolean,
      h_imm_sign_boolean,
      h_carry'_boolean,
      h_mem_as,
      h_ts_1,
      h_ts_2
    ⟩ := h_constraints'
    have h_imm_range        := StoreB.imm_range_of_opcode_533 air row h_opcode h_is_valid h_bus_wellformedness
    have h_imm_extend_range := StoreB.imm_extend_range_of_opcode_533 air row h_row h_constraints h_is_valid
    have h_read_as          := StoreB.read_as_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid
    have h_read_ptr         := StoreB.read_ptr_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid
    have h_write_as         := StoreB.write_as_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid
    have h_shift_amount     := StoreB.shift_amount_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid
    have h_ptr_range        := StoreB.mem_ptr_range_of_opcode_533 air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
    have h_eq_shift : air.core.store_shift_amount row 0 = air.shift_amount row 0 := by
      rewrite [h_shift_amount]
      exact StoreB.store_shift_amount_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid
    have h_imm_upper : (air.adapter.imm row 0).val / 256 % 256 = (air.adapter.imm row 0).val / 256
      := by clear *- h_imm_range; rw [Nat.mod_eq_of_lt (by omega)]
    have h_imm_ext_upper : (air.adapter.imm_extended_limb row 0).val / 256 % 256 = (air.adapter.imm_extended_limb row 0).val / 256
      := by clear *- h_imm_extend_range; rw [Nat.mod_eq_of_lt (by omega)]
    simp [U32.toBV, h_imm_upper, h_imm_ext_upper, -BitVec.toNat_add]
    split_ands <;> try assumption
    . clear *-; omega
    . clear *- h_imm_range; omega
    . clear *-; omega
    . clear *- h_imm_extend_range; omega
    . clear *- h_shift_amount; grind
    . have := sb_spec_imm_eq air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness (by omega) (by omega) (by omega) (by omega)
      clear *- this
      simp [U32.toBV, h_imm_upper, h_imm_ext_upper] at this
      rw [this]
    . have := sb_spec_sign_extend_eq_imm air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness (by omega) (by omega) (by omega) (by omega)
      clear *- this
      simp [U32.toBV, h_imm_upper, h_imm_ext_upper] at this
      rw [← this]
    . have := sb_spec_imm_sign air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness (by omega) (by omega) (by omega) (by omega)
      clear *- this
      simp [this, h_imm_upper, h_imm_ext_upper]
      simp_all [U32.toBV]
    . rw [StoreB.write_data_0_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid, h_shift_amount]
      clear *-; split_ifs <;> grind
    . rw [StoreB.write_data_1_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid, h_shift_amount]
      clear *-; split_ifs <;> grind
    . rw [StoreB.write_data_2_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid, h_shift_amount]
      clear *-; split_ifs <;> grind
    . rw [StoreB.write_data_3_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid, h_shift_amount]
      clear *-; split_ifs <;> grind
    . simp [
        Valid_VmAirWrapper_loadstore.to_pc
      ]
      have h_execution := h_bus_axioms.1
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid
      ] at h_execution
      rewrite [Fin.val_add, Nat.mod_eq_of_lt, BitVec.ofNat_add]
      . simp
      . omega
    . have h_shift_eq : air.shift_amount row 0 = air.core.store_shift_amount row 0
        := by rw [h_shift_amount, StoreB.store_shift_amount_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid]
      simp only [U32.toNat]
      rewrite [
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
        BitVec.toNat_ofFin,
      ]
      simp
      have := StoreB.write_ptr_of_opcode_533 air row h_opcode h_row h_constraints h_is_valid
      rewrite [this]; clear this
      have h_mem_ptr := StoreB.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
      have h_imm_sign_extend := StoreB.imm_sign_extend_of_opcode_533 air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [h_imm_sign_extend] at h_mem_ptr
      rewrite [BitVec.toNat_eq] at h_mem_ptr
      simp [-BitVec.toNat_add] at h_mem_ptr
      rewrite [BitVec.toNat_add] at h_mem_ptr
      simp at h_mem_ptr
      rewrite [Nat.mod_eq_of_lt (by omega)] at h_mem_ptr
      rw [← h_shift_eq]
      rw [Fin.sub_val_of_le
          (by simp [h_shift_amount] at h_ptr_range ⊢
              clear *- h_ptr_range
              split_ifs with h1 h2 h3
              all_goals
                simp [*] at h_ptr_range
                omega)]
      rewrite [h_mem_ptr]; clear h_mem_ptr
      congr
      rewrite [BitVec.toNat_ofFin]
      simp
      have (x y: ℕ) :
        (BitVec.setWidth 32 (BitVec.ofNat 16 x)) <<< 16 +
        (BitVec.setWidth 32 (BitVec.ofNat 16 y)) =
        (BitVec.ofNat 16 x) ++ (BitVec.ofNat 16 y)
      := by bv_decide
      rewrite [←this]; clear this
      rewrite [BitVec.toNat_add]
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
    . rw [BitVec.toNat_add]
      rw [add_comm]; congr
      . rw [← U32.toBV_toNat, BitVec.toNat_inj]
        simp [U32.toBV]
        have := sb_spec_imm_eq air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness (by omega) (by omega) (by omega) (by omega)
        clear *- this
        simp [U32.toBV, h_imm_upper, h_imm_ext_upper] at this
        rw [this]
      . rw [← U32.toBV_toNat, BitVec.toNat_inj]
        simp [U32.toBV]
    . simp [BitVec.extractLsb]
      rw [BitVec.extractLsb'_append_eq_of_add_le (by simp)]
      simp; rfl

  /-
     ***
     *** LW
     ***
  -/

  def LwInput_of_LoadStore_instruction_fields (row : LoadStore_instruction_fields) : PureSpec.LwInput := {
    r1 := BitVec.ofFin (wrap_to_regidx row.rs1)
    imm := BabyBear.toBV32 row.imm
    rd := BitVec.ofFin (wrap_to_regidx row.rd)
    r1_val := BabyBear.toBV32 row.rs1_val
    PC := row.pc.toNat
    mstatus := config.mstatus
    cur_privilege := config.cur_privilege
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

  lemma lw_spec_of_get_instruction_fields_part_1 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
  :
    (air.adapter.imm row 0).val % 256 < 256
  := by
    omega

  lemma lw_spec_of_get_instruction_fields_part_2 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.imm row 0).val / 256 < 256
  := by
    have := LoadW.imm_range_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
    omega

  lemma lw_spec_of_get_instruction_fields_part_3 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
  :
    (air.adapter.imm_extended_limb row 0).val % 256 < 256
  := by
    omega

  lemma lw_spec_of_get_instruction_fields_part_4 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
  :
    (air.adapter.imm_extended_limb row 0).val / 256 < 256
  := by
    have := LoadW.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
    omega

  lemma lw_spec_of_get_instruction_fields_part_5 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_0 row 0).val < 256
  := by
    have := LoadW.rs1_data_0_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lw_spec_of_get_instruction_fields_part_6 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_1 row 0).val < 256
  := by
    have := LoadW.rs1_data_1_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lw_spec_of_get_instruction_fields_part_7 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_2 row 0).val < 256
  := by
    have := LoadW.rs1_data_2_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lw_spec_of_get_instruction_fields_part_8 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_3 row 0).val < 256
  := by
    have := LoadW.rs1_data_3_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lw_spec_of_get_instruction_fields_part_9 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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
    (h_is_valid : air.core.is_valid row 0 = 1)
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
    (h_is_valid : air.core.is_valid row 0 = 1)
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
    (h_is_valid : air.core.is_valid row 0 = 1)
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
    (h_is_valid : air.core.is_valid row 0 = 1)
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
    have h_0 := LoadW.write_data_0_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_1 := LoadW.write_data_1_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_2 := LoadW.write_data_2_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    have h_3 := LoadW.write_data_3_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    rewrite [h_0, h_1, h_2, h_3]
    split_ands
    . exact h_memory.2.1.2.2.1
    . exact h_memory.2.1.2.2.2.1
    . exact h_memory.2.1.2.2.2.2.1
    . exact h_memory.2.1.2.2.2.2.2

  lemma lw_spec_of_get_instruction_fields_part_15 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
  :
    BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32 =
    BitVec.ofNat 32 (air.to_pc row 0).val
  := by
    simp [
      Valid_VmAirWrapper_loadstore.to_pc
    ]
    have h_execution := h_bus_axioms.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_execution
    rewrite [Fin.val_add, Nat.mod_eq_of_lt, BitVec.ofNat_add]
    . simp
    . omega

  lemma lw_spec_of_get_instruction_fields_part_16 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
    (h5 : (air.adapter.rs1_data_0 row 0).val % 256 < 2 ^ 8)
    (h6 : (air.adapter.rs1_data_1 row 0).val % 256 < 2 ^ 8)
    (h7 : (air.adapter.rs1_data_2 row 0).val % 256 < 2 ^ 8)
    (h8 : (air.adapter.rs1_data_3 row 0).val % 256 < 2 ^ 8)
  :
    ↑(air.read_ptr row 0) =
    (
      U32.toNat #v[
        { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
        { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
      ] +
      U32.toNat #v[
        { toFin := ⟨↑(air.adapter.rs1_data_0 row 0) % 256, h5⟩ },
        { toFin := ⟨↑(air.adapter.rs1_data_1 row 0) % 256, h6⟩ },
        { toFin := ⟨↑(air.adapter.rs1_data_2 row 0) % 256, h7⟩ },
        { toFin := ⟨↑(air.adapter.rs1_data_3 row 0) % 256, h8⟩ }
      ]
    ) % 4294967296
  := by
    simp only [U32.toNat]
    rewrite [
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin
    ]
    simp
    have := LoadW.read_ptr_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    rewrite [this]; clear this
    have h_mem_ptr := LoadW.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    have h_imm_sign_extend := LoadW.imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
    rewrite [h_imm_sign_extend] at h_mem_ptr
    rewrite [BitVec.toNat_eq] at h_mem_ptr
    simp [-BitVec.toNat_add] at h_mem_ptr
    rewrite [BitVec.toNat_add] at h_mem_ptr
    simp at h_mem_ptr
    rewrite [Nat.mod_eq_of_lt (by omega)] at h_mem_ptr
    rewrite [h_mem_ptr]; clear h_mem_ptr
    congr
    rewrite [BitVec.toNat_ofFin]
    simp
    have (x y: ℕ) :
      (BitVec.setWidth 32 (BitVec.ofNat 16 x)) <<< 16 +
      (BitVec.setWidth 32 (BitVec.ofNat 16 y)) =
      (BitVec.ofNat 16 x) ++ (BitVec.ofNat 16 y)
    := by bv_decide
    rewrite [←this]; clear this
    rewrite [BitVec.toNat_add]
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

  lemma lw_spec_of_get_instruction_fields_part_17 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    BitVec.signExtend 32
    (BitVec.setWidth 12
      (U32.toBV
        #v[
          { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
          { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
        ]
      )
    ) =
    U32.toBV
      #v[
        { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
        { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
      ]
  := by
    have := LoadW.imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) :
      BitVec.setWidth 12 (bv1 ++ bv2 ++ bv3 ++ bv4) =
      BitVec.setWidth 12 (bv3 ++ bv4)
    := by bv_decide
    rewrite [this]; clear this
    -- combine the two halves of imm into BitVec.ofNat 16 imm
    have h_imm_range := LoadW.imm_range_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
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
        Interaction.ProgramBusEntry.operand_properties
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
      have h_bound := Transpiler.pc_bound_of_some h_instruction
      obtain
        ⟨_, imm, rs1, rd, h_instruction_load, _⟩ |
        ⟨_, imm, rs1, h_instruction_load⟩
      := this
      all_goals {
        rewrite [h_instruction_load] at h_instruction
        unfold Transpiler.transpile_op at h_instruction
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
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
    . have h_imm_extended_range := LoadW.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
      have h_split_imm_extended := split_bitvec_16_to_8s h_imm_extended_range
      simp [BitVec.ofNat, Nat.cast] at h_split_imm_extended
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm_extended
      dsimp at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt]
      rewrite [←h_split_imm_extended]
      have := LoadW.imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [this]
      simp [BitVec.ofNat, Nat.cast]
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
      dsimp
      simp (disch := omega) [Nat.mod_eq_of_lt]

  lemma lw_spec_of_get_instruction_fields_part_18 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    U32.toBV
    #v[
      { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
      { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
      { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
      { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
    ] =
    BitVec.signExtend 32 (BitVec.ofNat 16 ↑(air.adapter.imm row 0))
  := by
    simp [U32.toBV]
    have := LoadW.imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
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
        have := LoadW.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
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
        have := LoadW.imm_range_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
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
      }

  lemma lw_spec_of_get_instruction_fields_part_19 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 528)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    air.adapter.imm_sign row 0 =
    ↑(
      U32.toBV
        #v[
          { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
          { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
        ]
    ).msb.toNat
  := by
    have := LoadW.imm_sign_of_opcode_528 air row h_bus_wellformedness h_is_valid h_opcode
    rewrite [this]; clear this
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) : (bv1 ++ bv2 ++ bv3 ++ bv4).msb = bv1.msb := by bv_decide
    simp [this]
    have := LoadW.imm_extend_range_of_opcode_528 air row h_row h_constraints h_is_valid
    have :
      (air.adapter.imm_extended_limb row 0).val / 256 % 256 =
      (air.adapter.imm_extended_limb row 0).val / 256
    := by
      omega
    simp [this]
    have h_sign_extend := LoadW.imm_sign_extend_of_opcode_528 air row h_opcode h_is_valid h_bus_wellformedness
    have (bv1 bv2: BitVec 32): bv1 = bv2 → bv1.msb = bv2.msb := by intro h; grind
    apply this at h_sign_extend
    have (bv: BitVec 16) : (bv.signExtend 32).msb = bv.msb := by bv_decide
    rewrite [this] at h_sign_extend
    rewrite [h_sign_extend]
    have (bv1 bv2: BitVec 16): (bv1 ++ bv2).msb = bv1.msb := by bv_decide
    rewrite [this]
    have (a b : Bool) : (a.toNat: FBB) = (b.toNat: FBB) ↔ a = b := by cases a <;> cases b <;> decide
    rewrite [this]
    simp [BitVec.msb, BitVec.getMsbD, Nat.testBit]
    rewrite [Nat.mod_eq_of_lt (by omega)]
    unfold getElem BitVec.instGetElemNatBoolLt
    simp only [BitVec.getLsb, Nat.testBit]
    simp
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow,
    ]
    simp
    rewrite [Nat.div_div_eq_div_mul]
    simp

  set_option maxHeartbeats 0 in
  lemma lw_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
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
    rewrite [BitVec.toNat_add]
    simp

    rewrite [allHold_allRows] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    specialize h_bus_axioms row h_row
    specialize h_bus_wellformedness row h_row
    simp [LwInput_of_LoadStore_instruction_fields, PureSpec.execute_LOAD_lw_pure]

    split_ands
    . exact lw_spec_of_get_instruction_fields_part_1 air row
    . exact lw_spec_of_get_instruction_fields_part_2 air row h_is_valid h_opcode h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_3 air row
    . exact lw_spec_of_get_instruction_fields_part_4 air row h_row h_is_valid h_constraints
    . exact lw_spec_of_get_instruction_fields_part_5 air row h_is_valid h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_6 air row h_is_valid h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_7 air row h_is_valid h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_8 air row h_is_valid h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_9 air row h_is_valid h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_10 air row h_is_valid h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_11 air row h_is_valid h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_12 air row h_is_valid h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_13 air row h_is_valid h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_14 air row h_row h_is_valid h_opcode h_constraints h_bus_wellformedness
    . exact lw_spec_of_get_instruction_fields_part_15 air row h_is_valid h_bus_axioms
    . exact LoadW.read_as_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    . exact LoadW.write_as_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    . apply lw_spec_of_get_instruction_fields_part_16 air row h_row h_is_valid h_opcode h_constraints h_bus_wellformedness
    . exact LoadW.write_ptr_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
    . apply lw_spec_of_get_instruction_fields_part_17 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . apply lw_spec_of_get_instruction_fields_part_18 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . apply lw_spec_of_get_instruction_fields_part_19 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . have h_transpile := h_bus_wellformedness.2.2.2
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨instruction, multiplicity, data, h_instruction⟩ := h_transpile
      have h_aligned := Transpiler.pc_aligned_of_some h_instruction.1
      have h_bound := Transpiler.pc_bound_of_some h_instruction.1
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
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
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
            have := LoadW.write_data_3_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := LoadW.write_data_2_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := LoadW.write_data_1_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := LoadW.write_data_0_of_opcode_528 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
          . grind
          . clear *-h_rd
            fin_cases rd
            . simp_all
            all_goals decide
        . clear *-h_rd
          obtain ⟨⟨rd: Fin 32⟩⟩ := rd
          simp
          convert h_rd
          omega
      . rewrite [h_instruction_load] at h_instruction
        unfold Transpiler.transpile_op at h_instruction
        dsimp at h_instruction
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
        simp [-Vector.mk_eq] at h_instruction
        rewrite [←h_instruction.2.2.2.2.1, ←h_instruction.1.2]
        simp [Transpiler.ind, wrap_to_regidx, regidx_to_fin]
        rewrite [←h_instruction.2.2.2.2.2.2.2.2.2.1, ←h_instruction.1.2]
        simp
        decide

  /-
     ***
     *** LHU
     ***
  -/

  def LhuInput_of_LoadStore_instruction_fields (row : LoadStore_instruction_fields) : PureSpec.LhuInput := {
    r1 := BitVec.ofFin (wrap_to_regidx row.rs1)
    imm := BabyBear.toBV32 row.imm
    rd := BitVec.ofFin (wrap_to_regidx row.rd)
    r1_val := BabyBear.toBV32 row.rs1_val
    PC := row.pc.toNat
    mstatus := config.mstatus
    cur_privilege := config.cur_privilege
    plat_clint_base := config.plat_clint_base
    plat_clint_size := config.plat_clint_size
    plat_ram_base := config.plat_ram_base
    plat_ram_size := config.plat_ram_size
    plat_rom_base := config.plat_rom_base
    plat_rom_size := config.plat_rom_size
    htif_tohost_base := config.htif_tohost_base
    data0 := if (row.shift = 0) then row.prev_read_data[0] else row.prev_read_data[2]
    data1 := if (row.shift = 0) then row.prev_read_data[1] else row.prev_read_data[3]
    : PureSpec.LhuInput
  }

  def LhuOutput_matches_LoadStore_instruction_fields (row : LoadStore_instruction_fields) (lhu_output : PureSpec.LhuOutput) : Prop :=
    BabyBear.isU32 row.imm ∧
    BabyBear.isU32 row.rs1_val ∧
    BabyBear.isU32 row.prev_read_data ∧
    BabyBear.isU32 row.read_data ∧
    (row.needs_write = 1 → BabyBear.isU32 row.prev_write_data) ∧
    (row.needs_write = 1 → BabyBear.isU32 row.write_data) ∧
    lhu_output.nextPC = row.next_pc.toNat ∧
    row.read_address_space = row.memory_address_space ∧
    row.write_address_space = 1 ∧
    row.read_ptr.val = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat - row.shift.val∧
    row.write_ptr = row.rd ∧
    row.prev_read_data = row.read_data ∧
    BitVec.signExtend 32 (BitVec.setWidth 12 (BabyBear.toBV32 row.imm)) = BabyBear.toBV32 row.imm ∧
    BabyBear.toBV32 row.imm = BitVec.signExtend 32 (BitVec.ofNat 16 row.imm_lower_half) ∧
    row.imm_sign = (BabyBear.toBV32 row.imm).msb.toNat ∧
    match lhu_output.rd with
      | .none =>
        row.rd = 0 ∧
        row.needs_write = 0
      | .some (rd, rd_val) =>
        BabyBear.toBV32 row.write_data = rd_val ∧
        rd.1.toNat * 4 = row.rd.toNat ∧
        row.needs_write = 1

  lemma lhu_spec_of_get_instruction_fields_part_1 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
  :
    (air.adapter.imm row 0).val % 256 < 256
  := by
    omega

  lemma lhu_spec_of_get_instruction_fields_part_2 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 530)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.imm row 0).val / 256 < 256
  := by
    have := LoadHU.imm_range_of_opcode_530 air row h_opcode h_is_valid h_bus_wellformedness
    omega

  lemma lhu_spec_of_get_instruction_fields_part_3 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
  :
    (air.adapter.imm_extended_limb row 0).val % 256 < 256
  := by
    omega

  lemma lhu_spec_of_get_instruction_fields_part_4 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
  :
    (air.adapter.imm_extended_limb row 0).val / 256 < 256
  := by
    have := LoadHU.imm_extend_range_of_opcode_530 air row h_row h_constraints h_is_valid
    omega

  lemma lhu_spec_of_get_instruction_fields_part_5 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_0 row 0).val < 256
  := by
    have := LoadHU.rs1_data_0_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lhu_spec_of_get_instruction_fields_part_6 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_1 row 0).val < 256
  := by
    have := LoadHU.rs1_data_1_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lhu_spec_of_get_instruction_fields_part_7 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_2 row 0).val < 256
  := by
    have := LoadHU.rs1_data_2_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lhu_spec_of_get_instruction_fields_part_8 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_3 row 0).val < 256
  := by
    have := LoadHU.rs1_data_3_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lhu_spec_of_get_instruction_fields_part_9 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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

  lemma lhu_spec_of_get_instruction_fields_part_10 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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

  lemma lhu_spec_of_get_instruction_fields_part_11 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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

  lemma lhu_spec_of_get_instruction_fields_part_12 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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

  lemma lhu_spec_of_get_instruction_fields_part_13 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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

  lemma lhu_spec_of_get_instruction_fields_part_14 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 530)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
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
    have h_0 := LoadHU.write_data_0_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
    have h_1 := LoadHU.write_data_1_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
    have h_2 := LoadHU.write_data_2_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
    have h_3 := LoadHU.write_data_3_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
    rewrite [h_0, h_1, h_2, h_3]
    split_ands <;> simp <;> split_ifs <;> grind

  lemma lhu_spec_of_get_instruction_fields_part_15 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
  :
    BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32 =
    BitVec.ofNat 32 (air.to_pc row 0).val
  := by
    simp [
      Valid_VmAirWrapper_loadstore.to_pc
    ]
    have h_execution := h_bus_axioms.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_execution
    rewrite [Fin.val_add, Nat.mod_eq_of_lt, BitVec.ofNat_add]
    . simp
    . omega

  set_option maxHeartbeats 0 in
  lemma lhu_spec_of_get_instruction_fields_part_16 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 530)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
    (h5 : (air.adapter.rs1_data_0 row 0).val % 256 < 2 ^ 8)
    (h6 : (air.adapter.rs1_data_1 row 0).val % 256 < 2 ^ 8)
    (h7 : (air.adapter.rs1_data_2 row 0).val % 256 < 2 ^ 8)
    (h8 : (air.adapter.rs1_data_3 row 0).val % 256 < 2 ^ 8)
  :
    ↑(air.read_ptr row 0) =
    (
      U32.toNat #v[
        { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
        { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
      ] +
      U32.toNat #v[
        { toFin := ⟨↑(air.adapter.rs1_data_0 row 0) % 256, h5⟩ },
        { toFin := ⟨↑(air.adapter.rs1_data_1 row 0) % 256, h6⟩ },
        { toFin := ⟨↑(air.adapter.rs1_data_2 row 0) % 256, h7⟩ },
        { toFin := ⟨↑(air.adapter.rs1_data_3 row 0) % 256, h8⟩ }
      ]
    ) % 4294967296 - (air.shift_amount row 0).val
  := by
    simp only [U32.toNat]
    rewrite [
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin
    ]
    simp
    have := LoadHU.read_ptr_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
    rewrite [this]; clear this
    have h_mem_ptr := LoadHU.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    have h_imm_sign_extend := LoadHU.imm_sign_extend_of_opcode_530 air row h_opcode h_is_valid h_bus_wellformedness
    rewrite [h_imm_sign_extend] at h_mem_ptr
    rewrite [BitVec.toNat_eq] at h_mem_ptr
    simp [-BitVec.toNat_add] at h_mem_ptr
    rewrite [BitVec.toNat_add] at h_mem_ptr
    simp at h_mem_ptr
    rewrite [Nat.mod_eq_of_lt (by omega)] at h_mem_ptr
    rw [Fin.sub_val_of_le
        (by have h_ptr_range := LoadHU.mem_ptr_range_of_opcode_530 air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
            simp [LoadHU.shift_amount_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid] at h_ptr_range ⊢
            clear *- h_ptr_range
            split_ifs with h_if <;>
            simp_all;
            clear h_if;
            omega)]
    rewrite [h_mem_ptr]; clear h_mem_ptr
    congr
    rewrite [BitVec.toNat_ofFin]
    simp
    have (x y: ℕ) :
      (BitVec.setWidth 32 (BitVec.ofNat 16 x)) <<< 16 +
      (BitVec.setWidth 32 (BitVec.ofNat 16 y)) =
      (BitVec.ofNat 16 x) ++ (BitVec.ofNat 16 y)
    := by bv_decide
    rewrite [←this]; clear this
    rewrite [BitVec.toNat_add]
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

  lemma lhu_spec_of_get_instruction_fields_part_17 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 530)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    BitVec.signExtend 32
    (BitVec.setWidth 12
      (U32.toBV
        #v[
          { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
          { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
        ]
      )
    ) =
    U32.toBV
      #v[
        { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
        { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
      ]
  := by
    have := LoadHU.imm_sign_extend_of_opcode_530 air row h_opcode h_is_valid h_bus_wellformedness
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) :
      BitVec.setWidth 12 (bv1 ++ bv2 ++ bv3 ++ bv4) =
      BitVec.setWidth 12 (bv3 ++ bv4)
    := by bv_decide
    rewrite [this]; clear this
    -- combine the two halves of imm into BitVec.ofNat 16 imm
    have h_imm_range := LoadHU.imm_range_of_opcode_530 air row h_opcode h_is_valid h_bus_wellformedness
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
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨
        instruction,
        multiplciity,
        data,
        ⟨h_instruction, _, _, h_data_opcode, _, _, h_data_imm, _⟩
      ⟩ := h_transpile
      rewrite [←h_data_imm]
      have := Transpiler.transpiler_opcode_530 h_instruction
      simp [h_data_opcode, h_opcode] at this
      have h_alignment := Transpiler.pc_aligned_of_some h_instruction
      have h_bound := Transpiler.pc_bound_of_some h_instruction
      obtain
        ⟨_, imm, rs1, rd, h_instruction_load, _⟩ |
        ⟨_, imm, rs1, h_instruction_load⟩
      := this
      all_goals {
        rewrite [h_instruction_load] at h_instruction
        unfold Transpiler.transpile_op at h_instruction
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
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
    . have h_imm_extended_range := LoadHU.imm_extend_range_of_opcode_530 air row h_row h_constraints h_is_valid
      have h_split_imm_extended := split_bitvec_16_to_8s h_imm_extended_range
      simp [BitVec.ofNat, Nat.cast] at h_split_imm_extended
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm_extended
      dsimp at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt]
      rewrite [←h_split_imm_extended]
      have := LoadHU.imm_sign_extend_of_opcode_530 air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [this]
      simp [BitVec.ofNat, Nat.cast]
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
      dsimp
      simp (disch := omega) [Nat.mod_eq_of_lt]

  lemma lhu_spec_of_get_instruction_fields_part_18 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 530)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    U32.toBV
    #v[
      { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
      { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
      { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
      { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
    ] =
    BitVec.signExtend 32 (BitVec.ofNat 16 ↑(air.adapter.imm row 0))
  := by
    simp [U32.toBV]
    have := LoadHU.imm_sign_extend_of_opcode_530 air row h_opcode h_is_valid h_bus_wellformedness
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
        have := LoadHU.imm_extend_range_of_opcode_530 air row h_row h_constraints h_is_valid
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
        have := LoadHU.imm_range_of_opcode_530 air row h_opcode h_is_valid h_bus_wellformedness
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
      }

  lemma lhu_spec_of_get_instruction_fields_part_19 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 530)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    air.adapter.imm_sign row 0 =
    ↑(
      U32.toBV
        #v[
          { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
          { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
        ]
    ).msb.toNat
  := by
    have := LoadHU.imm_sign_of_opcode_530 air row h_bus_wellformedness h_is_valid h_opcode
    rewrite [this]; clear this
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) : (bv1 ++ bv2 ++ bv3 ++ bv4).msb = bv1.msb := by bv_decide
    simp [this]
    have := LoadHU.imm_extend_range_of_opcode_530 air row h_row h_constraints h_is_valid
    have :
      (air.adapter.imm_extended_limb row 0).val / 256 % 256 =
      (air.adapter.imm_extended_limb row 0).val / 256
    := by
      omega
    simp [this]
    have h_sign_extend := LoadHU.imm_sign_extend_of_opcode_530 air row h_opcode h_is_valid h_bus_wellformedness
    have (bv1 bv2: BitVec 32): bv1 = bv2 → bv1.msb = bv2.msb := by intro h; grind
    apply this at h_sign_extend
    have (bv: BitVec 16) : (bv.signExtend 32).msb = bv.msb := by bv_decide
    rewrite [this] at h_sign_extend
    rewrite [h_sign_extend]
    have (bv1 bv2: BitVec 16): (bv1 ++ bv2).msb = bv1.msb := by bv_decide
    rewrite [this]
    have (a b : Bool) : (a.toNat: FBB) = (b.toNat: FBB) ↔ a = b := by cases a <;> cases b <;> decide
    rewrite [this]
    simp [BitVec.msb, BitVec.getMsbD, Nat.testBit]
    rewrite [Nat.mod_eq_of_lt (by omega)]
    unfold getElem BitVec.instGetElemNatBoolLt
    simp only [BitVec.getLsb, Nat.testBit]
    simp
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow,
    ]
    simp
    rewrite [Nat.div_div_eq_div_mul]
    simp

  set_option maxHeartbeats 0 in
  lemma lhu_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 530 →
        LhuOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_LOADHU_lhu_pure
            (LhuInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [
      LhuOutput_matches_LoadStore_instruction_fields,
      get_instruction_fields_row,
      -BitVec.toNat_add
    ]
    rewrite [BitVec.toNat_add]
    simp

    rewrite [allHold_allRows] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    specialize h_bus_axioms row h_row
    specialize h_bus_wellformedness row h_row
    simp [LhuInput_of_LoadStore_instruction_fields, PureSpec.execute_LOADHU_lhu_pure]

    split_ands
    . exact lhu_spec_of_get_instruction_fields_part_1 air row
    . exact lhu_spec_of_get_instruction_fields_part_2 air row h_is_valid h_opcode h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_3 air row
    . exact lhu_spec_of_get_instruction_fields_part_4 air row h_row h_is_valid h_constraints
    . exact lhu_spec_of_get_instruction_fields_part_5 air row h_is_valid h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_6 air row h_is_valid h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_7 air row h_is_valid h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_8 air row h_is_valid h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_9 air row h_is_valid h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_10 air row h_is_valid h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_11 air row h_is_valid h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_12 air row h_is_valid h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_13 air row h_is_valid h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_14 air row h_row h_is_valid h_opcode h_constraints h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields_part_15 air row h_is_valid h_bus_axioms
    . exact LoadHU.read_as_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
    . exact LoadHU.write_as_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
    . apply lhu_spec_of_get_instruction_fields_part_16 air row h_row h_is_valid h_opcode h_constraints h_bus_wellformedness
    . exact LoadHU.write_ptr_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
    . apply lhu_spec_of_get_instruction_fields_part_17 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . apply lhu_spec_of_get_instruction_fields_part_18 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . apply lhu_spec_of_get_instruction_fields_part_19 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . have h_transpile := h_bus_wellformedness.2.2.2
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨instruction, multiplicity, data, h_instruction⟩ := h_transpile
      have h_aligned := Transpiler.pc_aligned_of_some h_instruction.1
      have h_bound := Transpiler.pc_bound_of_some h_instruction.1
      have h_rd := Transpiler.transpiler_opcode_530 h_instruction.1
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
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
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
            have := LoadHU.write_data_3_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := LoadHU.write_data_2_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := LoadHU.write_data_1_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := LoadHU.write_data_0_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid
            simp [this, LoadHU.shift_amount_of_opcode_530 air row h_opcode h_row h_constraints h_is_valid]
            simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_bus_wellformedness
            split_ifs
            . clear *-; symm
              simp [BitVec.extend, ← BitVec.toNat_inj]
              repeat rw [BitVec.toNat_append]
              simp
              rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
              omega
            . clear *-; symm
              simp [BitVec.extend, ← BitVec.toNat_inj]
              repeat rw [BitVec.toNat_append]
              simp
              rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
              omega
          . grind
          . clear *-h_rd
            fin_cases rd
            . simp_all
            all_goals decide
        . clear *-h_rd
          obtain ⟨⟨rd: Fin 32⟩⟩ := rd
          simp
          convert h_rd
          omega
      . rewrite [h_instruction_load] at h_instruction
        unfold Transpiler.transpile_op at h_instruction
        dsimp at h_instruction
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
        simp [-Vector.mk_eq] at h_instruction
        rewrite [←h_instruction.2.2.2.2.1, ←h_instruction.1.2]
        simp [Transpiler.ind, wrap_to_regidx, regidx_to_fin]
        rewrite [←h_instruction.2.2.2.2.2.2.2.2.2.1, ←h_instruction.1.2]
        simp
        decide

  /-
     ***
     *** LBU
     ***
  -/

  def LbuInput_of_LoadStore_instruction_fields (row : LoadStore_instruction_fields) : PureSpec.LbuInput := {
    r1 := BitVec.ofFin (wrap_to_regidx row.rs1)
    imm := BabyBear.toBV32 row.imm
    rd := BitVec.ofFin (wrap_to_regidx row.rd)
    r1_val := BabyBear.toBV32 row.rs1_val
    PC := row.pc.toNat
    mstatus := config.mstatus
    cur_privilege := config.cur_privilege
    plat_clint_base := config.plat_clint_base
    plat_clint_size := config.plat_clint_size
    plat_ram_base := config.plat_ram_base
    plat_ram_size := config.plat_ram_size
    plat_rom_base := config.plat_rom_base
    plat_rom_size := config.plat_rom_size
    htif_tohost_base := config.htif_tohost_base
    data0 := if (row.shift = 0) then row.prev_read_data[0] else
             if (row.shift = 1) then row.prev_read_data[1] else
             if (row.shift = 2) then row.prev_read_data[2] else
                                     row.prev_read_data[3]
    : PureSpec.LbuInput
  }

  def LbuOutput_matches_LoadStore_instruction_fields (row : LoadStore_instruction_fields) (lbu_output : PureSpec.LbuOutput) : Prop :=
    BabyBear.isU32 row.imm ∧
    BabyBear.isU32 row.rs1_val ∧
    BabyBear.isU32 row.prev_read_data ∧
    BabyBear.isU32 row.read_data ∧
    (row.needs_write = 1 → BabyBear.isU32 row.prev_write_data) ∧
    (row.needs_write = 1 → BabyBear.isU32 row.write_data) ∧
    lbu_output.nextPC = row.next_pc.toNat ∧
    row.read_address_space = row.memory_address_space ∧
    row.write_address_space = 1 ∧
    row.read_ptr.val = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat - row.shift.val∧
    row.write_ptr = row.rd ∧
    row.prev_read_data = row.read_data ∧
    BitVec.signExtend 32 (BitVec.setWidth 12 (BabyBear.toBV32 row.imm)) = BabyBear.toBV32 row.imm ∧
    BabyBear.toBV32 row.imm = BitVec.signExtend 32 (BitVec.ofNat 16 row.imm_lower_half) ∧
    row.imm_sign = (BabyBear.toBV32 row.imm).msb.toNat ∧
    match lbu_output.rd with
      | .none =>
        row.rd = 0 ∧
        row.needs_write = 0
      | .some (rd, rd_val) =>
        BabyBear.toBV32 row.write_data = rd_val ∧
        rd.1.toNat * 4 = row.rd.toNat ∧
        row.needs_write = 1

  lemma lbu_spec_of_get_instruction_fields_part_1 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
  :
    (air.adapter.imm row 0).val % 256 < 256
  := by
    omega

  lemma lbu_spec_of_get_instruction_fields_part_2 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 529)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.imm row 0).val / 256 < 256
  := by
    have := LoadBU.imm_range_of_opcode_529 air row h_opcode h_is_valid h_bus_wellformedness
    omega

  lemma lbu_spec_of_get_instruction_fields_part_3 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
  :
    (air.adapter.imm_extended_limb row 0).val % 256 < 256
  := by
    omega

  lemma lbu_spec_of_get_instruction_fields_part_4 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
  :
    (air.adapter.imm_extended_limb row 0).val / 256 < 256
  := by
    have := LoadBU.imm_extend_range_of_opcode_529 air row h_row h_constraints h_is_valid
    omega

  lemma lbu_spec_of_get_instruction_fields_part_5 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_0 row 0).val < 256
  := by
    have := LoadBU.rs1_data_0_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lbu_spec_of_get_instruction_fields_part_6 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_1 row 0).val < 256
  := by
    have := LoadBU.rs1_data_1_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lbu_spec_of_get_instruction_fields_part_7 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_2 row 0).val < 256
  := by
    have := LoadBU.rs1_data_2_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lbu_spec_of_get_instruction_fields_part_8 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_3 row 0).val < 256
  := by
    have := LoadBU.rs1_data_3_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lbu_spec_of_get_instruction_fields_part_9 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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

  lemma lbu_spec_of_get_instruction_fields_part_10 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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

  lemma lbu_spec_of_get_instruction_fields_part_11 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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

  lemma lbu_spec_of_get_instruction_fields_part_12 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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

  lemma lbu_spec_of_get_instruction_fields_part_13 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
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

  lemma lbu_spec_of_get_instruction_fields_part_14 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 529)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
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
    have h_0 := LoadBU.write_data_0_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
    have h_1 := LoadBU.write_data_1_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
    have h_2 := LoadBU.write_data_2_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
    have h_3 := LoadBU.write_data_3_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
    rewrite [h_0, h_1, h_2, h_3]
    split_ands <;> simp; split_ifs <;> grind

  lemma lbu_spec_of_get_instruction_fields_part_15 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
  :
    BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32 =
    BitVec.ofNat 32 (air.to_pc row 0).val
  := by
    simp [
      Valid_VmAirWrapper_loadstore.to_pc
    ]
    have h_execution := h_bus_axioms.1
    simp [
      VmAirWrapper_loadstore_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_execution
    rewrite [Fin.val_add, Nat.mod_eq_of_lt, BitVec.ofNat_add]
    . simp
    . omega

  set_option maxHeartbeats 0 in
  lemma lbu_spec_of_get_instruction_fields_part_16 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 529)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
    (h5 : (air.adapter.rs1_data_0 row 0).val % 256 < 2 ^ 8)
    (h6 : (air.adapter.rs1_data_1 row 0).val % 256 < 2 ^ 8)
    (h7 : (air.adapter.rs1_data_2 row 0).val % 256 < 2 ^ 8)
    (h8 : (air.adapter.rs1_data_3 row 0).val % 256 < 2 ^ 8)
  :
    ↑(air.read_ptr row 0) =
    (
      U32.toNat #v[
        { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
        { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
      ] +
      U32.toNat #v[
        { toFin := ⟨↑(air.adapter.rs1_data_0 row 0) % 256, h5⟩ },
        { toFin := ⟨↑(air.adapter.rs1_data_1 row 0) % 256, h6⟩ },
        { toFin := ⟨↑(air.adapter.rs1_data_2 row 0) % 256, h7⟩ },
        { toFin := ⟨↑(air.adapter.rs1_data_3 row 0) % 256, h8⟩ }
      ]
    ) % 4294967296 - (air.shift_amount row 0).val
  := by
    simp only [U32.toNat]
    rewrite [
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin,
      BitVec.toNat_ofFin
    ]
    simp
    have := LoadBU.read_ptr_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
    rewrite [this]; clear this
    have h_mem_ptr := LoadBU.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    have h_imm_sign_extend := LoadBU.imm_sign_extend_of_opcode_529 air row h_opcode h_is_valid h_bus_wellformedness
    rewrite [h_imm_sign_extend] at h_mem_ptr
    rewrite [BitVec.toNat_eq] at h_mem_ptr
    simp [-BitVec.toNat_add] at h_mem_ptr
    rewrite [BitVec.toNat_add] at h_mem_ptr
    simp at h_mem_ptr
    rewrite [Nat.mod_eq_of_lt (by omega)] at h_mem_ptr
    rw [Fin.sub_val_of_le
        (by have h_ptr_range := LoadBU.mem_ptr_range_of_opcode_529 air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
            simp [LoadBU.shift_amount_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid] at h_ptr_range ⊢
            clear *- h_ptr_range
            split_ifs <;>
            simp_all <;>
            omega)]
    rewrite [h_mem_ptr]; clear h_mem_ptr
    congr
    rewrite [BitVec.toNat_ofFin]
    simp
    have (x y: ℕ) :
      (BitVec.setWidth 32 (BitVec.ofNat 16 x)) <<< 16 +
      (BitVec.setWidth 32 (BitVec.ofNat 16 y)) =
      (BitVec.ofNat 16 x) ++ (BitVec.ofNat 16 y)
    := by bv_decide
    rewrite [←this]; clear this
    rewrite [BitVec.toNat_add]
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

  lemma lbu_spec_of_get_instruction_fields_part_17 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 529)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    BitVec.signExtend 32
    (BitVec.setWidth 12
      (U32.toBV
        #v[
          { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
          { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
        ]
      )
    ) =
    U32.toBV
      #v[
        { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
        { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
        { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
      ]
  := by
    have := LoadBU.imm_sign_extend_of_opcode_529 air row h_opcode h_is_valid h_bus_wellformedness
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) :
      BitVec.setWidth 12 (bv1 ++ bv2 ++ bv3 ++ bv4) =
      BitVec.setWidth 12 (bv3 ++ bv4)
    := by bv_decide
    rewrite [this]; clear this
    -- combine the two halves of imm into BitVec.ofNat 16 imm
    have h_imm_range := LoadBU.imm_range_of_opcode_529 air row h_opcode h_is_valid h_bus_wellformedness
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
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨
        instruction,
        multiplciity,
        data,
        ⟨h_instruction, _, _, h_data_opcode, _, _, h_data_imm, _⟩
      ⟩ := h_transpile
      rewrite [←h_data_imm]
      have := Transpiler.transpiler_opcode_529 h_instruction
      simp [h_data_opcode, h_opcode] at this
      have h_alignment := Transpiler.pc_aligned_of_some h_instruction
      have h_bound := Transpiler.pc_bound_of_some h_instruction
      obtain
        ⟨_, imm, rs1, rd, h_instruction_load, _⟩ |
        ⟨_, imm, rs1, h_instruction_load⟩
      := this
      all_goals {
        rewrite [h_instruction_load] at h_instruction
        unfold Transpiler.transpile_op at h_instruction
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
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
    . have h_imm_extended_range := LoadBU.imm_extend_range_of_opcode_529 air row h_row h_constraints h_is_valid
      have h_split_imm_extended := split_bitvec_16_to_8s h_imm_extended_range
      simp [BitVec.ofNat, Nat.cast] at h_split_imm_extended
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm_extended
      dsimp at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt]
      rewrite [←h_split_imm_extended]
      have := LoadBU.imm_sign_extend_of_opcode_529 air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [this]
      simp [BitVec.ofNat, Nat.cast]
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
      dsimp
      simp (disch := omega) [Nat.mod_eq_of_lt]

  lemma lbu_spec_of_get_instruction_fields_part_18 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 529)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    U32.toBV
    #v[
      { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
      { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
      { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
      { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
    ] =
    BitVec.signExtend 32 (BitVec.ofNat 16 ↑(air.adapter.imm row 0))
  := by
    simp [U32.toBV]
    have := LoadBU.imm_sign_extend_of_opcode_529 air row h_opcode h_is_valid h_bus_wellformedness
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
        have := LoadBU.imm_extend_range_of_opcode_529 air row h_row h_constraints h_is_valid
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
        have := LoadBU.imm_range_of_opcode_529 air row h_opcode h_is_valid h_bus_wellformedness
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
      }

  lemma lbu_spec_of_get_instruction_fields_part_19 [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 529)
    (h_constraints : VmAirWrapper_loadstore.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
    (h1 : (air.adapter.imm row 0).val % 256 < 2 ^ 8)
    (h2 : (air.adapter.imm row 0).val / 256 % 256 < 2 ^ 8)
    (h3 : (air.adapter.imm_extended_limb row 0).val % 256 < 2 ^ 8)
    (h4 : (air.adapter.imm_extended_limb row 0).val / 256 % 256 < 2 ^ 8)
  :
    air.adapter.imm_sign row 0 =
    ↑(
      U32.toBV
        #v[
          { toFin := ⟨↑(air.adapter.imm row 0) % 256, h1⟩ },
          { toFin := ⟨↑(air.adapter.imm row 0) / 256 % 256, h2⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) % 256, h3⟩ },
          { toFin := ⟨↑(air.adapter.imm_extended_limb row 0) / 256 % 256, h4⟩ }
        ]
    ).msb.toNat
  := by
    have := LoadBU.imm_sign_of_opcode_529 air row h_bus_wellformedness h_is_valid h_opcode
    rewrite [this]; clear this
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) : (bv1 ++ bv2 ++ bv3 ++ bv4).msb = bv1.msb := by bv_decide
    simp [this]
    have := LoadBU.imm_extend_range_of_opcode_529 air row h_row h_constraints h_is_valid
    have :
      (air.adapter.imm_extended_limb row 0).val / 256 % 256 =
      (air.adapter.imm_extended_limb row 0).val / 256
    := by
      omega
    simp [this]
    have h_sign_extend := LoadBU.imm_sign_extend_of_opcode_529 air row h_opcode h_is_valid h_bus_wellformedness
    have (bv1 bv2: BitVec 32): bv1 = bv2 → bv1.msb = bv2.msb := by intro h; grind
    apply this at h_sign_extend
    have (bv: BitVec 16) : (bv.signExtend 32).msb = bv.msb := by bv_decide
    rewrite [this] at h_sign_extend
    rewrite [h_sign_extend]
    have (bv1 bv2: BitVec 16): (bv1 ++ bv2).msb = bv1.msb := by bv_decide
    rewrite [this]
    have (a b : Bool) : (a.toNat: FBB) = (b.toNat: FBB) ↔ a = b := by cases a <;> cases b <;> decide
    rewrite [this]
    simp [BitVec.msb, BitVec.getMsbD, Nat.testBit]
    rewrite [Nat.mod_eq_of_lt (by omega)]
    unfold getElem BitVec.instGetElemNatBoolLt
    simp only [BitVec.getLsb, Nat.testBit]
    simp
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow,
    ]
    simp
    rewrite [Nat.div_div_eq_div_mul]
    simp

  set_option maxHeartbeats 0 in
  lemma lbu_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 529 →
        LbuOutput_matches_LoadStore_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_LOADBU_lbu_pure
            (LbuInput_of_LoadStore_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [
      LbuOutput_matches_LoadStore_instruction_fields,
      get_instruction_fields_row,
      -BitVec.toNat_add
    ]
    rewrite [BitVec.toNat_add]
    simp

    rewrite [allHold_allRows] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    specialize h_bus_axioms row h_row
    specialize h_bus_wellformedness row h_row
    simp [LbuInput_of_LoadStore_instruction_fields, PureSpec.execute_LOADBU_lbu_pure]

    split_ands
    . exact lbu_spec_of_get_instruction_fields_part_1 air row
    . exact lbu_spec_of_get_instruction_fields_part_2 air row h_is_valid h_opcode h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_3 air row
    . exact lbu_spec_of_get_instruction_fields_part_4 air row h_row h_is_valid h_constraints
    . exact lbu_spec_of_get_instruction_fields_part_5 air row h_is_valid h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_6 air row h_is_valid h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_7 air row h_is_valid h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_8 air row h_is_valid h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_9 air row h_is_valid h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_10 air row h_is_valid h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_11 air row h_is_valid h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_12 air row h_is_valid h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_13 air row h_is_valid h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_14 air row h_row h_is_valid h_opcode h_constraints h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields_part_15 air row h_is_valid h_bus_axioms
    . exact LoadBU.read_as_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
    . exact LoadBU.write_as_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
    . apply lbu_spec_of_get_instruction_fields_part_16 air row h_row h_is_valid h_opcode h_constraints h_bus_wellformedness
    . exact LoadBU.write_ptr_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
    . apply lbu_spec_of_get_instruction_fields_part_17 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . apply lbu_spec_of_get_instruction_fields_part_18 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . apply lbu_spec_of_get_instruction_fields_part_19 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . have h_transpile := h_bus_wellformedness.2.2.2
      simp [
        VmAirWrapper_loadstore_constraint_and_interaction_simplification,
        h_is_valid,
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨instruction, multiplicity, data, h_instruction⟩ := h_transpile
      have h_aligned := Transpiler.pc_aligned_of_some h_instruction.1
      have h_bound := Transpiler.pc_bound_of_some h_instruction.1
      have h_rd := Transpiler.transpiler_opcode_529 h_instruction.1
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
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
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
            have := LoadBU.write_data_3_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := LoadBU.write_data_2_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := LoadBU.write_data_1_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
            simp [this]
            have := LoadBU.write_data_0_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid
            simp [this, LoadBU.shift_amount_of_opcode_529 air row h_opcode h_row h_constraints h_is_valid]
            simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_bus_wellformedness
            clear *-
            split_ifs
            all_goals {
              symm
              simp [BitVec.extend, ← BitVec.toNat_inj]
              split_ifs <;> (try (exfalso; tauto)) <;>
              (repeat rw [BitVec.toNat_append]) <;>
              simp <;>
              omega
            }
          . grind
          . clear *-h_rd
            fin_cases rd
            . simp_all
            all_goals decide
        . clear *-h_rd
          obtain ⟨⟨rd: Fin 32⟩⟩ := rd
          simp
          convert h_rd
          omega
      . rewrite [h_instruction_load] at h_instruction
        unfold Transpiler.transpile_op at h_instruction
        dsimp at h_instruction
        rewrite [if_pos (by constructor <;> assumption)] at h_instruction
        simp [-Vector.mk_eq] at h_instruction
        rewrite [←h_instruction.2.2.2.2.1, ←h_instruction.1.2]
        simp [Transpiler.ind, wrap_to_regidx, regidx_to_fin]
        rewrite [←h_instruction.2.2.2.2.2.2.2.2.2.1, ←h_instruction.1.2]
        simp
        decide

  /-
     ***
     *** Main specification
     ***
  -/

  def LoadStore_instruction_fields.spec (row : LoadStore_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode ∈ Finset.Icc 528 533 ∧
      (row.opcode = 528 →
        LwOutput_matches_LoadStore_instruction_fields
          row
          (PureSpec.execute_LOAD_lw_pure (LwInput_of_LoadStore_instruction_fields row))
      ) ∧
      (row.opcode = 529 →
        LbuOutput_matches_LoadStore_instruction_fields
          row
          (PureSpec.execute_LOADBU_lbu_pure (LbuInput_of_LoadStore_instruction_fields row))
      ) ∧
      (row.opcode = 530 →
        LhuOutput_matches_LoadStore_instruction_fields
          row
          (PureSpec.execute_LOADHU_lhu_pure (LhuInput_of_LoadStore_instruction_fields row))
      ) ∧
      (row.opcode = 531 →
        SwOutput_matches_LoadStore_instruction_fields
          row
          (PureSpec.execute_STORE_sw_pure (SwInput_of_LoadStore_instruction_fields row))
      ) ∧
      (row.opcode = 532 →
        ShOutput_matches_LoadStore_instruction_fields
          row
          (PureSpec.execute_STOREH_sh_pure (ShInput_of_LoadStore_instruction_fields row))
      ) ∧
      (row.opcode = 533 →
        SbOutput_matches_LoadStore_instruction_fields
          row
          (PureSpec.execute_STOREB_sb_pure (SbInput_of_LoadStore_instruction_fields row))
      )
    )

  lemma spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
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

    split_ands
    . exact get_instruction_fields_row_opcode_range air row (by omega) h_constraints h_is_valid
    . exact lw_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
    . exact lbu_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
    . exact lhu_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
    . exact sw_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
    . exact sh_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
    . exact sb_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness

  theorem loadstore_spec [Field ExtF]
    (air : Valid_VmAirWrapper_loadstore FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_loadstore.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List LoadStore_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall LoadStore_instruction_fields.spec
  := by
    use get_instruction_fields air
    simp only [
      bus_from_instruction_fields_eq_air_buses air h_constraints,
      spec_of_get_instruction_fields air h_constraints h_bus_axioms h_bus_wellformedness
    ]
    trivial

end Equivalence.LoadStore
