import OpenvmFv.RV32D.lh
import OpenvmFv.RV32D.lb

import OpenvmFv.Spec.LoadH
import OpenvmFv.Spec.LoadB

namespace Equivalence.LoadSignExtend

  private lemma concat_ofNat8_div_mod (a : ℕ) :
    256#16 * BitVec.setWidth 16 (BitVec.ofNat 8 (a / 256)) +
    BitVec.ofNat 8 (a % 256) =
    BitVec.ofNat 8 (a / 256) ++ BitVec.ofNat 8 (a % 256)
  := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_append]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.shiftLeft_eq, BitVec.toNat_setWidth]
    omega

  private lemma concat8_eq_mul_add (bv1 bv2 : BitVec 8) :
    256#16 * BitVec.setWidth 16 bv1 + BitVec.setWidth 16 bv2 =
    bv1 ++ bv2
  := by
    apply BitVec.eq_of_toNat_eq
    rw [
      BitVec.toNat_add,
      BitVec.toNat_mul,
      BitVec.toNat_setWidth,
      BitVec.toNat_setWidth,
      BitVec.toNat_append
    ]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.shiftLeft_eq]
    omega

  private lemma concat16_eq_shift_add (x y : ℕ) :
    (BitVec.setWidth 32 (BitVec.ofNat 16 x)) <<< 16 +
    (BitVec.setWidth 32 (BitVec.ofNat 16 y)) =
    (BitVec.ofNat 16 x) ++ (BitVec.ofNat 16 y)
  := by
    apply BitVec.eq_of_toNat_eq
    rw [
      BitVec.toNat_add,
      BitVec.toNat_shiftLeft,
      BitVec.toNat_setWidth,
      BitVec.toNat_setWidth,
      BitVec.toNat_append
    ]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.shiftLeft_eq]
    omega

  private lemma setWidth12_append_four_eq_tail (bv1 bv2 bv3 bv4 : BitVec 8) :
    BitVec.setWidth 12 (bv1 ++ bv2 ++ bv3 ++ bv4) =
    BitVec.setWidth 12 (bv3 ++ bv4)
  := by
    ext i hi
    simp only [BitVec.getElem_setWidth]
    repeat rw [BitVec.getLsbD_append]
    by_cases h : i < 8
    · simp [h]
    · simp [h]
      omega

  private lemma append_zero_20_12 (imm : BitVec 12) :
    0#20 ++ imm = 0#16 ++ (0#4 ++ imm)
  := by
    ext i hi
    rw [← BitVec.getLsbD_eq_getElem hi]
    rw [← BitVec.getLsbD_eq_getElem hi]
    repeat rw [BitVec.getLsbD_append]
    by_cases h12 : i < 12
    · simp [h12]
      omega
    · by_cases h16 : i < 16
      · simp [h12, h16]
      · simp [h12, h16]

  private lemma append_allOnes_20_12 (imm : BitVec 12) :
    BitVec.allOnes 20 ++ imm =
    BitVec.allOnes 16 ++ (BitVec.allOnes 4 ++ imm)
  := by
    ext i hi
    rw [← BitVec.getLsbD_eq_getElem hi]
    rw [← BitVec.getLsbD_eq_getElem hi]
    repeat rw [BitVec.getLsbD_append]
    by_cases h12 : i < 12
    · simp [h12]
      omega
    · by_cases h16 : i < 16
      · simp [h12, h16]
        rw [BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
        rw [show 1048575 = 2 ^ 20 - 1 by norm_num]
        rw [show 15 = 2 ^ 4 - 1 by norm_num]
        rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
        simp
        omega
      · simp [h12, h16]
        rw [BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
        rw [show 1048575 = 2 ^ 20 - 1 by norm_num]
        rw [show 65535 = 2 ^ 16 - 1 by norm_num]
        rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
        simp
        omega

  private lemma signExtend32_signExtend16_eq (imm : BitVec 12) :
    BitVec.signExtend 32 imm =
    BitVec.signExtend 32 (BitVec.signExtend 16 imm)
  := by
    cases h : imm.msb
    · rw [BitVec.signExtend_eq_append_of_le (by omega : 12 ≤ 16)]
      rw [BitVec.signExtend_eq_append_of_le (by omega : 12 ≤ 32)]
      rw [BitVec.signExtend_eq_append_of_le (by omega : 16 ≤ 32)]
      simp only [h, Bool.false_eq_true, ↓reduceIte, BitVec.cast_eq]
      rw [BitVec.msb_append]
      simp only [h]
      exact append_zero_20_12 imm
    · rw [BitVec.signExtend_eq_append_of_le (by omega : 12 ≤ 16)]
      rw [BitVec.signExtend_eq_append_of_le (by omega : 12 ≤ 32)]
      rw [BitVec.signExtend_eq_append_of_le (by omega : 16 ≤ 32)]
      simp only [h, ↓reduceIte, BitVec.cast_eq]
      rw [BitVec.msb_append]
      simp only [BitVec.msb_allOnes (by omega : 0 < 4)]
      exact append_allOnes_20_12 imm

  private lemma signExtend32_setWidth12_signExtend16_eq (imm : BitVec 12) :
    BitVec.signExtend 32 (BitVec.setWidth 12 (BitVec.signExtend 16 imm)) =
    BitVec.signExtend 32 (BitVec.signExtend 16 imm)
  := by
    have h_setWidth : BitVec.setWidth 12 (BitVec.signExtend 16 imm) = imm := by
      rw [BitVec.signExtend_eq_append_of_le (by omega : 12 ≤ 16)]
      rw [BitVec.setWidth_cast]
      rw [BitVec.setWidth_append_eq_right]
    rw [h_setWidth]
    exact signExtend32_signExtend16_eq imm

  @[ext]
  structure LoadSignExtend_instruction_fields where
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

    range_checked_vals : Vector FBB 9

  lemma LoadSignExtend_instruction_fields_eq (a b : LoadSignExtend_instruction_fields)
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


  def LoadSignExtend_instruction_fields.execution (row : LoadSignExtend_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def LoadSignExtend_instruction_fields.memory (row : LoadSignExtend_instruction_fields) : List (FBB × List FBB) := [
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

  def LoadSignExtend_instruction_fields.range_checks (row : LoadSignExtend_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 7]),
    (row.is_valid, [row.range_checked_vals[1], 17]),
    (row.is_valid, [row.range_checked_vals[2], 12]),
    (row.is_valid, [row.range_checked_vals[3], 14]),
    (row.is_valid, [row.range_checked_vals[4], 13]),
    (row.is_valid, [row.range_checked_vals[5], 17]),
    (row.is_valid, [row.range_checked_vals[6], 12]),
    (row.needs_write, [row.range_checked_vals[7], 17]),
    (row.needs_write, [row.range_checked_vals[8], 12])
  ]

  def LoadSignExtend_instruction_fields.read_instruction (row : LoadSignExtend_instruction_fields) : List (FBB × List FBB) := [
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

  def bus_from_instruction_fields (rows : List LoadSignExtend_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then
        rows.flatMap LoadSignExtend_instruction_fields.execution
      else if index = MemoryBus then
        rows.flatMap LoadSignExtend_instruction_fields.memory
      else if index = ProgramBus then
        rows.flatMap LoadSignExtend_instruction_fields.read_instruction
      else if index = RangeCheckerBus then
        rows.flatMap LoadSignExtend_instruction_fields.range_checks
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_load_sign_extend.constraints.allHold air row.1 (by grind)

  def get_instruction_fields_row [Field ExtF] (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF) (row : ℕ) : LoadSignExtend_instruction_fields := {
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
      air.core.read_data row 0 0,
      air.core.read_data row 0 1,
      air.core.read_data row 0 2,
      air.core.read_data row 0 3
    ]
    read_data := #v[
      air.core.read_data row 0 0,
      air.core.read_data row 0 1,
      air.core.read_data row 0 2,
      air.core.read_data row 0 3
    ]
    prev_write_data := #v[
      air.core.prev_data_0 row 0,
      air.core.prev_data_1 row 0,
      air.core.prev_data_2 row 0,
      air.core.prev_data_3 row 0
    ]
    write_data := #v[
      air.core.write_data row 0 0,
      air.core.write_data row 0 1,
      air.core.write_data row 0 2,
      air.core.write_data row 0 3
    ]
    shift := air.shift_amount row 0,
    range_checked_vals := #v[
      air.core.most_sig_limb row 0 - air.core.data_most_sig_bit row 0 * 128,
      air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0,
      air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0,
      (air.adapter.mem_ptr_limbs_0 row 0 - air.core.load_shift_amount row 0) * 1509949441,
      air.adapter.mem_ptr_limbs_1 row 0,
      air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_0 row 0,
      air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_1 row 0,
      air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_0 row 0,
      air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_1 row 0
    ]
    : LoadSignExtend_instruction_fields
  }

  def get_instruction_fields [Field ExtF] (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF) : List LoadSignExtend_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma execution_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
  :
    List.flatMap (VmAirWrapper_load_sign_extend.constraints.executionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap LoadSignExtend_instruction_fields.execution (get_instruction_fields air)
  := by
    unfold LoadSignExtend_instruction_fields.execution
    unfold VmAirWrapper_load_sign_extend.constraints.executionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma memory_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
  :
    List.flatMap (VmAirWrapper_load_sign_extend.constraints.memoryBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap LoadSignExtend_instruction_fields.memory (get_instruction_fields air)
  := by
    unfold LoadSignExtend_instruction_fields.memory
    unfold VmAirWrapper_load_sign_extend.constraints.memoryBus_row
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      h_neg_one
    ]

  lemma range_checks_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
  :
    List.flatMap (VmAirWrapper_load_sign_extend.constraints.rangeCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap LoadSignExtend_instruction_fields.range_checks (get_instruction_fields air)
  := by
    unfold LoadSignExtend_instruction_fields.range_checks
    unfold VmAirWrapper_load_sign_extend.constraints.rangeCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma read_instruction_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
  :
    List.flatMap (VmAirWrapper_load_sign_extend.constraints.programBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap LoadSignExtend_instruction_fields.read_instruction (get_instruction_fields air)
  := by
    unfold LoadSignExtend_instruction_fields.read_instruction
    unfold VmAirWrapper_load_sign_extend.constraints.programBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma bus_from_instruction_fields_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (h_constraints : allHold_allRows air)
  :
    air.buses = bus_from_instruction_fields (get_instruction_fields air)
  := by
    have h_interactions := VmAirWrapper_load_sign_extend.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_load_sign_extend.constraints.constrain_interactions at h_interactions
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
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
  :
    (get_instruction_fields_row air row).opcode ∈ Finset.Icc 534 535
  := by
    simp [
      get_instruction_fields_row,
      Valid_LoadSignExtendCoreAir_4.expected_opcode,
    ]
    rewrite [
      allHold_allRows
    ] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    rewrite [
      VmAirWrapper_load_sign_extend.constraints.allHold_simplified_of_allHold
    ] at h_constraints
    simp [VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification] at h_constraints
    simp [Valid_LoadSignExtendCoreAir_4.is_valid] at h_is_valid
    grind

  lemma transpile_of_bus_wellformedness [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
    unfold VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2
    simp [
      VmAirWrapper_load_sign_extend.constraints.propertiesToAssume,
      Interaction.ProgramBusEntry.operand_properties,
      VmAirWrapper_load_sign_extend.constraints._programBus_row,
      VmAirWrapper_load_sign_extend.constraints.programBus_row,
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
    := by exact concat_ofNat8_div_mod a
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
     *** LH
     ***
  -/

  def LhInput_of_LoadSignExtend_instruction_fields (row : LoadSignExtend_instruction_fields) : PureSpec.LhInput := {
    r1 := BitVec.ofFin (Transpiler.wrap_to_regidx row.rs1)
    imm := BabyBear.toBV32 row.imm
    rd := BitVec.ofFin (Transpiler.wrap_to_regidx row.rd)
    r1_val := BabyBear.toBV32 row.rs1_val
    PC := row.pc.toNat
    data0 := if (row.shift = 0) then row.prev_read_data[0] else row.prev_read_data[2]
    data1 := if (row.shift = 0) then row.prev_read_data[1] else row.prev_read_data[3]
    : PureSpec.LhInput
  }

  def LhOutput_matches_LoadSignExtend_instruction_fields (row : LoadSignExtend_instruction_fields) (lh_output : PureSpec.LhOutput) : Prop :=
    BabyBear.isU32 row.imm ∧
    BabyBear.isU32 row.rs1_val ∧
    BabyBear.isU32 row.prev_read_data ∧
    BabyBear.isU32 row.read_data ∧
    (row.needs_write = 1 → BabyBear.isU32 row.prev_write_data) ∧
    (row.needs_write = 1 → BabyBear.isU32 row.write_data) ∧
    lh_output.nextPC = row.next_pc.toNat ∧
    row.read_address_space = row.memory_address_space ∧
    row.write_address_space = 1 ∧
    row.read_ptr.val = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat - row.shift.val∧
    row.write_ptr = row.rd ∧
    row.prev_read_data = row.read_data ∧
    BitVec.signExtend 32 (BitVec.setWidth 12 (BabyBear.toBV32 row.imm)) = BabyBear.toBV32 row.imm ∧
    BabyBear.toBV32 row.imm = BitVec.signExtend 32 (BitVec.ofNat 16 row.imm_lower_half) ∧
    row.imm_sign = (BabyBear.toBV32 row.imm).msb.toNat ∧
    match lh_output.rd with
      | .none =>
        row.rd = 0 ∧
        row.needs_write = 0
      | .some (rd, rd_val) =>
        BabyBear.toBV32 row.write_data = rd_val ∧
        rd.1.toNat * 4 = row.rd.toNat ∧
        row.needs_write = 1

  lemma lh_spec_of_get_instruction_fields_part_1 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
  :
    (air.adapter.imm row 0).val % 256 < 256
  := by
    omega

  lemma lh_spec_of_get_instruction_fields_part_2 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 535)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.imm row 0).val / 256 < 256
  := by
    have := LoadH.imm_range air row h_opcode h_is_valid h_bus_wellformedness
    omega

  lemma lh_spec_of_get_instruction_fields_part_3 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
  :
    (air.adapter.imm_extended_limb row 0).val % 256 < 256
  := by
    omega

  lemma lh_spec_of_get_instruction_fields_part_4 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
  :
    (air.adapter.imm_extended_limb row 0).val / 256 < 256
  := by
    have := LoadH.imm_extend_range air row h_row h_constraints h_is_valid
    omega

  lemma lh_spec_of_get_instruction_fields_part_5 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_0 row 0).val < 256
  := by
    have := LoadH.rs1_data_0_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lh_spec_of_get_instruction_fields_part_6 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_1 row 0).val < 256
  := by
    have := LoadH.rs1_data_1_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lh_spec_of_get_instruction_fields_part_7 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_2 row 0).val < 256
  := by
    have := LoadH.rs1_data_2_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lh_spec_of_get_instruction_fields_part_8 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_3 row 0).val < 256
  := by
    have := LoadH.rs1_data_3_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lh_spec_of_get_instruction_fields_part_9 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data row 0 0).val < 256
  := by
    have h_memory := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920 : FBB) = (-1 : FBB) by decide
    ] at h_memory
    exact h_memory.2.1.2.2.1

  lemma lh_spec_of_get_instruction_fields_part_10 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data row 0 1).val < 256
  := by
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.1

  lemma lh_spec_of_get_instruction_fields_part_11 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data row 0 2).val < 256
  := by
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.2.1

  lemma lh_spec_of_get_instruction_fields_part_12 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data row 0 3).val < 256
  := by
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.2.2

  lemma lh_spec_of_get_instruction_fields_part_13 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
      VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920 : FBB) = (-1 : FBB) by decide,
      h_needs_write
    ] at h_memory
    split_ands
    . exact h_memory.2.2.2.2.1
    . exact h_memory.2.2.2.2.2.1
    . exact h_memory.2.2.2.2.2.2.1
    . exact h_memory.2.2.2.2.2.2.2

  lemma lh_spec_of_get_instruction_fields_part_14 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 535)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.adapter.needs_write row 0 = 1 →
    (air.core.write_data row 0 0).val < 256 ∧
    (air.core.write_data row 0 1).val < 256 ∧
    (air.core.write_data row 0 2).val < 256 ∧
    (air.core.write_data row 0 3).val < 256
  := by
    intro h_needs_write
    have h_memory := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920 : FBB) = (-1 : FBB) by decide,
      h_needs_write
    ] at h_memory
    obtain ⟨ w0, w1, w2, w3 ⟩ := LoadH.write_data_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    rewrite [ w0, w1, w2, w3 ]
    obtain ⟨ sd0, sd1 ⟩ := LoadH.shifted_read_data air row h_opcode h_row h_constraints h_is_valid
    split_ands
    . rewrite [ sd0 ]; split_ifs <;> grind
    . rewrite [ sd1 ]; split_ifs <;> grind
    . by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.shifted_read_data_1 row 0)).msb <;> simp [hmsb]
    . by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.shifted_read_data_1 row 0)).msb <;> simp [hmsb]


  lemma lh_spec_of_get_instruction_fields_part_15 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
  :
    BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32 =
    BitVec.ofNat 32 (air.to_pc row 0).val
  := by
    simp [
      Valid_VmAirWrapper_load_sign_extend.to_pc
    ]
    have h_execution := h_bus_axioms.1
    simp [
      VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_execution
    rewrite [Fin.val_add, Nat.mod_eq_of_lt, BitVec.ofNat_add]
    . simp
    . omega

  set_option maxHeartbeats 0 in
  lemma lh_spec_of_get_instruction_fields_part_16 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 535)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
    have := LoadH.read_ptr_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    rewrite [this]; clear this
    have h_mem_ptr := LoadH.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    have h_imm_sign_extend := LoadH.imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness
    rewrite [h_imm_sign_extend] at h_mem_ptr
    rewrite [BitVec.toNat_eq] at h_mem_ptr
    simp [-BitVec.toNat_add] at h_mem_ptr
    rewrite [BitVec.toNat_add] at h_mem_ptr
    simp at h_mem_ptr
    rewrite [Nat.mod_eq_of_lt (by omega)] at h_mem_ptr
    rw [Fin.sub_val_of_le
        (by have h_ptr_range := LoadH.mem_ptr_range air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
            obtain ⟨ sh, lsh, rsh ⟩ := LoadH.shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
            simp [sh] at h_ptr_range ⊢
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
    := by exact concat16_eq_shift_add x y
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

  set_option maxRecDepth 2_000_000 in
  lemma lh_spec_of_get_instruction_fields_part_17 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 535)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
    have := LoadH.imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) :
      BitVec.setWidth 12 (bv1 ++ bv2 ++ bv3 ++ bv4) =
      BitVec.setWidth 12 (bv3 ++ bv4)
    := by exact setWidth12_append_four_eq_tail bv1 bv2 bv3 bv4
    rewrite [this]; clear this
    -- combine the two halves of imm into BitVec.ofNat 16 imm
    have h_imm_range := LoadH.imm_range air row h_opcode h_is_valid h_bus_wellformedness
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
        VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
        h_is_valid,
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨
        instruction,
        data,
        ⟨h_instruction, _, h_data_opcode, _, _, h_data_imm, _⟩
      ⟩ := h_transpile
      rewrite [←h_data_imm]
      have := Transpiler.transpiler_opcode_535 h_instruction
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
        simp (disch := omega) [←h_instruction, Transpiler.utof, Transpiler.sign_extend_16, Nat.mod_eq_of_lt]
        exact signExtend32_setWidth12_signExtend16_eq imm
      }
    convert this using 1
    . simp [BitVec.ofNat, Nat.cast]
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
      dsimp
      simp (disch := omega) [Nat.mod_eq_of_lt]
    . have h_imm_extended_range := LoadH.imm_extend_range air row h_row h_constraints h_is_valid
      have h_split_imm_extended := split_bitvec_16_to_8s h_imm_extended_range
      simp [BitVec.ofNat, Nat.cast] at h_split_imm_extended
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm_extended
      dsimp at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt]
      rewrite [←h_split_imm_extended]
      have := LoadH.imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [this]
      simp [BitVec.ofNat, Nat.cast]
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
      dsimp
      simp (disch := omega) [Nat.mod_eq_of_lt]

  lemma lh_spec_of_get_instruction_fields_part_18 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 535)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
    have := LoadH.imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness
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
        have := LoadH.imm_extend_range air row h_row h_constraints h_is_valid
        omega
      simp [Nat.mod_eq_of_lt this]
      have (bv1 bv2: BitVec 8) :
        256#16 * BitVec.setWidth 16 bv1 + BitVec.setWidth 16 bv2 =
        bv1 ++ bv2
      := by exact concat8_eq_mul_add bv1 bv2
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
        have := LoadH.imm_range air row h_opcode h_is_valid h_bus_wellformedness
        omega
      simp [Nat.mod_eq_of_lt this]
      have (bv1 bv2: BitVec 8) :
        256#16 * BitVec.setWidth 16 bv1 + BitVec.setWidth 16 bv2 =
        bv1 ++ bv2
      := by exact concat8_eq_mul_add bv1 bv2
      rewrite [←this]
      congr <;> {
        unfold BitVec.setWidth BitVec.setWidth' BitVec.toNat
        simp [BitVec.ofNat]
        refine BitVec.eq_of_toNat_eq ?_
        simp
        omega
      }

  lemma lh_spec_of_get_instruction_fields_part_19 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 535)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
    have := LoadH.imm_sign air row h_bus_wellformedness h_is_valid h_opcode
    rewrite [this]; clear this
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) : (bv1 ++ bv2 ++ bv3 ++ bv4).msb = bv1.msb := by
      repeat rw [BitVec.msb_append]
      simp
    simp [this]
    have := LoadH.imm_extend_range air row h_row h_constraints h_is_valid
    have :
      (air.adapter.imm_extended_limb row 0).val / 256 % 256 =
      (air.adapter.imm_extended_limb row 0).val / 256
    := by
      omega
    simp [this]
    have h_sign_extend := LoadH.imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness
    have (bv1 bv2: BitVec 32): bv1 = bv2 → bv1.msb = bv2.msb := by intro h; grind
    apply this at h_sign_extend
    have (bv: BitVec 16) : (bv.signExtend 32).msb = bv.msb := by
      simp [BitVec.msb_signExtend]
    rewrite [this] at h_sign_extend
    rewrite [h_sign_extend]
    have (bv1 bv2: BitVec 16): (bv1 ++ bv2).msb = bv1.msb := by
      rw [BitVec.msb_append]
      simp
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
  set_option maxRecDepth 2_000_000 in
  lemma lh_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 535 →
        LhOutput_matches_LoadSignExtend_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_LOADH_pure
            (LhInput_of_LoadSignExtend_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [
      LhOutput_matches_LoadSignExtend_instruction_fields,
      get_instruction_fields_row,
      -BitVec.toNat_add
    ]
    rewrite [BitVec.toNat_add]
    simp

    rewrite [allHold_allRows] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    specialize h_bus_axioms row h_row
    specialize h_bus_wellformedness row h_row
    simp [LhInput_of_LoadSignExtend_instruction_fields, PureSpec.execute_LOADH_pure]

    split_ands
    . exact lh_spec_of_get_instruction_fields_part_1 air row
    . exact lh_spec_of_get_instruction_fields_part_2 air row h_is_valid h_opcode h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_3 air row
    . exact lh_spec_of_get_instruction_fields_part_4 air row h_row h_is_valid h_constraints
    . exact lh_spec_of_get_instruction_fields_part_5 air row h_is_valid h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_6 air row h_is_valid h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_7 air row h_is_valid h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_8 air row h_is_valid h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_9 air row h_is_valid h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_10 air row h_is_valid h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_11 air row h_is_valid h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_12 air row h_is_valid h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_13 air row h_is_valid h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_14 air row h_row h_is_valid h_opcode h_constraints h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields_part_15 air row h_is_valid h_bus_axioms
    . exact LoadH.read_as air row h_is_valid
    . exact LoadH.write_as air row h_is_valid
    . apply lh_spec_of_get_instruction_fields_part_16 air row h_row h_is_valid h_opcode h_constraints h_bus_wellformedness
    . exact LoadH.write_ptr air row h_is_valid
    . apply lh_spec_of_get_instruction_fields_part_17 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . apply lh_spec_of_get_instruction_fields_part_18 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . apply lh_spec_of_get_instruction_fields_part_19 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . have h_transpile := h_bus_wellformedness.2.2.2
      simp [
        VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
        h_is_valid,
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨instruction, data, h_instruction⟩ := h_transpile
      have h_aligned := Transpiler.pc_aligned_of_some h_instruction.1
      have h_bound := Transpiler.pc_bound_of_some h_instruction.1
      have h_rd := Transpiler.transpiler_opcode_535 h_instruction.1
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
        rewrite [←h_instruction.2.2.2.1, ←h_instruction.1]
        simp [Transpiler.ind, Transpiler.wrap_to_regidx, regidx_to_fin]
        rewrite [dite_cond_eq_false]
        . simp
          rewrite [←h_instruction.2.2.2.2.2.2.2.2.1, ←h_instruction.1]
          simp
          obtain ⟨⟨rd: Fin 32⟩⟩ := rd
          split_ands
          . simp [U32.toBV]
            obtain ⟨ w0, w1, w2, w3 ⟩ := LoadH.write_data_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
            obtain ⟨ sd0, sd1 ⟩ := LoadH.shifted_read_data air row h_opcode h_row h_constraints h_is_valid
            obtain ⟨ sh, lsh, rsh ⟩ := LoadH.shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
            simp [w0, w1, w2, w3, sd0, sd1, sh]
            simp [VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification] at h_bus_wellformedness
            split_ifs
            . simp [← BitVec.toInt_inj,
                    BitVec.toInt_signExtend_of_le]
              repeat rw [BitVec.toInt_append]
              simp [Int.bmod_def]
              by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.read_data row 0 1)).msb
              . simp [hmsb]
                simp [BitVec.msb_eq_decide] at hmsb
                omega
              . simp [hmsb]
                simp [BitVec.msb_eq_decide] at hmsb
                omega
            . simp [← BitVec.toInt_inj,
                    BitVec.toInt_signExtend_of_le]
              repeat rw [BitVec.toInt_append]
              simp [Int.bmod_def]
              by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.read_data row 0 3)).msb
              . simp [hmsb]
                simp [BitVec.msb_eq_decide] at hmsb
                omega
              . simp [hmsb]
                simp [BitVec.msb_eq_decide] at hmsb
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
        rewrite [←h_instruction.2.2.2.1, ←h_instruction.1]
        simp [Transpiler.ind, Transpiler.wrap_to_regidx, regidx_to_fin]
        rewrite [←h_instruction.2.2.2.2.2.2.2.2.1, ←h_instruction.1]
        simp
        decide

  /-
     ***
     *** LB
     ***
  -/

  def LbInput_of_LoadSignExtend_instruction_fields (row : LoadSignExtend_instruction_fields) : PureSpec.LbInput := {
    r1 := BitVec.ofFin (Transpiler.wrap_to_regidx row.rs1)
    imm := BabyBear.toBV32 row.imm
    rd := BitVec.ofFin (Transpiler.wrap_to_regidx row.rd)
    r1_val := BabyBear.toBV32 row.rs1_val
    PC := row.pc.toNat
    data0 := if (row.shift = 0) then row.prev_read_data[0] else
             if (row.shift = 1) then row.prev_read_data[1] else
             if (row.shift = 2) then row.prev_read_data[2] else
                                     row.prev_read_data[3]
    : PureSpec.LbInput
  }

  def LbOutput_matches_LoadSignExtend_instruction_fields (row : LoadSignExtend_instruction_fields) (lb_output : PureSpec.LbOutput) : Prop :=
    BabyBear.isU32 row.imm ∧
    BabyBear.isU32 row.rs1_val ∧
    BabyBear.isU32 row.prev_read_data ∧
    BabyBear.isU32 row.read_data ∧
    (row.needs_write = 1 → BabyBear.isU32 row.prev_write_data) ∧
    (row.needs_write = 1 → BabyBear.isU32 row.write_data) ∧
    lb_output.nextPC = row.next_pc.toNat ∧
    row.read_address_space = row.memory_address_space ∧
    row.write_address_space = 1 ∧
    row.read_ptr.val = (BabyBear.toBV32 row.imm + BabyBear.toBV32 row.rs1_val).toNat - row.shift.val∧
    row.write_ptr = row.rd ∧
    row.prev_read_data = row.read_data ∧
    BitVec.signExtend 32 (BitVec.setWidth 12 (BabyBear.toBV32 row.imm)) = BabyBear.toBV32 row.imm ∧
    BabyBear.toBV32 row.imm = BitVec.signExtend 32 (BitVec.ofNat 16 row.imm_lower_half) ∧
    row.imm_sign = (BabyBear.toBV32 row.imm).msb.toNat ∧
    match lb_output.rd with
      | .none =>
        row.rd = 0 ∧
        row.needs_write = 0
      | .some (rd, rd_val) =>
        BabyBear.toBV32 row.write_data = rd_val ∧
        rd.1.toNat * 4 = row.rd.toNat ∧
        row.needs_write = 1

  lemma lb_spec_of_get_instruction_fields_part_1 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
  :
    (air.adapter.imm row 0).val % 256 < 256
  := by
    omega

  lemma lb_spec_of_get_instruction_fields_part_2 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 534)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.imm row 0).val / 256 < 256
  := by
    have := LoadB.imm_range air row h_opcode h_is_valid h_bus_wellformedness
    omega

  lemma lb_spec_of_get_instruction_fields_part_3 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
  :
    (air.adapter.imm_extended_limb row 0).val % 256 < 256
  := by
    omega

  lemma lb_spec_of_get_instruction_fields_part_4 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
  :
    (air.adapter.imm_extended_limb row 0).val / 256 < 256
  := by
    have := LoadB.imm_extend_range air row h_row h_constraints h_is_valid
    omega

  lemma lb_spec_of_get_instruction_fields_part_5 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_0 row 0).val < 256
  := by
    have := LoadB.rs1_data_0_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lb_spec_of_get_instruction_fields_part_6 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_1 row 0).val < 256
  := by
    have := LoadB.rs1_data_1_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lb_spec_of_get_instruction_fields_part_7 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_2 row 0).val < 256
  := by
    have := LoadB.rs1_data_2_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lb_spec_of_get_instruction_fields_part_8 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.adapter.rs1_data_3 row 0).val < 256
  := by
    have := LoadB.rs1_data_3_range air row h_is_valid h_bus_wellformedness
    apply Fin.lt_def.mp at this
    convert this

  lemma lb_spec_of_get_instruction_fields_part_9 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data row 0 0).val < 256
  := by
    have h_memory := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920 : FBB) = (-1 : FBB) by decide
    ] at h_memory
    exact h_memory.2.1.2.2.1

  lemma lb_spec_of_get_instruction_fields_part_10 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data row 0 1).val < 256
  := by
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.1

  lemma lb_spec_of_get_instruction_fields_part_11 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data row 0 2).val < 256
  := by
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.2.1

  lemma lb_spec_of_get_instruction_fields_part_12 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    (air.core.read_data row 0 3).val < 256
  := by
    . have h_memory := h_bus_wellformedness.2.1
      simp [
        VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
        h_is_valid,
        show (2013265920 : FBB) = (-1 : FBB) by decide
      ] at h_memory
      exact h_memory.2.1.2.2.2.2.2

  lemma lb_spec_of_get_instruction_fields_part_13 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
      VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920 : FBB) = (-1 : FBB) by decide,
      h_needs_write
    ] at h_memory
    split_ands
    . exact h_memory.2.2.2.2.1
    . exact h_memory.2.2.2.2.2.1
    . exact h_memory.2.2.2.2.2.2.1
    . exact h_memory.2.2.2.2.2.2.2

  lemma lb_spec_of_get_instruction_fields_part_14 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 534)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.adapter.needs_write row 0 = 1 →
    (air.core.write_data row 0 0).val < 256 ∧
    (air.core.write_data row 0 1).val < 256 ∧
    (air.core.write_data row 0 2).val < 256 ∧
    (air.core.write_data row 0 3).val < 256
  := by
    intro h_needs_write
    have h_memory := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920 : FBB) = (-1 : FBB) by decide,
      h_needs_write
    ] at h_memory
    obtain ⟨ w0, w1, w2, w3 ⟩ := LoadB.write_data_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    rewrite [ w0, w1, w2, w3 ]
    obtain ⟨ sd0, sd1 ⟩ := LoadB.shifted_read_data air row h_opcode h_row h_constraints h_is_valid
    simp; split_ands
    . split_ifs <;> grind
    all_goals
      split_ifs
      . by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.read_data row 0 0)).msb <;> simp [hmsb]
      . by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.read_data row 0 1)).msb <;> simp [hmsb]
      . by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.read_data row 0 2)).msb <;> simp [hmsb]
      . by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.read_data row 0 3)).msb <;> simp [hmsb]

  lemma lb_spec_of_get_instruction_fields_part_15 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
  :
    BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32 =
    BitVec.ofNat 32 (air.to_pc row 0).val
  := by
    simp [
      Valid_VmAirWrapper_load_sign_extend.to_pc
    ]
    have h_execution := h_bus_axioms.1
    simp [
      VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_execution
    rewrite [Fin.val_add, Nat.mod_eq_of_lt, BitVec.ofNat_add]
    . simp
    . omega

  set_option maxHeartbeats 0 in
  lemma lb_spec_of_get_instruction_fields_part_16 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 534)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
    have := LoadB.read_ptr_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    rewrite [this]; clear this
    have h_mem_ptr := LoadB.mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    have h_imm_sign_extend := LoadB.imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness
    rewrite [h_imm_sign_extend] at h_mem_ptr
    rewrite [BitVec.toNat_eq] at h_mem_ptr
    simp [-BitVec.toNat_add] at h_mem_ptr
    rewrite [BitVec.toNat_add] at h_mem_ptr
    simp at h_mem_ptr
    rewrite [Nat.mod_eq_of_lt (by omega)] at h_mem_ptr
    rw [Fin.sub_val_of_le
        (by have h_ptr_range := LoadB.mem_ptr_range air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
            obtain ⟨ sh, lsh, rsh ⟩ := LoadB.shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
            simp [sh] at h_ptr_range ⊢
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
    := by exact concat16_eq_shift_add x y
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

  set_option maxRecDepth 2_000_000 in
  lemma lb_spec_of_get_instruction_fields_part_17 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 534)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
    have := LoadB.imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) :
      BitVec.setWidth 12 (bv1 ++ bv2 ++ bv3 ++ bv4) =
      BitVec.setWidth 12 (bv3 ++ bv4)
    := by exact setWidth12_append_four_eq_tail bv1 bv2 bv3 bv4
    rewrite [this]; clear this
    -- combine the two halves of imm into BitVec.ofNat 16 imm
    have h_imm_range := LoadB.imm_range air row h_opcode h_is_valid h_bus_wellformedness
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
        VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
        h_is_valid,
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨
        instruction,
        data,
        ⟨h_instruction, _, h_data_opcode, _, _, h_data_imm, _⟩
      ⟩ := h_transpile
      rewrite [←h_data_imm]
      have := Transpiler.transpiler_opcode_534 h_instruction
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
        simp (disch := omega) [←h_instruction, Transpiler.utof, Transpiler.sign_extend_16, Nat.mod_eq_of_lt]
        exact signExtend32_setWidth12_signExtend16_eq imm
      }
    convert this using 1
    . simp [BitVec.ofNat, Nat.cast]
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
      dsimp
      simp (disch := omega) [Nat.mod_eq_of_lt]
    . have h_imm_extended_range := LoadB.imm_extend_range air row h_row h_constraints h_is_valid
      have h_split_imm_extended := split_bitvec_16_to_8s h_imm_extended_range
      simp [BitVec.ofNat, Nat.cast] at h_split_imm_extended
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat at h_split_imm_extended
      dsimp at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt] at h_split_imm_extended
      simp (disch := omega) [Nat.mod_eq_of_lt]
      rewrite [←h_split_imm_extended]
      have := LoadB.imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness
      rewrite [this]
      simp [BitVec.ofNat, Nat.cast]
      unfold NatCast.natCast Fin.NatCast.instNatCast Fin.ofNat
      dsimp
      simp (disch := omega) [Nat.mod_eq_of_lt]

  lemma lb_spec_of_get_instruction_fields_part_18 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 534)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
    have := LoadB.imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness
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
        have := LoadB.imm_extend_range air row h_row h_constraints h_is_valid
        omega
      simp [Nat.mod_eq_of_lt this]
      have (bv1 bv2: BitVec 8) :
        256#16 * BitVec.setWidth 16 bv1 + BitVec.setWidth 16 bv2 =
        bv1 ++ bv2
      := by exact concat8_eq_mul_add bv1 bv2
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
        have := LoadB.imm_range air row h_opcode h_is_valid h_bus_wellformedness
        omega
      simp [Nat.mod_eq_of_lt this]
      have (bv1 bv2: BitVec 8) :
        256#16 * BitVec.setWidth 16 bv1 + BitVec.setWidth 16 bv2 =
        bv1 ++ bv2
      := by exact concat8_eq_mul_add bv1 bv2
      rewrite [←this]
      congr <;> {
        unfold BitVec.setWidth BitVec.setWidth' BitVec.toNat
        simp [BitVec.ofNat]
        refine BitVec.eq_of_toNat_eq ?_
        simp
        omega
      }

  lemma lb_spec_of_get_instruction_fields_part_19 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_opcode : air.core.expected_opcode row 0 = 534)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_axioms : VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
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
    have := LoadB.imm_sign air row h_bus_wellformedness h_is_valid h_opcode
    rewrite [this]; clear this
    simp [U32.toBV]
    have (bv1 bv2 bv3 bv4: BitVec 8) : (bv1 ++ bv2 ++ bv3 ++ bv4).msb = bv1.msb := by
      repeat rw [BitVec.msb_append]
      simp
    simp [this]
    have := LoadB.imm_extend_range air row h_row h_constraints h_is_valid
    have :
      (air.adapter.imm_extended_limb row 0).val / 256 % 256 =
      (air.adapter.imm_extended_limb row 0).val / 256
    := by
      omega
    simp [this]
    have h_sign_extend := LoadB.imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness
    have (bv1 bv2: BitVec 32): bv1 = bv2 → bv1.msb = bv2.msb := by intro h; grind
    apply this at h_sign_extend
    have (bv: BitVec 16) : (bv.signExtend 32).msb = bv.msb := by
      simp [BitVec.msb_signExtend]
    rewrite [this] at h_sign_extend
    rewrite [h_sign_extend]
    have (bv1 bv2: BitVec 16): (bv1 ++ bv2).msb = bv1.msb := by
      rw [BitVec.msb_append]
      simp
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
  set_option maxRecDepth 2_000_000 in
  lemma lb_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).opcode = 534 →
        LbOutput_matches_LoadSignExtend_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_LOADB_pure
            (LbInput_of_LoadSignExtend_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [
      LbOutput_matches_LoadSignExtend_instruction_fields,
      get_instruction_fields_row,
      -BitVec.toNat_add
    ]
    rewrite [BitVec.toNat_add]
    simp

    rewrite [allHold_allRows] at h_constraints
    specialize h_constraints ⟨row, by omega⟩
    specialize h_bus_axioms row h_row
    specialize h_bus_wellformedness row h_row
    simp [LbInput_of_LoadSignExtend_instruction_fields, PureSpec.execute_LOADB_pure]

    split_ands
    . exact lb_spec_of_get_instruction_fields_part_1 air row
    . exact lb_spec_of_get_instruction_fields_part_2 air row h_is_valid h_opcode h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_3 air row
    . exact lb_spec_of_get_instruction_fields_part_4 air row h_row h_is_valid h_constraints
    . exact lb_spec_of_get_instruction_fields_part_5 air row h_is_valid h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_6 air row h_is_valid h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_7 air row h_is_valid h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_8 air row h_is_valid h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_9 air row h_is_valid h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_10 air row h_is_valid h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_11 air row h_is_valid h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_12 air row h_is_valid h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_13 air row h_is_valid h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_14 air row h_row h_is_valid h_opcode h_constraints h_bus_wellformedness
    . exact lb_spec_of_get_instruction_fields_part_15 air row h_is_valid h_bus_axioms
    . exact LoadB.read_as air row h_is_valid
    . exact LoadB.write_as air row h_is_valid
    . apply lb_spec_of_get_instruction_fields_part_16 air row h_row h_is_valid h_opcode h_constraints h_bus_wellformedness
    . exact LoadB.write_ptr air row h_is_valid
    . apply lb_spec_of_get_instruction_fields_part_17 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . apply lb_spec_of_get_instruction_fields_part_18 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . apply lb_spec_of_get_instruction_fields_part_19 air row h_row h_is_valid h_opcode h_constraints h_bus_axioms h_bus_wellformedness
    . have h_transpile := h_bus_wellformedness.2.2.2
      simp [
        VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
        h_is_valid,
        Interaction.ProgramBusEntry.operand_properties
      ] at h_transpile
      obtain ⟨instruction, data, h_instruction⟩ := h_transpile
      have h_aligned := Transpiler.pc_aligned_of_some h_instruction.1
      have h_bound := Transpiler.pc_bound_of_some h_instruction.1
      have h_rd := Transpiler.transpiler_opcode_534 h_instruction.1
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
        rewrite [←h_instruction.2.2.2.1, ←h_instruction.1]
        simp [Transpiler.ind, Transpiler.wrap_to_regidx, regidx_to_fin]
        rewrite [dite_cond_eq_false]
        . simp
          rewrite [←h_instruction.2.2.2.2.2.2.2.2.1, ←h_instruction.1]
          simp
          obtain ⟨⟨rd: Fin 32⟩⟩ := rd
          split_ands
          . obtain ⟨ w0, w1, w2, w3 ⟩ := LoadB.write_data_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
            obtain ⟨ sh, lsh, rsh ⟩ := LoadB.shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
            have shift_msb_is_bool := LoadB.shift_msb_is_bool air row h_opcode h_row h_constraints h_is_valid
            simp [w0, w1, w2, w3, sh]
            simp [
              VmAirWrapper_Rv32LoadStoreAdapterAir_LoadSignExtendCoreAir_4_8_constraint_and_interaction_simplification,
              h_is_valid,
              show (2013265920 : FBB) = (-1 : FBB) by decide
            ] at h_bus_wellformedness
            split_ifs with hif0 hif1 hif2
            . simp [← BitVec.toInt_inj,
                    BitVec.toInt_signExtend_of_le]
              simp [U32.toInt, ← U32.msb_3_negative, U32.toNat, BitVec.msb_eq_decide]
              simp [hif0]
              simp [Int.bmod_def]
              by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.read_data row 0 0)).msb
              . simp [BitVec.msb_eq_decide] at hmsb
                rw [decide_eq_true (by omega)]
                simp; omega
              . simp [BitVec.msb_eq_decide] at hmsb
                rw [decide_eq_false (by omega)]
                simp; omega
            . simp [← BitVec.toInt_inj,
                    BitVec.toInt_signExtend_of_le]
              simp [U32.toInt, ← U32.msb_3_negative, U32.toNat, BitVec.msb_eq_decide]
              simp [hif1]
              simp [hif1] at hif0
              simp [*, Int.bmod_def]
              by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.read_data row 0 1)).msb
              . simp [BitVec.msb_eq_decide] at hmsb
                rw [decide_eq_true (by omega)]
                simp; omega
              . simp [BitVec.msb_eq_decide] at hmsb
                rw [decide_eq_false (by omega)]
                simp; omega
            . simp [← BitVec.toInt_inj,
                    BitVec.toInt_signExtend_of_le]
              simp [U32.toInt, ← U32.msb_3_negative, U32.toNat, BitVec.msb_eq_decide]
              simp [hif2] at hif0 hif1 ⊢
              simp [*, Int.bmod_def]
              by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.read_data row 0 2)).msb
              . simp [BitVec.msb_eq_decide] at hmsb
                rw [decide_eq_true (by omega)]
                simp; omega
              . simp [BitVec.msb_eq_decide] at hmsb
                rw [decide_eq_false (by omega)]
                simp; omega
            . simp [← BitVec.toInt_inj,
                    BitVec.toInt_signExtend_of_le]
              simp [U32.toInt, ← U32.msb_3_negative, U32.toNat, BitVec.msb_eq_decide]
              have shift_msb_is_bool := LoadB.shift_msb_is_bool air row h_opcode h_row h_constraints h_is_valid
              simp at hif0 hif1 hif2
              obtain smsb | smsb := shift_msb_is_bool <;> [ (clear *- smsb hif1; grind); skip ]
              simp [smsb] at hif0 hif1 hif2 ⊢
              simp [*, Int.bmod_def]
              by_cases hmsb : (BitVec.ofNat 8 ↑(air.core.read_data row 0 3)).msb
              . simp [BitVec.msb_eq_decide] at hmsb
                rw [decide_eq_true (by omega)]
                simp; omega
              . simp [BitVec.msb_eq_decide] at hmsb
                rw [decide_eq_false (by omega)]
                simp; omega
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
        rewrite [←h_instruction.2.2.2.1, ←h_instruction.1]
        simp [Transpiler.ind, Transpiler.wrap_to_regidx, regidx_to_fin]
        rewrite [←h_instruction.2.2.2.2.2.2.2.2.1, ←h_instruction.1]
        simp
        decide

  /-
     ***
     *** Main specification
     ***
  -/

  def LoadSignExtend_instruction_fields.spec (row : LoadSignExtend_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode ∈ Finset.Icc 534 535 ∧
      (row.opcode = 534 →
        LbOutput_matches_LoadSignExtend_instruction_fields
          row
          (PureSpec.execute_LOADB_pure (LbInput_of_LoadSignExtend_instruction_fields row))
      ) ∧
      (row.opcode = 535 →
        LhOutput_matches_LoadSignExtend_instruction_fields
          row
          (PureSpec.execute_LOADH_pure (LhInput_of_LoadSignExtend_instruction_fields row))
      )
    )

  lemma spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    List.Forall LoadSignExtend_instruction_fields.spec (get_instruction_fields air)
  := by
    apply List.forall_iff_forall_mem.mpr
    intro instruction_fields h_instruction_fields
    unfold LoadSignExtend_instruction_fields.spec

    intro h_is_valid

    simp [get_instruction_fields] at h_instruction_fields
    obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
    rewrite [←h_fields] at ⊢ h_is_valid; clear h_fields

    simp [get_instruction_fields_row] at h_is_valid

    split_ands
    . exact get_instruction_fields_row_opcode_range air row (by omega) h_constraints h_is_valid
    . exact lb_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness
    . exact lh_spec_of_get_instruction_fields air row (by omega) h_constraints h_is_valid h_bus_axioms h_bus_wellformedness

  theorem loadstore_spec [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List LoadSignExtend_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall LoadSignExtend_instruction_fields.spec
  := by
    use get_instruction_fields air
    simp only [
      bus_from_instruction_fields_eq_air_buses air h_constraints,
      spec_of_get_instruction_fields air h_constraints h_bus_axioms h_bus_wellformedness
    ]
    trivial

end Equivalence.LoadSignExtend
