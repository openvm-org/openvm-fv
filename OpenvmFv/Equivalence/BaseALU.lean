import OpenvmFv.Spec.BaseALU

import OpenvmFv.Spec.RTYPE.add
import OpenvmFv.Spec.RTYPE.sub
import OpenvmFv.Spec.RTYPE.xor
import OpenvmFv.Spec.RTYPE.or
import OpenvmFv.Spec.RTYPE.and

import OpenvmFv.Spec.ITYPE.addi
import OpenvmFv.Spec.ITYPE.andi
import OpenvmFv.Spec.ITYPE.ori
import OpenvmFv.Spec.ITYPE.xori


namespace Equivalence.BaseALU

  @[ext]
  structure ALU_instruction_fields where
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

    range_checked_vals : Vector FBB 6
    bitwise_vals : Vector (Vector FBB 3) 5

  lemma ALU_instruction_fields_eq (a b : ALU_instruction_fields)
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
    a.range_checked_vals = b.range_checked_vals ∧
    a.bitwise_vals = b.bitwise_vals
      → a = b
  := by
    intro field_eq
    ext <;> grind

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val / 4 % 32, by grind⟩

  def AddInput_of_ALU_instruction_fields (row : ALU_instruction_fields) : PureSpec.AddInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.AddInput
  }

  def AddiInput_of_ALU_instruction_fields (row : ALU_instruction_fields) : PureSpec.AddiInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 12 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.AddiInput
  }

  def SubInput_of_ALU_instruction_fields (row : ALU_instruction_fields) : PureSpec.SubInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SubInput
  }

  def XorInput_of_ALU_instruction_fields (row : ALU_instruction_fields) : PureSpec.XorInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.XorInput
  }

  def XoriInput_of_ALU_instruction_fields (row : ALU_instruction_fields) : PureSpec.XoriInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 12 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.XoriInput
  }

  def OrInput_of_ALU_instruction_fields (row : ALU_instruction_fields) : PureSpec.OrInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.OrInput
  }

  def OriInput_of_ALU_instruction_fields (row : ALU_instruction_fields) : PureSpec.OriInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 12 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.OriInput
  }

  def AndInput_of_ALU_instruction_fields (row : ALU_instruction_fields) : PureSpec.AndInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.AndInput
  }

  def AndiInput_of_ALU_instruction_fields (row : ALU_instruction_fields) : PureSpec.AndiInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 12 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.AndiInput
  }

  def AddOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (add_output : PureSpec.AddOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    add_output.nextPC = row.next_pc.toNat ∧
    match add_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def AddiOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (addi_output : PureSpec.AddiOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    addi_output.nextPC = row.next_pc.toNat ∧
    match addi_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def SubOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (sub_output : PureSpec.SubOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    sub_output.nextPC = row.next_pc.toNat ∧
    match sub_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def XorOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (xor_output : PureSpec.XorOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    xor_output.nextPC = row.next_pc.toNat ∧
    match xor_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def XoriOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (xori_output : PureSpec.XoriOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    xori_output.nextPC = row.next_pc.toNat ∧
    match xori_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def OrOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (or_output : PureSpec.OrOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    or_output.nextPC = row.next_pc.toNat ∧
    match or_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def OriOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (ori_output : PureSpec.OriOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    ori_output.nextPC = row.next_pc.toNat ∧
    match ori_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def AndOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (and_output : PureSpec.AndOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    and_output.nextPC = row.next_pc.toNat ∧
    match and_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def AndiOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (andi_output : PureSpec.AndiOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    andi_output.nextPC = row.next_pc.toNat ∧
    match andi_output.rd with
      | .none =>
        row.a = row.prev_a ∧
        row.rd_ptr = 0
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat * 4 = row.rd_ptr.toNat

  def ALU_instruction_fields.spec (row : ALU_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      (row.non_imm = 0 ∨ row.non_imm = 1) ∧
      row.opcode ∈ Finset.Icc 512 516 ∧
      (row.non_imm = 1 → (
        (row.opcode = 512 →
          AddOutput_matches_ALU_instruction_fields
            row
            (PureSpec.execute_RTYPE_add_pure (AddInput_of_ALU_instruction_fields row))
        ) ∧
        (row.opcode = 513 →
          SubOutput_matches_ALU_instruction_fields
            row
            (PureSpec.execute_RTYPE_sub_pure (SubInput_of_ALU_instruction_fields row))
        ) ∧
        (row.opcode = 514 →
          XorOutput_matches_ALU_instruction_fields
            row
            (PureSpec.execute_RTYPE_xor_pure (XorInput_of_ALU_instruction_fields row))
        ) ∧
        (row.opcode = 515 →
          OrOutput_matches_ALU_instruction_fields
            row
            (PureSpec.execute_RTYPE_or_pure (OrInput_of_ALU_instruction_fields row))
        ) ∧
        (row.opcode = 516 →
          AndOutput_matches_ALU_instruction_fields
            row
            (PureSpec.execute_RTYPE_and_pure (AndInput_of_ALU_instruction_fields row))
        )
      )) ∧
      (row.non_imm = 0 → (
        (row.opcode = 512 →
          AddiOutput_matches_ALU_instruction_fields
            row
            (PureSpec.execute_ITYPE_addi_pure (AddiInput_of_ALU_instruction_fields row))
        ) ∧
        (row.opcode ≠ 513) ∧
        (row.opcode = 514 →
          XoriOutput_matches_ALU_instruction_fields
            row
            (PureSpec.execute_ITYPE_xori_pure (XoriInput_of_ALU_instruction_fields row))
        ) ∧
        (row.opcode = 515 →
          OriOutput_matches_ALU_instruction_fields
            row
            (PureSpec.execute_ITYPE_ori_pure (OriInput_of_ALU_instruction_fields row))
        ) ∧
        (row.opcode = 516 →
          AndiOutput_matches_ALU_instruction_fields
            row
            (PureSpec.execute_ITYPE_andi_pure (AndiInput_of_ALU_instruction_fields row))
        )
      ))
    )

  def ALU_instruction_fields.execution (row : ALU_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def ALU_instruction_fields.memory (row : ALU_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.prev_b_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.b_timestamp]),
    (-row.non_imm, [row.non_imm, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.prev_c_timestamp]),
    ( row.non_imm, [row.non_imm, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.c_timestamp]),
    (-row.is_valid, [1, row.rd_ptr, row.prev_a[0], row.prev_a[1], row.prev_a[2], row.prev_a[3], row.prev_a_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.a_timestamp]),
  ]

  def ALU_instruction_fields.range_checks (row : ALU_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
    (row.non_imm, [row.range_checked_vals[2], 17]),
    (row.non_imm, [row.range_checked_vals[3], 12]),
    (row.is_valid, [row.range_checked_vals[4], 17]),
    (row.is_valid, [row.range_checked_vals[5], 12]),
  ]

  def ALU_instruction_fields.read_instruction (row : ALU_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, row.rs1_ptr, row.rs2_ptr, 1, row.non_imm, 0, 0])
  ]

  def ALU_instruction_fields.bitwise (row : ALU_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.bitwise_vals[0][0], row.bitwise_vals[0][1], row.bitwise_vals[0][2], 1]),
    (row.is_valid, [row.bitwise_vals[1][0], row.bitwise_vals[1][1], row.bitwise_vals[1][2], 1]),
    (row.is_valid, [row.bitwise_vals[2][0], row.bitwise_vals[2][1], row.bitwise_vals[2][2], 1]),
    (row.is_valid, [row.bitwise_vals[3][0], row.bitwise_vals[3][1], row.bitwise_vals[3][2], 1]),
    (row.is_valid - row.non_imm, [row.bitwise_vals[4][0], row.bitwise_vals[4][1], row.bitwise_vals[4][2], 0]),
  ]

  def bus_from_instruction_fields (rows : List ALU_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then            rows.flatMap ALU_instruction_fields.execution
      else if index = MemoryBus then          rows.flatMap ALU_instruction_fields.memory
      else if index = RangeCheckerBus then    rows.flatMap ALU_instruction_fields.range_checks
      else if index = ProgramBus then rows.flatMap ALU_instruction_fields.read_instruction
      else if index = BitwiseBus then         rows.flatMap ALU_instruction_fields.bitwise
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_alu FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_alu.constraints.allHold air row.1 (by grind)

  def get_instruction_fields_row (air : Valid_VmAirWrapper_alu FBB ExtF) (row : ℕ) : ALU_instruction_fields := {
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
    bitwise_vals :=
      #v[
        #v[air.core.x_0 row 0, air.core.y_0 row 0, air.core.x_xor_y_0 row 0],
        #v[air.core.x_1 row 0, air.core.y_1 row 0, air.core.x_xor_y_1 row 0],
        #v[air.core.x_2 row 0, air.core.y_2 row 0, air.core.x_xor_y_2 row 0],
        #v[air.core.x_3 row 0, air.core.y_3 row 0, air.core.x_xor_y_3 row 0],
        #v[air.core.c_0 row 0, air.core.c_1 row 0, 0]
      ]
    : ALU_instruction_fields
  }

  def get_instruction_fields (air : Valid_VmAirWrapper_alu FBB ExtF) : List ALU_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => get_instruction_fields_row air row)

  lemma execution_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
  :
    List.flatMap (VmAirWrapper_alu.constraints.executionBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap ALU_instruction_fields.execution (get_instruction_fields air)
  := by
    unfold ALU_instruction_fields.execution
    unfold VmAirWrapper_alu.constraints.executionBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma memory_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
  :
    List.flatMap (VmAirWrapper_alu.constraints.memoryBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap ALU_instruction_fields.memory (get_instruction_fields air)
  := by
    unfold ALU_instruction_fields.memory
    unfold VmAirWrapper_alu.constraints.memoryBus_row
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map,
      h_neg_one
    ]

  lemma range_checks_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
  :
    List.flatMap (VmAirWrapper_alu.constraints.rangeCheckerBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap ALU_instruction_fields.range_checks (get_instruction_fields air)
  := by
    unfold ALU_instruction_fields.range_checks
    unfold VmAirWrapper_alu.constraints.rangeCheckerBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma read_instruction_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
  :
    List.flatMap (VmAirWrapper_alu.constraints.programBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap ALU_instruction_fields.read_instruction (get_instruction_fields air)
  := by
    unfold ALU_instruction_fields.read_instruction
    unfold VmAirWrapper_alu.constraints.programBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma bitwise_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
  :
    List.flatMap (VmAirWrapper_alu.constraints.bitwiseBus_row air) (List.range (air.last_row + 1)) =
    List.flatMap ALU_instruction_fields.bitwise (get_instruction_fields air)
  := by
    unfold ALU_instruction_fields.bitwise
    unfold VmAirWrapper_alu.constraints.bitwiseBus_row
    simp [
      get_instruction_fields,
      get_instruction_fields_row,
      List.flatMap_map
    ]

  lemma bus_from_instruction_fields_eq_air_buses [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (h_constraints : allHold_allRows air)
  :
    air.buses = bus_from_instruction_fields (get_instruction_fields air)
  := by
    have h_interactions := VmAirWrapper_alu.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold VmAirWrapper_alu.constraints.constrain_interactions at h_interactions
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
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
  :
    (get_instruction_fields_row air row).non_imm = 0 ∨
    (get_instruction_fields_row air row).non_imm = 1
  := by
    simp [get_instruction_fields_row]
    have := ALU.ValidRows.essentials
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
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
  :
    (get_instruction_fields_row air row).opcode ∈ Finset.Icc 512 516
  := by
    simp [get_instruction_fields_row]
    have := ALU.ValidRows.essentials
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
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
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
    unfold VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
    simp [
      VmAirWrapper_alu.constraints.propertiesToAssume,
      Interaction.ProgramBusEntry.operand_properties,
      VmAirWrapper_alu.constraints._programBus_row,
      VmAirWrapper_alu.constraints.programBus_row,
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

  lemma add_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 512)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_cases := Transpiler.transpiler_opcode_512 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_addi =>
        exfalso
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_addi
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
      | inr h_add =>
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_add
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

  lemma add_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
  :
    ((get_instruction_fields_row air row).opcode = 512 →
        AddOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_add_pure
            (AddInput_of_ALU_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [AddOutput_matches_ALU_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= ALU.ValidRows.essentials
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
      simp [PureSpec.execute_RTYPE_add_pure, AddInput_of_ALU_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_constraints h_non_imm h_a0 h_a1 h_a2 h_a3
      simp [AddInput_of_ALU_instruction_fields, PureSpec.execute_RTYPE_add_pure]
      have h_rd := add_rd_properties
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
        h_a0, h_a1, h_a2, h_a3,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_ind

      split_ands
      . have h_spec := ALU.ValidRows.spec_base_ALU_non_imm
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
          ALU.ValidRows.rop_of_ALU_opcode, execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        convert h_spec
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma sub_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 513)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_sub := Transpiler.transpiler_opcode_513 h_transpile.1 h_transpile.2.2.2.1
    obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_sub
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

  lemma sub_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
  :
    ((get_instruction_fields_row air row).opcode = 513 →
        SubOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_sub_pure
            (SubInput_of_ALU_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [SubOutput_matches_ALU_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= ALU.ValidRows.essentials
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
      simp [PureSpec.execute_RTYPE_sub_pure, SubInput_of_ALU_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_constraints h_non_imm h_a0 h_a1 h_a2 h_a3
      simp [SubInput_of_ALU_instruction_fields, PureSpec.execute_RTYPE_sub_pure]
      have h_rd := sub_rd_properties
        air
        row
        h_is_valid
        (h_bus_wellformedness row h_row)
        h_opcode
      obtain ⟨h_rd_non_zero, h_rd_ind⟩ := h_rd
      simp only [dite_cond_eq_false, h_rd_non_zero]
      simp [get_instruction_fields_row] at ⊢ h_rd_ind
      obtain ⟨rd, h_rd_ind⟩ := h_rd_ind
      simp [
        true_and,
        h_a0, h_a1, h_a2, h_a3,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_ind

      split_ands
      . have h_spec := ALU.ValidRows.spec_base_ALU_non_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row h_row)
          (h_bus_wellformedness row h_row)
          h_non_imm

        simp [
          ALU.ValidRows.rop_of_ALU_opcode, execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        convert h_spec
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma xor_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 514)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_cases := Transpiler.transpiler_opcode_514 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_xori =>
        exfalso
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_xori
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
      | inr h_xor =>
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_xor
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

  lemma xor_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
  :
    ((get_instruction_fields_row air row).opcode = 514 →
        XorOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_xor_pure
            (XorInput_of_ALU_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [XorOutput_matches_ALU_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= ALU.ValidRows.essentials
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
      simp [PureSpec.execute_RTYPE_xor_pure, XorInput_of_ALU_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_constraints h_non_imm h_a0 h_a1 h_a2 h_a3
      simp [XorInput_of_ALU_instruction_fields, PureSpec.execute_RTYPE_xor_pure]
      have h_rd := xor_rd_properties
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
        h_a0, h_a1, h_a2, h_a3,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_ind

      split_ands
      . have h_spec := ALU.ValidRows.spec_base_ALU_non_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row h_row)
          (h_bus_wellformedness row h_row)
          h_non_imm

        simp [
          ALU.ValidRows.rop_of_ALU_opcode, execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        convert h_spec
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma or_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 515)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_cases := Transpiler.transpiler_opcode_515 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_ori =>
        exfalso
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_ori
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
      | inr h_or =>
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_or
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

  lemma or_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
  :
    ((get_instruction_fields_row air row).opcode = 515 →
        OrOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_or_pure
            (OrInput_of_ALU_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [OrOutput_matches_ALU_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= ALU.ValidRows.essentials
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
      simp [PureSpec.execute_RTYPE_or_pure, OrInput_of_ALU_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_constraints h_non_imm h_a0 h_a1 h_a2 h_a3
      simp [OrInput_of_ALU_instruction_fields, PureSpec.execute_RTYPE_or_pure]
      have h_rd := or_rd_properties
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
        h_a0, h_a1, h_a2, h_a3,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_ind

      split_ands
      . have h_spec := ALU.ValidRows.spec_base_ALU_non_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row h_row)
          (h_bus_wellformedness row h_row)
          h_non_imm

        simp [
          ALU.ValidRows.rop_of_ALU_opcode, execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        convert h_spec
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma and_rd_properties [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 516)
  :
    ¬wrap_to_regidx (get_instruction_fields_row air row).rd_ptr = 0 ∧
    ∃ rd, (get_instruction_fields_row air row).rd_ptr = Transpiler.ind rd
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid h_bus_wellformedness
    simp [wrap_to_regidx, get_instruction_fields_row]
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness
    rewrite [h_opcode] at h_transpile
    have h_pc_aligned := Transpiler.pc_aligned_of_some h_transpile.1
    have h_cases := Transpiler.transpiler_opcode_516 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_andi =>
        exfalso
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_andi
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
      | inr h_and =>
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_and
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

  lemma and_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_non_imm : air.adapter.rs2_as row 0 = 1)
  :
    ((get_instruction_fields_row air row).opcode = 516 →
        AndOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_and_pure
            (AndInput_of_ALU_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [AndOutput_matches_ALU_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= ALU.ValidRows.essentials
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
      simp [PureSpec.execute_RTYPE_and_pure, AndInput_of_ALU_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_constraints h_non_imm h_a0 h_a1 h_a2 h_a3
      simp [AndInput_of_ALU_instruction_fields, PureSpec.execute_RTYPE_and_pure]
      have h_rd := and_rd_properties
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
        h_a0, h_a1, h_a2, h_a3,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_ind

      split_ands
      . have h_spec := ALU.ValidRows.spec_base_ALU_non_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row h_row)
          (h_bus_wellformedness row h_row)
          h_non_imm

        simp [
          ALU.ValidRows.rop_of_ALU_opcode, execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        convert h_spec
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma addi_register_properties [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 512)
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
    have h_cases := Transpiler.transpiler_opcode_512 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_addi =>
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_addi
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
      | inr h_add =>
        exfalso
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_add
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

  lemma addi_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
  :
    ((get_instruction_fields_row air row).opcode = 512 →
      AddiOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
        (PureSpec.execute_ITYPE_addi_pure
          (AddiInput_of_ALU_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [AddiOutput_matches_ALU_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= ALU.ValidRows.essentials
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
      simp [PureSpec.execute_ITYPE_addi_pure, AddiInput_of_ALU_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_constraints h_imm h_a0 h_a1 h_a2 h_a3
      simp [AddiInput_of_ALU_instruction_fields, PureSpec.execute_ITYPE_addi_pure]
      have h_rd := addi_register_properties
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
        h_a0, h_a1, h_a2, h_a3,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_ind

      split_ands
      . have h_spec := ALU.ValidRows.spec_base_ALU_imm
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
          ALU.ValidRows.iop_of_ALU_opcode, execute_ITYPE_pure,
          execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        convert h_spec
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma subi_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
  :
    ((get_instruction_fields_row air row).opcode ≠ 513)
  := by
    replace h_bus_wellformedness := transpile_of_bus_wellformedness air row h_is_valid (h_bus_wellformedness row h_row)
    obtain ⟨instruction, mult, result, h_transpile⟩ := h_bus_wellformedness

    by_cases h_opcode : ((get_instruction_fields_row air row).opcode = 513)
    . simp [get_instruction_fields_row] at h_opcode
      rewrite [h_opcode] at h_transpile
      simp [get_instruction_fields_row]
      have h_cases := Transpiler.transpiler_opcode_513 h_transpile.1 h_transpile.2.2.2.1
      simp at h_cases
      simp [h_cases.1, h_imm] at h_transpile
    . exact h_opcode

  lemma xori_register_properties [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 514)
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
    have h_cases := Transpiler.transpiler_opcode_514 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_xori =>
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_xori
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
      | inr h_xor =>
        exfalso
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_xor
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

  lemma xori_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
  :
    ((get_instruction_fields_row air row).opcode = 514 →
      XoriOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
        (PureSpec.execute_ITYPE_xori_pure
          (XoriInput_of_ALU_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [XoriOutput_matches_ALU_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= ALU.ValidRows.essentials
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
      simp [PureSpec.execute_ITYPE_xori_pure, XoriInput_of_ALU_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_constraints h_imm h_a0 h_a1 h_a2 h_a3
      simp [XoriInput_of_ALU_instruction_fields, PureSpec.execute_ITYPE_xori_pure]
      have h_rd := xori_register_properties
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
        h_a0, h_a1, h_a2, h_a3,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_ind

      split_ands
      . have h_spec := ALU.ValidRows.spec_base_ALU_imm
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
          ALU.ValidRows.iop_of_ALU_opcode, execute_ITYPE_pure,
          execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        convert h_spec
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma ori_register_properties [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 515)
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
    have h_cases := Transpiler.transpiler_opcode_515 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_ori =>
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_ori
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
      | inr h_or =>
        exfalso
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_or
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

  lemma ori_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
  :
    ((get_instruction_fields_row air row).opcode = 515 →
      OriOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
        (PureSpec.execute_ITYPE_ori_pure
          (OriInput_of_ALU_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [OriOutput_matches_ALU_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= ALU.ValidRows.essentials
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
      simp [PureSpec.execute_ITYPE_ori_pure, OriInput_of_ALU_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_constraints h_imm h_a0 h_a1 h_a2 h_a3
      simp [OriInput_of_ALU_instruction_fields, PureSpec.execute_ITYPE_ori_pure]
      have h_rd := ori_register_properties
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
        h_a0, h_a1, h_a2, h_a3,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_ind

      split_ands
      . have h_spec := ALU.ValidRows.spec_base_ALU_imm
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
          ALU.ValidRows.iop_of_ALU_opcode, execute_ITYPE_pure,
          execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        convert h_spec
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma andi_register_properties [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
    (h_opcode : (air.core.ctx row 0).instruction.opcode = 516)
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
    have h_cases := Transpiler.transpiler_opcode_516 h_transpile.1 h_transpile.2.2.2.1
    cases h_cases with
      | inl h_andi =>
        obtain ⟨h_rs2_as, ⟨imm, rs1, rd, h_instruction, h_rd⟩⟩ := h_andi
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
      | inr h_and =>
        exfalso
        obtain ⟨h_rs2_as, ⟨rs2, rs1, rd, h_instruction, h_rd⟩⟩ := h_and
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

  lemma andi_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
    (h_imm : air.adapter.rs2_as row 0 = 0)
  :
    ((get_instruction_fields_row air row).opcode = 516 →
      AndiOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
        (PureSpec.execute_ITYPE_andi_pure
          (AndiInput_of_ALU_instruction_fields (get_instruction_fields_row air row))))
  := by
    intro h_opcode
    simp [get_instruction_fields_row] at h_opcode
    simp [AndiOutput_matches_ALU_instruction_fields]
    have ⟨
        h_pc,
        ⟨
          h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3
        ⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩:= ALU.ValidRows.essentials
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
      simp [PureSpec.execute_ITYPE_andi_pure, AndiInput_of_ALU_instruction_fields, get_instruction_fields_row]
      simp [← BitVec.toNat_inj]
      specialize h_bus_assumptions row h_row
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    . clear *-h_bus_assumptions h_bus_wellformedness h_row h_is_valid h_opcode h_constraints h_imm h_a0 h_a1 h_a2 h_a3
      simp [AndiInput_of_ALU_instruction_fields, PureSpec.execute_ITYPE_andi_pure]
      have h_rd := andi_register_properties
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
        h_a0, h_a1, h_a2, h_a3,
        wrap_to_regidx,
        h_rd_ind
      ]
      clear h_a0 h_a1 h_a2 h_a3 h_rd_ind

      split_ands
      . have h_spec := ALU.ValidRows.spec_base_ALU_imm
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
          ALU.ValidRows.iop_of_ALU_opcode, execute_ITYPE_pure,
          execute_RTYPE_pure,
          h_opcode
        ] at h_spec

        convert h_spec
      . simp [Transpiler.ind, regidx_to_fin]
        rewrite [Nat.mod_eq_of_lt]
        . simp [Nat.toNat, mul_comm]
        . convert @BitVec.toNat_lt_twoPow_of_le _ 5 _ rd.1
          simp

  lemma non_imm_spec_of_get_instruction_fields [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).non_imm = 1 →
    ((get_instruction_fields_row air row).opcode = 512 →
        AddOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_RTYPE_add_pure
            (AddInput_of_ALU_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 513 →
          SubOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_sub_pure
              (SubInput_of_ALU_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 514 →
          XorOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_xor_pure
              (XorInput_of_ALU_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 515 →
          OrOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_or_pure
              (OrInput_of_ALU_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 516 →
          AndOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_RTYPE_and_pure
              (AndInput_of_ALU_instruction_fields (get_instruction_fields_row air row)))))
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
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_allRows air)
    (h_is_valid : air.core.is_valid row 0 = 1)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
  :
    ((get_instruction_fields_row air row).non_imm = 0 →
    ((get_instruction_fields_row air row).opcode = 512 →
        AddiOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
          (PureSpec.execute_ITYPE_addi_pure
            (AddiInput_of_ALU_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode ≠ 513) ∧
      ((get_instruction_fields_row air row).opcode = 514 →
          XoriOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_ITYPE_xori_pure
              (XoriInput_of_ALU_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 515 →
          OriOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_ITYPE_ori_pure
              (OriInput_of_ALU_instruction_fields (get_instruction_fields_row air row)))) ∧
      ((get_instruction_fields_row air row).opcode = 516 →
          AndiOutput_matches_ALU_instruction_fields (get_instruction_fields_row air row)
            (PureSpec.execute_ITYPE_andi_pure
              (AndiInput_of_ALU_instruction_fields (get_instruction_fields_row air row)))))
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
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
  :
    List.Forall ALU_instruction_fields.spec (get_instruction_fields air)
  := by
    apply List.forall_iff_forall_mem.mpr
    intro instruction_fields h_instruction_fields
    unfold ALU_instruction_fields.spec

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
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List ALU_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall ALU_instruction_fields.spec
  := by
    use get_instruction_fields air
    simp only [
      bus_from_instruction_fields_eq_air_buses air h_constraints,
      spec_of_get_instruction_fields air h_constraints h_bus_assumptions h_bus_wellformedness
    ]
    trivial

end Equivalence.BaseALU
