import OpenvmFv.Spec.ALU

import OpenvmFv.Spec.RTYPE.add
import OpenvmFv.Spec.RTYPE.sub
import OpenvmFv.Spec.RTYPE.xor
import OpenvmFv.Spec.RTYPE.or
import OpenvmFv.Spec.RTYPE.and

import OpenvmFv.Spec.ITYPE.addi
import OpenvmFv.Spec.ITYPE.andi
import OpenvmFv.Spec.ITYPE.ori
import OpenvmFv.Spec.ITYPE.xori

set_option maxHeartbeats 1_000_000_000

namespace Equivalence.ALU

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

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val % 32, by grind⟩

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
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def AddiOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (addi_output : PureSpec.AddiOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    addi_output.nextPC = row.next_pc.toNat ∧
    match addi_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def SubOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (sub_output : PureSpec.SubOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    sub_output.nextPC = row.next_pc.toNat ∧
    match sub_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def XorOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (xor_output : PureSpec.XorOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    xor_output.nextPC = row.next_pc.toNat ∧
    match xor_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def XoriOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (xori_output : PureSpec.XoriOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    xori_output.nextPC = row.next_pc.toNat ∧
    match xori_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def OrOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (or_output : PureSpec.OrOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    or_output.nextPC = row.next_pc.toNat ∧
    match or_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def OriOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (ori_output : PureSpec.OriOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    ori_output.nextPC = row.next_pc.toNat ∧
    match ori_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def AndOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (and_output : PureSpec.AndOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    and_output.nextPC = row.next_pc.toNat ∧
    match and_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def AndiOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (andi_output : PureSpec.AndiOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    andi_output.nextPC = row.next_pc.toNat ∧
    match andi_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

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
      else if index = ReadInstructionBus then rows.flatMap ALU_instruction_fields.read_instruction
      else if index = BitwiseBus then         rows.flatMap ALU_instruction_fields.bitwise
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_alu FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_alu.constraints.allHold air row.1 (by grind)

  def get_instruction_fields (air : Valid_VmAirWrapper_alu FBB ExtF) : List ALU_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => {
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
    })

  theorem alu_spec [Field ExtF]
    (air : Valid_VmAirWrapper_alu FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_alu.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List ALU_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall ALU_instruction_fields.spec
  := by
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl

    have h_interactions := VmAirWrapper_alu.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold allHold_allRows at h_constraints
    use get_instruction_fields air
    split_ands
    . unfold VmAirWrapper_alu.constraints.constrain_interactions at h_interactions
      rewrite [h_interactions]; clear h_interactions
      unfold bus_from_instruction_fields ALU_instruction_fields.execution ALU_instruction_fields.memory ALU_instruction_fields.range_checks ALU_instruction_fields.read_instruction ALU_instruction_fields.bitwise
      simp [
        get_instruction_fields,
        VmAirWrapper_alu_constraint_and_interaction_simplification
      ]
      unfold VmAirWrapper_alu.constraints.executionBus_row
      unfold VmAirWrapper_alu.constraints.memoryBus_row
      unfold VmAirWrapper_alu.constraints.rangeCheckerBus_row
      unfold VmAirWrapper_alu.constraints.readInstructionBus_row
      unfold VmAirWrapper_alu.constraints.bitwiseBus_row
      funext index
      by_cases h_index: index = ExecutionBus
      . simp [h_index, List.flatMap_map]
      by_cases h_index: index = MemoryBus
      . simp [h_index, List.flatMap_map]
        congr
        funext row
        congr
        all_goals simp [h_neg_one]
      by_cases h_index: index = RangeCheckerBus
      . simp [h_index, List.flatMap_map]
      by_cases h_index: index = ReadInstructionBus
      . simp [h_index, List.flatMap_map]
      by_cases h_index: index = BitwiseBus
      . simp [h_index, List.flatMap_map]
      . simp [*]
    . apply List.forall_iff_forall_mem.mpr
      intro instruction_fields h_instruction_fields
      unfold ALU_instruction_fields.spec
      simp [get_instruction_fields] at h_instruction_fields
      obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
      rewrite [←h_fields]; clear h_fields
      simp

      intro h_is_valid

      have ⟨
        h_pc,
        h_timestamp,
        ⟨h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩ := ALU.ValidRows.essentials
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_assumptions row (by omega))
        (h_bus_wellformedness row (by omega))
      simp only [h_imm_binary, true_and]
      clear h_imm_binary

      -- discharge opcode range, leave non-imm specs and imm-specs respectively
      split_ands <;> [grind; grind; skip; skip]

      . intro h_non_imm
        have non_imm_spec := ALU.ValidRows.spec_base_ALU_non_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_wellformedness row (by omega))

        dsimp only at *

        split_ands
        . intro h_opcode
          simp [AddOutput_matches_ALU_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            assumption; assumption; assumption; assumption;
            skip; skip ]
          . simp [AddInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_add_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [AddInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_add_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; assumption; assumption; assumption; skip; skip ]
              . specialize non_imm_spec h_non_imm
                unfold execute_RTYPE_pure at non_imm_spec
                simp only [h_opcode, ALU.ValidRows.rop_of_ALU_opcode] at non_imm_spec
                dsimp at non_imm_spec
                assumption
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega
        . intro h_opcode
          simp [SubOutput_matches_ALU_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            assumption; assumption; assumption; assumption;
            skip; skip ]
          . simp [SubInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_sub_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [SubInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_sub_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; assumption; assumption; assumption; skip; skip ]
              . specialize non_imm_spec h_non_imm
                unfold execute_RTYPE_pure at non_imm_spec
                simp only [h_opcode, ALU.ValidRows.rop_of_ALU_opcode] at non_imm_spec
                dsimp at non_imm_spec
                assumption
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega
        . intro h_opcode
          simp [XorOutput_matches_ALU_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            assumption; assumption; assumption; assumption;
            skip; skip ]
          . simp [XorInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_xor_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [XorInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_xor_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; assumption; assumption; assumption; skip; skip ]
              . specialize non_imm_spec h_non_imm
                unfold execute_RTYPE_pure at non_imm_spec
                simp only [h_opcode, ALU.ValidRows.rop_of_ALU_opcode] at non_imm_spec
                dsimp at non_imm_spec
                assumption
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega
        . intro h_opcode
          simp [OrOutput_matches_ALU_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            assumption; assumption; assumption; assumption;
            skip; skip ]
          . simp [OrInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_or_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [OrInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_or_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; assumption; assumption; assumption; skip; skip ]
              . specialize non_imm_spec h_non_imm
                unfold execute_RTYPE_pure at non_imm_spec
                simp only [h_opcode, ALU.ValidRows.rop_of_ALU_opcode] at non_imm_spec
                dsimp at non_imm_spec
                assumption
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega
        . intro h_opcode
          simp [AndOutput_matches_ALU_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            assumption; assumption; assumption; assumption;
            skip; skip ]
          . simp [AndInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_and_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [AndInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_and_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; assumption; assumption; assumption; skip; skip ]
              . specialize non_imm_spec h_non_imm
                unfold execute_RTYPE_pure at non_imm_spec
                simp only [h_opcode, ALU.ValidRows.rop_of_ALU_opcode] at non_imm_spec
                dsimp at non_imm_spec
                assumption
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega
      . intro h_imm
        have imm_spec := ALU.ValidRows.spec_base_ALU_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row (by omega))
          (h_bus_wellformedness row (by omega))
          h_imm

        dsimp only at *

        split_ands

        . intro h_opcode
          simp [AddiOutput_matches_ALU_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            skip; skip; skip ]
          . clear *-h_imm_op_properties h_imm
            simp [h_imm] at h_imm_op_properties
            have := @BitVec.toInt_signExtend 12 24 (BitVec.ofNat 12 ↑(air.adapter.rs2 row 0))
            apply BitVec.eq_of_toInt_eq
            rewrite [this]
            simp
            have := h_imm_op_properties.2.2.1
            rewrite [this]
            exact Int.bmod_eq_of_le (by grind) (by grind)
          . simp [AddiInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_addi_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [AddiInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_addi_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; assumption; assumption; assumption; skip; skip ]
              . unfold execute_ITYPE_pure at imm_spec
                simp only [h_opcode, ALU.ValidRows.iop_of_ALU_opcode] at imm_spec
                dsimp at imm_spec
                assumption
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega
        . specialize h_imm_op_properties h_imm
          clear *-h_imm_op_properties
          grind
        . intro h_opcode
          simp [XoriOutput_matches_ALU_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            skip; skip; skip ]
          . clear *-h_imm_op_properties h_imm
            simp [h_imm] at h_imm_op_properties
            have := @BitVec.toInt_signExtend 12 24 (BitVec.ofNat 12 ↑(air.adapter.rs2 row 0))
            apply BitVec.eq_of_toInt_eq
            rewrite [this]
            simp
            have := h_imm_op_properties.2.2.1
            rewrite [this]
            exact Int.bmod_eq_of_le (by grind) (by grind)
          . simp [XoriInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_xori_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [XoriInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_xori_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; assumption; assumption; assumption; skip; skip ]
              . unfold execute_ITYPE_pure at imm_spec
                simp only [h_opcode, ALU.ValidRows.iop_of_ALU_opcode] at imm_spec
                dsimp at imm_spec
                assumption
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega
        . intro h_opcode
          simp [OriOutput_matches_ALU_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            skip; skip; skip ]
          . clear *-h_imm_op_properties h_imm
            simp [h_imm] at h_imm_op_properties
            have := @BitVec.toInt_signExtend 12 24 (BitVec.ofNat 12 ↑(air.adapter.rs2 row 0))
            apply BitVec.eq_of_toInt_eq
            rewrite [this]
            simp
            have := h_imm_op_properties.2.2.1
            rewrite [this]
            exact Int.bmod_eq_of_le (by grind) (by grind)
          . simp [OriInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_ori_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [OriInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_ori_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; assumption; assumption; assumption; skip; skip ]
              . unfold execute_ITYPE_pure at imm_spec
                simp only [h_opcode, ALU.ValidRows.iop_of_ALU_opcode] at imm_spec
                dsimp at imm_spec
                assumption
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega
        . intro h_opcode
          simp [AndiOutput_matches_ALU_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            skip; skip; skip ]
          . clear *-h_imm_op_properties h_imm
            simp [h_imm] at h_imm_op_properties
            have := @BitVec.toInt_signExtend 12 24 (BitVec.ofNat 12 ↑(air.adapter.rs2 row 0))
            apply BitVec.eq_of_toInt_eq
            rewrite [this]
            simp
            have := h_imm_op_properties.2.2.1
            rewrite [this]
            exact Int.bmod_eq_of_le (by grind) (by grind)
          . simp [AndiInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_andi_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [AndiInput_of_ALU_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_andi_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; assumption; assumption; assumption; skip; skip ]
              . unfold execute_ITYPE_pure at imm_spec
                simp only [h_opcode, ALU.ValidRows.iop_of_ALU_opcode] at imm_spec
                dsimp at imm_spec
                assumption
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_alu_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega

end Equivalence.ALU
