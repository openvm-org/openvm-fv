import OpenvmFv.Spec.Lt

import OpenvmFv.Spec.RTYPE.slt
import OpenvmFv.Spec.RTYPE.sltu

import OpenvmFv.Spec.ITYPE.slti
import OpenvmFv.Spec.ITYPE.sltiu

set_option maxHeartbeats 1_000_000_000

namespace Equivalence.Lt

  structure Lt_instruction_fields where
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

    prefix_sum : FBB

    range_checked_vals : Vector FBB 6
    bitwise_vals : Vector (Vector FBB 3) 3

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val % 32, by grind⟩

  def SltInput_of_Lt_instruction_fields (row : Lt_instruction_fields) : PureSpec.SltInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SltInput
  }

  def SltiInput_of_Lt_instruction_fields (row : Lt_instruction_fields) : PureSpec.SltiInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 12 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SltiInput
  }

  def SltuInput_of_Lt_instruction_fields (row : Lt_instruction_fields) : PureSpec.SltuInput := {
    r1_val := BabyBear.toBV32 row.b
    r2_val := BabyBear.toBV32 row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SltuInput
  }

  def SltiuInput_of_Lt_instruction_fields (row : Lt_instruction_fields) : PureSpec.SltiuInput := {
    r1_val := BabyBear.toBV32 row.b
    imm := BitVec.ofNat 12 row.rs2_ptr.toNat
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.SltiuInput
  }

  def SltOutput_matches_Lt_instruction_fields (row : Lt_instruction_fields) (slt_output : PureSpec.SltOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    slt_output.nextPC = row.next_pc.toNat ∧
    match slt_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def SltiOutput_matches_Lt_instruction_fields (row : Lt_instruction_fields) (slti_output : PureSpec.SltiOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    slti_output.nextPC = row.next_pc.toNat ∧
    match slti_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def SltuOutput_matches_Lt_instruction_fields (row : Lt_instruction_fields) (sltu_output : PureSpec.SltuOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    BabyBear.isU32 row.c ∧
    sltu_output.nextPC = row.next_pc.toNat ∧
    match sltu_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def SltiuOutput_matches_Lt_instruction_fields (row : Lt_instruction_fields) (sltiu_output : PureSpec.SltiuOutput) : Prop :=
    BabyBear.isU32 row.b ∧
    (BitVec.ofNat 12 (row.rs2_ptr)).signExtend 24 =
    (BitVec.ofNat 24 (row.rs2_ptr)) ∧
    sltiu_output.nextPC = row.next_pc.toNat ∧
    match sltiu_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        BabyBear.isU32 row.a ∧
        BabyBear.toBV32 row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def Lt_instruction_fields.spec (row : Lt_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      (row.non_imm = 0 ∨ row.non_imm = 1) ∧
      row.opcode ∈ Finset.Icc 520 521 ∧
      (row.non_imm = 1 →
        (row.opcode = 520 →
          SltOutput_matches_Lt_instruction_fields
            row
            (PureSpec.execute_RTYPE_slt_pure (SltInput_of_Lt_instruction_fields row))
        ) ∧
        (row.opcode = 521 →
          SltuOutput_matches_Lt_instruction_fields
            row
            (PureSpec.execute_RTYPE_sltu_pure (SltuInput_of_Lt_instruction_fields row))
        )
      ) ∧
      (row.non_imm = 0 →
        (row.opcode = 520 →
          SltiOutput_matches_Lt_instruction_fields
            row
            (PureSpec.execute_ITYPE_slti_pure (SltiInput_of_Lt_instruction_fields row))
        ) ∧
        (row.opcode = 521 →
          SltiuOutput_matches_Lt_instruction_fields
            row
            (PureSpec.execute_ITYPE_sltiu_pure (SltiuInput_of_Lt_instruction_fields row))
        )
      )
    )

  def Lt_instruction_fields.execution (row : Lt_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def Lt_instruction_fields.memory (row : Lt_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.prev_b_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.b_timestamp]),
    (-row.non_imm, [row.non_imm, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.prev_c_timestamp]),
    ( row.non_imm, [row.non_imm, row.rs2_ptr, row.c[0], row.c[1], row.c[2], row.c[3], row.c_timestamp]),
    (-row.is_valid, [1, row.rd_ptr, row.prev_a[0], row.prev_a[1], row.prev_a[2], row.prev_a[3], row.prev_a_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.a_timestamp]),
  ]

  def Lt_instruction_fields.range_checks (row : Lt_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
    (row.non_imm, [row.range_checked_vals[2], 17]),
    (row.non_imm, [row.range_checked_vals[3], 12]),
    (row.is_valid, [row.range_checked_vals[4], 17]),
    (row.is_valid, [row.range_checked_vals[5], 12]),
  ]

  def Lt_instruction_fields.read_instruction (row : Lt_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, row.rs1_ptr, row.rs2_ptr, 1, row.non_imm, 0, 0])
  ]

  def Lt_instruction_fields.bitwise (row : Lt_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.bitwise_vals[0][0], row.bitwise_vals[0][1], row.bitwise_vals[0][2], 0]),
    (row.prefix_sum, [row.bitwise_vals[1][0], row.bitwise_vals[1][1], row.bitwise_vals[1][2], 0]),
    (row.is_valid - row.non_imm, [row.bitwise_vals[2][0], row.bitwise_vals[2][1], row.bitwise_vals[2][2], 0])
  ]

  def bus_from_instruction_fields (rows : List Lt_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then            rows.flatMap Lt_instruction_fields.execution
      else if index = MemoryBus then          rows.flatMap Lt_instruction_fields.memory
      else if index = RangeCheckerBus then    rows.flatMap Lt_instruction_fields.range_checks
      else if index = ReadInstructionBus then rows.flatMap Lt_instruction_fields.read_instruction
      else if index = BitwiseBus then         rows.flatMap Lt_instruction_fields.bitwise
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_lt FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_lt.constraints.allHold air row.1 (by grind)

  def get_instruction_fields (air : Valid_VmAirWrapper_lt FBB ExtF) : List Lt_instruction_fields :=
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
      a := #v[air.core.cmp_result row 0, 0, 0, 0]
      b := #v[air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0]
      c := #v[air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0]
      prefix_sum := air.core.prefix_sum row 0 0,
      range_checked_vals :=
        #v[air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0,
           air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0,
           air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0,
           air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0,
           air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0,
           air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0]
      bitwise_vals :=
        #v[
            #v[air.core.b_msb_f row 0 + 128 * air.core.opcode_slt_flag row 0, air.core.c_msb_f row 0 + 128 * air.core.opcode_slt_flag row 0, 0],
            #v[air.core.diff_val row 0 - 1, 0, 0],
            #v[air.core.c_0 row 0, air.core.c_1 row 0, 0]
        ]
      : Lt_instruction_fields
    })

  set_option maxRecDepth 1_000_000 in
  theorem lt_spec [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_assumptions : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.assumptionsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_lt.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List Lt_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall Lt_instruction_fields.spec
  := by
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl

    have h_interactions := VmAirWrapper_lt.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold allHold_allRows at h_constraints
    use get_instruction_fields air
    split_ands
    . unfold VmAirWrapper_lt.constraints.constrain_interactions at h_interactions
      rewrite [h_interactions]; clear h_interactions
      unfold bus_from_instruction_fields Lt_instruction_fields.execution Lt_instruction_fields.memory Lt_instruction_fields.range_checks Lt_instruction_fields.read_instruction Lt_instruction_fields.bitwise
      simp [
        get_instruction_fields,
        VmAirWrapper_lt_constraint_and_interaction_simplification
      ]
      unfold VmAirWrapper_lt.constraints.executionBus_row
      unfold VmAirWrapper_lt.constraints.memoryBus_row
      unfold VmAirWrapper_lt.constraints.rangeCheckerBus_row
      unfold VmAirWrapper_lt.constraints.readInstructionBus_row
      unfold VmAirWrapper_lt.constraints.bitwiseBus_row
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
      . simp [h_index, List.flatMap_map, ← LessThanCoreAir_4.ctx.instruction.opcode_def]
      by_cases h_index: index = BitwiseBus
      . simp [h_index, List.flatMap_map]
      . simp [*]
    . apply List.forall_iff_forall_mem.mpr
      intro instruction_fields h_instruction_fields
      unfold Lt_instruction_fields.spec
      simp [get_instruction_fields] at h_instruction_fields
      obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
      rewrite [←h_fields]; clear h_fields
      simp

      intro h_is_valid

      have ⟨
        h_pc,
        h_timestamp,
        ⟨h_cmp, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3⟩,
        h_opcodes,
        h_imm_binary,
        h_imm_op_properties
      ⟩ := Lt.ValidRows.essentials
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

      dsimp only at *

      split_ands <;> [ grind; grind; skip; skip ]

      . intro h_non_imm
        have non_imm_spec := Lt.ValidRows.spec_base_Lt_non_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row (by omega))
          (h_bus_wellformedness row (by omega))

        split_ands

        . intro h_opcode
          simp [SltOutput_matches_Lt_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            assumption; assumption; assumption; assumption;
            skip; skip ]
          . simp [SltInput_of_Lt_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_slt_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [SltInput_of_Lt_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_slt_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; skip; skip ]
              . specialize non_imm_spec h_non_imm
                unfold execute_RTYPE_pure at non_imm_spec
                simp [h_opcode, Lt.ValidRows.rop_of_Lt_opcode] at non_imm_spec
                split_ifs at non_imm_spec with h_lt <;> simp at non_imm_spec h_lt
                . rw [if_pos]
                  . assumption
                  . simpa [BitVec.slt]
                . rw [if_neg]
                  . assumption
                  . simpa [BitVec.slt]
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega
        . intro h_opcode
          simp [SltuOutput_matches_Lt_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            assumption; assumption; assumption; assumption;
            skip; skip ]
          . simp [SltuInput_of_Lt_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_sltu_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [SltuInput_of_Lt_instruction_fields, BabyBear.toBV32, PureSpec.execute_RTYPE_sltu_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; skip; skip ]
              . specialize non_imm_spec h_non_imm
                unfold execute_RTYPE_pure at non_imm_spec
                simp [h_opcode, Lt.ValidRows.rop_of_Lt_opcode] at non_imm_spec
                split_ifs at non_imm_spec with h_lt <;> simp at non_imm_spec h_lt
                . rw [if_pos]
                  . assumption
                  . simpa [BitVec.lt_def]
                . rw [if_neg]
                  . assumption
                  . simpa [BitVec.lt_def]
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega

      . intro h_imm
        have imm_spec := Lt.ValidRows.spec_base_ALU_imm
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_assumptions row (by omega))
          (h_bus_wellformedness row (by omega))
          h_imm

        split_ands

        . intro h_opcode
          simp [SltiOutput_matches_Lt_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            skip; skip; skip ]
          . clear *- h_imm_op_properties h_imm
            simp [h_imm] at h_imm_op_properties
            have := @BitVec.toInt_signExtend 12 24 (BitVec.ofNat 12 ↑(air.adapter.rs2 row 0))
            apply BitVec.eq_of_toInt_eq
            simp [this]
            have := h_imm_op_properties.2.1
            rewrite [this]
            exact Int.bmod_eq_of_le (by grind) (by grind)
          . simp [SltiInput_of_Lt_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_slti_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [SltiInput_of_Lt_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_slti_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; skip; skip ]
              . unfold execute_ITYPE_pure at imm_spec
                simp [h_opcode, Lt.ValidRows.iop_of_Lt_opcode, execute_RTYPE_pure] at imm_spec
                split_ifs at imm_spec with h_lt <;> simp at imm_spec h_lt
                . rw [if_pos]
                  . assumption
                  . simpa [BitVec.slt]
                . rw [if_neg]
                  . assumption
                  . simpa [BitVec.slt]
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega

        . intro h_opcode
          simp [SltiuOutput_matches_Lt_instruction_fields]
          split_ands <;>
          [ assumption; assumption; assumption; assumption;
            skip; skip; skip ]
          . clear *- h_imm_op_properties h_imm
            simp [h_imm] at h_imm_op_properties
            have := @BitVec.toInt_signExtend 12 24 (BitVec.ofNat 12 ↑(air.adapter.rs2 row 0))
            apply BitVec.eq_of_toInt_eq
            simp [this]
            have := h_imm_op_properties.2.1
            rewrite [this]
            exact Int.bmod_eq_of_le (by grind) (by grind)
          . simp [SltiuInput_of_Lt_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_sltiu_pure]
            simp [← BitVec.toNat_inj]
            omega
          . simp [SltiuInput_of_Lt_instruction_fields, BabyBear.toBV32, PureSpec.execute_ITYPE_sltiu_pure]
            rewrite [dite_cond_eq_false]
            . simp
              split_ands <;>
              [ assumption; skip; skip ]
              . unfold execute_ITYPE_pure at imm_spec
                simp [h_opcode, Lt.ValidRows.iop_of_Lt_opcode, execute_RTYPE_pure] at imm_spec
                split_ifs at imm_spec with h_lt <;> simp at imm_spec h_lt
                . rw [if_pos]
                  . assumption
                  . simpa [BitVec.lt_def]
                . rw [if_neg]
                  . assumption
                  . simpa [BitVec.lt_def]
              . simp [wrap_to_regidx]
                specialize h_bus_wellformedness row (by omega)
                simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
                      Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
                omega
            . simp [wrap_to_regidx]
              specialize h_bus_wellformedness row (by omega)
              simp [VmAirWrapper_lt_constraint_and_interaction_simplification,
                    Interaction.ReadInstructionBusEntry.operand_properties] at h_bus_wellformedness
              omega

end Equivalence.Lt
