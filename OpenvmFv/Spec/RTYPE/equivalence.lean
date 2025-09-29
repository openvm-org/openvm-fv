import OpenvmFv.Spec.ALU
import OpenvmFv.Spec.RTYPE.add

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

    prev_a : Fin 4 → FBB
    a : Fin 4 → FBB
    b : Fin 4 → FBB
    c : Fin 4 → FBB

    range_checked_vals : Fin 6 → FBB
    bitwise_vals : Fin 5 → Fin 3 → FBB

  def wrap_to_word (vals : Fin 4 → FBB) : BitVec 32 :=
    (@BabyBear.toU32
      (vals 0 % 256)
      (vals 1 % 256)
      (vals 2 % 256)
      (vals 3 % 256)
      (by grind)).toBV

  def is_normalized_word (vals : Fin 4 → FBB) : Prop :=
    BabyBear.isU32
      (vals 0)
      (vals 1)
      (vals 2)
      (vals 3)

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val % 32, by grind⟩

  def AddInput_of_ALU_instruction_fields (row : ALU_instruction_fields) : PureSpec.AddInput := {
    r1_val := wrap_to_word row.b
    r2_val := wrap_to_word row.c
    rd := wrap_to_regidx row.rd_ptr
    PC := row.pc.toNat
    : PureSpec.AddInput
  }

  def AddOutput_matches_ALU_instruction_fields (row : ALU_instruction_fields) (add_output : PureSpec.AddOutput) : Prop :=
    is_normalized_word row.b ∧
    is_normalized_word row.c ∧
    add_output.nextPC = row.next_pc.toNat ∧
    match add_output.rd with
      | .none => row.a = row.prev_a
      | .some (rd, rd_val) =>
        is_normalized_word row.a ∧
        wrap_to_word row.a = rd_val ∧
        rd.1.toNat = row.rd_ptr.toNat

  def ALU_instruction_fields.spec (row : ALU_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode ∈ Finset.Icc 512 516 ∧
      ((row.opcode = 512 ∧ row.non_imm = 1) → (
        AddOutput_matches_ALU_instruction_fields
          row
          (PureSpec.execute_RTYPE_add_pure (AddInput_of_ALU_instruction_fields row))
      ))
    )

  def ALU_instruction_fields.execution (row : ALU_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def ALU_instruction_fields.memory (row : ALU_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.b 0, row.b 1, row.b 2, row.b 3, row.prev_b_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.b 0, row.b 1, row.b 2, row.b 3, row.b_timestamp]),
    (-row.non_imm, [row.non_imm, row.rs2_ptr, row.c 0, row.c 1, row.c 2, row.c 3, row.prev_c_timestamp]),
    ( row.non_imm, [row.non_imm, row.rs2_ptr, row.c 0, row.c 1, row.c 2, row.c 3, row.c_timestamp]),
    (-row.is_valid, [1, row.rd_ptr, row.prev_a 0, row.prev_a 1, row.prev_a 2, row.prev_a 3, row.prev_a_timestamp]),
    ( row.is_valid, [1, row.rd_ptr, row.a 0, row.a 1, row.a 2, row.a 3, row.a_timestamp]),
  ]

  def ALU_instruction_fields.range_checks (row : ALU_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals 0, 17]),
    (row.is_valid, [row.range_checked_vals 1, 12]),
    (row.non_imm, [row.range_checked_vals 2, 17]),
    (row.non_imm, [row.range_checked_vals 3, 12]),
    (row.is_valid, [row.range_checked_vals 4, 17]),
    (row.is_valid, [row.range_checked_vals 5, 12]),
  ]

  def ALU_instruction_fields.read_instruction (row : ALU_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rd_ptr, row.rs1_ptr, row.rs2_ptr, 1, row.non_imm, 0, 0])
  ]

  def ALU_instruction_fields.bitwise (row : ALU_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.bitwise_vals 0 0, row.bitwise_vals 0 1, row.bitwise_vals 0 2, 1]),
    (row.is_valid, [row.bitwise_vals 1 0, row.bitwise_vals 1 1, row.bitwise_vals 1 2, 1]),
    (row.is_valid, [row.bitwise_vals 2 0, row.bitwise_vals 2 1, row.bitwise_vals 2 2, 1]),
    (row.is_valid, [row.bitwise_vals 3 0, row.bitwise_vals 3 1, row.bitwise_vals 3 2, 1]),
    (row.is_valid - row.non_imm, [row.bitwise_vals 4 0, row.bitwise_vals 4 1, row.bitwise_vals 4 2, 0]),
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
      prev_a := λ idx => match idx with
        | 0 => air.adapter.writes_aux.prev_data_0 row 0
        | 1 => air.adapter.writes_aux.prev_data_1 row 0
        | 2 => air.adapter.writes_aux.prev_data_2 row 0
        | 3 => air.adapter.writes_aux.prev_data_3 row 0
      a := λ idx => match idx with
        | 0 => air.core.a_0 row 0
        | 1 => air.core.a_1 row 0
        | 2 => air.core.a_2 row 0
        | 3 => air.core.a_3 row 0
      b := λ idx => match idx with
        | 0 => air.core.b_0 row 0
        | 1 => air.core.b_1 row 0
        | 2 => air.core.b_2 row 0
        | 3 => air.core.b_3 row 0
      c := λ idx => match idx with
        | 0 => air.core.c_0 row 0
        | 1 => air.core.c_1 row 0
        | 2 => air.core.c_2 row 0
        | 3 => air.core.c_3 row 0
      range_checked_vals := λ idx => match idx with
        | 0 => air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0
        | 1 => air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0
        | 2 => air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0
        | 3 => air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0
        | 4 => air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0
        | 5 => air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0
      bitwise_vals := λ x y => match (x, y) with
        | (0, 0) => air.core.x_0 row 0
        | (0, 1) => air.core.y_0 row 0
        | (0, 2) => air.core.x_xor_y_0 row 0
        | (1, 0) => air.core.x_1 row 0
        | (1, 1) => air.core.y_1 row 0
        | (1, 2) => air.core.x_xor_y_1 row 0
        | (2, 0) => air.core.x_2 row 0
        | (2, 1) => air.core.y_2 row 0
        | (2, 2) => air.core.x_xor_y_2 row 0
        | (3, 0) => air.core.x_3 row 0
        | (3, 1) => air.core.y_3 row 0
        | (3, 2) => air.core.x_xor_y_3 row 0
        | (4, 0) => air.core.c_0 row 0
        | (4, 1) => air.core.c_1 row 0
        | (4, 2) => 0
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

      have non_imm_spec := ALU.ValidRows.spec_base_ALU_non_imm
        ExtF
        air
        row
        (by omega)
        (h_constraints ⟨row, by omega⟩)
        h_is_valid
        (h_bus_wellformedness row (by omega))

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

      dsimp only at *

      split_ands
      . grind
      . grind
      . intro h_opcode h_non_imm
        simp [AddOutput_matches_ALU_instruction_fields]
        split_ands
        . assumption
        . assumption
        . assumption
        . assumption
        . assumption
        . assumption
        . assumption
        . assumption
        . simp [AddInput_of_ALU_instruction_fields, wrap_to_word, PureSpec.execute_RTYPE_add_pure]
          simp [← BitVec.toNat_inj]
          omega
        . simp [AddInput_of_ALU_instruction_fields, wrap_to_word, PureSpec.execute_RTYPE_add_pure]
          rewrite [dite_cond_eq_false]
          . simp
            split_ands
            . assumption
            . assumption
            . assumption
            . assumption
            . specialize non_imm_spec h_non_imm
              unfold execute_RTYPE_pure at non_imm_spec
              simp only [h_opcode, ALU.ValidRows.rop_of_ALU_opcode] at non_imm_spec
              dsimp at non_imm_spec
              simp [← BitVec.toNat_inj, U32.toNat] at non_imm_spec ⊢
              omega
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
