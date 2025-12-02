import OpenvmFv.Spec.BranchEqual

import OpenvmFv.Spec.ControlFlow.beq
import OpenvmFv.Spec.ControlFlow.bne

set_option maxHeartbeats 1_000_000_000

namespace Equivalence.BranchEqual

  structure BranchEqual_instruction_fields where
    is_valid : FBB

    pc : FBB
    next_pc : FBB

    opcode : FBB

    prev_a_timestamp : FBB
    a_timestamp : FBB
    prev_b_timestamp : FBB
    b_timestamp : FBB
    timestamp : FBB
    next_timestamp : FBB

    rs1_ptr : FBB
    rs2_ptr : FBB
    imm : FBB

    a : Vector FBB 4
    b : Vector FBB 4

    misa : BitVec 32

    range_checked_vals : Vector FBB 4

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val % 32, by grind⟩

  def BeqInput_of_BranchEqual_instruction_fields (row : BranchEqual_instruction_fields) : PureSpec.BeqInput := {
    r1_val := BabyBear.toBV32 row.a
    r2_val := BabyBear.toBV32 row.b
    imm := BitVec.ofInt 13 (BabyBear.toInt row.imm)
    PC := row.pc.toNat
    misa := row.misa
    : PureSpec.BeqInput
  }

  def BneInput_of_BranchEqual_instruction_fields (row : BranchEqual_instruction_fields) : PureSpec.BneInput := {
    r1_val := BabyBear.toBV32 row.a
    r2_val := BabyBear.toBV32 row.b
    imm := BitVec.ofInt 13 (BabyBear.toInt row.imm)
    PC := row.pc.toNat
    misa := row.misa
    : PureSpec.BneInput
  }

  def BeqOutput_matches_BranchEqual_instruction_fields (row : BranchEqual_instruction_fields) (beq_output : PureSpec.BeqOutput) : Prop :=
    BabyBear.isU32 row.a ∧
    BabyBear.isU32 row.b ∧
    beq_output.nextPC = row.next_pc.toNat ∧
    beq_output.success = true

  def BneOutput_matches_BranchEqual_instruction_fields (row : BranchEqual_instruction_fields) (bne_output : PureSpec.BneOutput) : Prop :=
    BabyBear.isU32 row.a ∧
    BabyBear.isU32 row.b ∧
    bne_output.nextPC = row.next_pc.toNat ∧
    bne_output.success = true

  def BranchEqual_instruction_fields.spec (row : BranchEqual_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode ∈ Finset.Icc 544 545 ∧
      (row.opcode = 544 →
        BeqOutput_matches_BranchEqual_instruction_fields
          row
          (PureSpec.execute_BEQ_pure (BeqInput_of_BranchEqual_instruction_fields row))
      ) ∧
      (row.opcode = 545 →
        BneOutput_matches_BranchEqual_instruction_fields
          row
          (PureSpec.execute_BNE_pure (BneInput_of_BranchEqual_instruction_fields row))
      )
    )

  def BranchEqual_instruction_fields.execution (row : BranchEqual_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def BranchEqual_instruction_fields.memory (row : BranchEqual_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.prev_a_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.a_timestamp]),
    (-row.is_valid, [1, row.rs2_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.prev_b_timestamp]),
    ( row.is_valid, [1, row.rs2_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.b_timestamp]),
  ]

  def BranchEqual_instruction_fields.range_checks (row : BranchEqual_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
    (row.is_valid, [row.range_checked_vals[2], 17]),
    (row.is_valid, [row.range_checked_vals[3], 12]),
  ]

  def BranchEqual_instruction_fields.read_instruction (row : BranchEqual_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rs1_ptr, row.rs2_ptr, row.imm, 1, 1, 0, 0])
  ]

  def bus_from_instruction_fields (rows : List BranchEqual_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then            rows.flatMap BranchEqual_instruction_fields.execution
      else if index = MemoryBus then          rows.flatMap BranchEqual_instruction_fields.memory
      else if index = RangeCheckerBus then    rows.flatMap BranchEqual_instruction_fields.range_checks
      else if index = ProgramBus then rows.flatMap BranchEqual_instruction_fields.read_instruction
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_branch_eq FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_branch_eq.constraints.allHold air row.1 (by grind)

  def get_instruction_fields [Field ExtF] (air : Valid_VmAirWrapper_branch_eq FBB ExtF) : List BranchEqual_instruction_fields :=
    (List.range (air.last_row + 1)).map (λ row => {
      is_valid := air.core.is_valid row 0
      pc := air.adapter.from_state.pc row 0
      next_pc := air.to_pc row 0
      opcode := air.core.expected_opcode row 0
      prev_a_timestamp := air.adapter.reads_aux_0.base.prev_timestamp row 0
      a_timestamp := air.adapter.from_state.timestamp row 0
      prev_b_timestamp := air.adapter.reads_aux_1.base.prev_timestamp row 0
      b_timestamp := air.adapter.from_state.timestamp row 0 + 1
      timestamp := air.adapter.from_state.timestamp row 0
      next_timestamp := air.adapter.from_state.timestamp row 0 + 2
      rs1_ptr := air.adapter.rs1_ptr row 0
      rs2_ptr := air.adapter.rs2_ptr row 0
      imm := air.core.imm row 0
      a := #v[air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0]
      b := #v[air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0]
      range_checked_vals :=
        #v[air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0,
           air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0,
           air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0,
           air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0,]
      misa := LeanRV32D.Functions.misa
      : BranchEqual_instruction_fields
    })

  set_option maxRecDepth 1_000_000 in
  theorem branch_eq_spec [Field ExtF]
    (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_branch_eq.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_branch_eq.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List BranchEqual_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall BranchEqual_instruction_fields.spec
  := by
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl

    have h_interactions := VmAirWrapper_branch_eq.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold allHold_allRows at h_constraints
    use get_instruction_fields air
    split_ands
    . unfold VmAirWrapper_branch_eq.constraints.constrain_interactions at h_interactions
      rewrite [h_interactions]; clear h_interactions
      unfold bus_from_instruction_fields BranchEqual_instruction_fields.execution BranchEqual_instruction_fields.memory BranchEqual_instruction_fields.range_checks BranchEqual_instruction_fields.read_instruction
      simp [
        get_instruction_fields,
        VmAirWrapper_branch_eq_constraint_and_interaction_simplification
      ]
      unfold VmAirWrapper_branch_eq.constraints.executionBus_row
      unfold VmAirWrapper_branch_eq.constraints.memoryBus_row
      unfold VmAirWrapper_branch_eq.constraints.rangeCheckerBus_row
      unfold VmAirWrapper_branch_eq.constraints.programBus_row
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
      by_cases h_index: index = ProgramBus
      . simp [h_index, List.flatMap_map, ← BranchEqualCoreAir_4.expected_opcode_def]
      . simp [*]
    . apply List.forall_iff_forall_mem.mpr
      intro instruction_fields h_instruction_fields
      unfold BranchEqual_instruction_fields.spec
      simp [get_instruction_fields] at h_instruction_fields
      obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
      rewrite [←h_fields]; clear h_fields
      simp

      intro h_is_valid

      have ⟨
        h_pc, h_pc_mod_4, h_next_pc, h_next_pc_mod_4,
        ⟨h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3⟩,
        h_opcodes,
        imm_range
      ⟩ := BranchEqual.ValidRows.essentials
            ExtF
            air
            row
            (by omega)
            (h_constraints ⟨row, by omega⟩)
            h_is_valid
            (h_bus_axioms row (by omega))
            (h_bus_wellformedness row (by omega))

      split_ands
      . grind
      . grind

      all_goals
        have ⟨ spec_beq, spec_bne ⟩
        := BranchEqual.ValidRows.spec_BEQ_BNE_pc
            ExtF
            air
            row
            (by omega)
            (h_constraints ⟨row, by omega⟩)
            h_is_valid
            (h_bus_axioms row (by omega))
            (h_bus_wellformedness row (by omega))

      . clear spec_bne
        intro h_beq; simp [h_beq] at spec_beq

        split_ifs at spec_beq with h_eq

        . simp [BeqOutput_matches_BranchEqual_instruction_fields,
                BeqInput_of_BranchEqual_instruction_fields]
          simp [PureSpec.execute_BEQ_pure]
          rewrite [ite_cond_eq_false]
          . clear h_constraints h_bus_axioms h_bus_wellformedness
            split_ands
            . exact h_a0
            . exact h_a1
            . exact h_a2
            . exact h_a3
            . exact h_b0
            . exact h_b1
            . exact h_b2
            . exact h_b3
            . exact spec_beq.symm
            . right
              rewrite [←spec_beq]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . left
              right
              rewrite [←spec_beq]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
          . clear h_constraints h_bus_axioms h_bus_wellformedness
            simp_all
            split_ands
            . convert h_eq
            . intro h; clear h
              rewrite [←spec_beq]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . intro h; clear h
              rewrite [←spec_beq]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
        . simp [BeqOutput_matches_BranchEqual_instruction_fields,
                BeqInput_of_BranchEqual_instruction_fields]
          simp [PureSpec.execute_BEQ_pure]
          rewrite [ite_cond_eq_true]
          split_ands
          . exact h_a0
          . exact h_a1
          . exact h_a2
          . exact h_a3
          . exact h_b0
          . exact h_b1
          . exact h_b2
          . exact h_b3
          . exact spec_beq.symm
          . left
            convert h_eq
          . left
            left
            convert h_eq
          . apply eq_true
            left
            convert h_eq
      . clear spec_beq
        intro h_bne; simp [h_bne] at spec_bne

        split_ifs at spec_bne with h_ne

        . simp [BneOutput_matches_BranchEqual_instruction_fields,
                BneInput_of_BranchEqual_instruction_fields]
          simp [PureSpec.execute_BNE_pure]
          rewrite [ite_cond_eq_true]
          split_ands
          . exact h_a0
          . exact h_a1
          . exact h_a2
          . exact h_a3
          . exact h_b0
          . exact h_b1
          . exact h_b2
          . exact h_b3
          . exact spec_bne.symm
          . left
            convert h_ne
          . left
            left
            convert h_ne
          . apply eq_true
            left
            convert h_ne

        . simp [BneOutput_matches_BranchEqual_instruction_fields,
                BneInput_of_BranchEqual_instruction_fields]
          simp [PureSpec.execute_BNE_pure]
          rewrite [ite_cond_eq_false]
          . clear h_constraints h_bus_axioms h_bus_wellformedness
            split_ands
            . exact h_a0
            . exact h_a1
            . exact h_a2
            . exact h_a3
            . exact h_b0
            . exact h_b1
            . exact h_b2
            . exact h_b3
            . exact spec_bne.symm
            . right
              rewrite [←spec_bne]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . left
              right
              rewrite [←spec_bne]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
          . clear h_constraints h_bus_axioms h_bus_wellformedness
            simp_all
            split_ands
            . convert h_ne
            . intro h; clear h
              rewrite [←spec_bne]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . intro h; clear h
              rewrite [←spec_bne]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]

end Equivalence.BranchEqual
