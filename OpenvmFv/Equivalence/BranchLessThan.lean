import OpenvmFv.RV32D.blt
import OpenvmFv.RV32D.bltu
import OpenvmFv.RV32D.bge
import OpenvmFv.RV32D.bgeu

import OpenvmFv.Spec.BranchLessThan

set_option maxHeartbeats 1_000_000_000

namespace Equivalence.BranchLessThan

  structure BranchLessThan_instruction_fields where
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

    prefix_sum : FBB

    range_checked_vals : Vector FBB 4
    bitwise_vals : Vector (Vector FBB 3) 2

  def wrap_to_regidx (val : FBB) : Fin 32 :=
    ⟨val % 32, by grind⟩

  def BltInput_of_BranchLessThan_instruction_fields (row : BranchLessThan_instruction_fields) : PureSpec.BltInput := {
    r1_val := BabyBear.toBV32 row.a
    r2_val := BabyBear.toBV32 row.b
    imm := BitVec.ofInt 13 (BabyBear.toInt row.imm)
    PC := row.pc.toNat
    : PureSpec.BltInput
  }

  def BltuInput_of_BranchLessThan_instruction_fields (row : BranchLessThan_instruction_fields) : PureSpec.BltuInput := {
    r1_val := BabyBear.toBV32 row.a
    r2_val := BabyBear.toBV32 row.b
    imm := BitVec.ofInt 13 (BabyBear.toInt row.imm)
    PC := row.pc.toNat
    : PureSpec.BltuInput
  }

  def BgeInput_of_BranchLessThan_instruction_fields (row : BranchLessThan_instruction_fields) : PureSpec.BgeInput := {
    r1_val := BabyBear.toBV32 row.a
    r2_val := BabyBear.toBV32 row.b
    imm := BitVec.ofInt 13 (BabyBear.toInt row.imm)
    PC := row.pc.toNat
    : PureSpec.BgeInput
  }

  def BgeuInput_of_BranchLessThan_instruction_fields (row : BranchLessThan_instruction_fields) : PureSpec.BgeuInput := {
    r1_val := BabyBear.toBV32 row.a
    r2_val := BabyBear.toBV32 row.b
    imm := BitVec.ofInt 13 (BabyBear.toInt row.imm)
    PC := row.pc.toNat
    : PureSpec.BgeuInput
  }

  def BltOutput_matches_BranchLessThan_instruction_fields (row : BranchLessThan_instruction_fields) (blt_output : PureSpec.BltOutput) : Prop :=
    BabyBear.isU32 row.a ∧
    BabyBear.isU32 row.b ∧
    blt_output.nextPC = row.next_pc.toNat ∧
    blt_output.success = true

  def BltuOutput_matches_BranchLessThan_instruction_fields (row : BranchLessThan_instruction_fields) (bltu_output : PureSpec.BltuOutput) : Prop :=
    BabyBear.isU32 row.a ∧
    BabyBear.isU32 row.b ∧
    bltu_output.nextPC = row.next_pc.toNat ∧
    bltu_output.success = true

  def BgeOutput_matches_BranchLessThan_instruction_fields (row : BranchLessThan_instruction_fields) (bge_output : PureSpec.BgeOutput) : Prop :=
    BabyBear.isU32 row.a ∧
    BabyBear.isU32 row.b ∧
    bge_output.nextPC = row.next_pc.toNat ∧
    bge_output.success = true

  def BgeuOutput_matches_BranchLessThan_instruction_fields (row : BranchLessThan_instruction_fields) (bgeu_output : PureSpec.BgeuOutput) : Prop :=
    BabyBear.isU32 row.a ∧
    BabyBear.isU32 row.b ∧
    bgeu_output.nextPC = row.next_pc.toNat ∧
    bgeu_output.success = true

  def BranchLessThan_instruction_fields.spec (row : BranchLessThan_instruction_fields) : Prop :=
    row.is_valid = 1 → (
      row.opcode ∈ Finset.Icc 549 552 ∧
      (row.opcode = 549 →
        BltOutput_matches_BranchLessThan_instruction_fields
          row
          (PureSpec.execute_BLT_pure (BltInput_of_BranchLessThan_instruction_fields row))
      ) ∧
      (row.opcode = 550 →
        BltuOutput_matches_BranchLessThan_instruction_fields
          row
          (PureSpec.execute_BLTU_pure (BltuInput_of_BranchLessThan_instruction_fields row))
      ) ∧
      (row.opcode = 551 →
        BgeOutput_matches_BranchLessThan_instruction_fields
          row
          (PureSpec.execute_BGE_pure (BgeInput_of_BranchLessThan_instruction_fields row))
      ) ∧
      (row.opcode = 552 →
        BgeuOutput_matches_BranchLessThan_instruction_fields
          row
          (PureSpec.execute_BGEU_pure (BgeuInput_of_BranchLessThan_instruction_fields row))
      )
    )

  def BranchLessThan_instruction_fields.execution (row : BranchLessThan_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [row.pc, row.timestamp]),
    (row.is_valid, [row.next_pc, row.next_timestamp])
  ]

  def BranchLessThan_instruction_fields.memory (row : BranchLessThan_instruction_fields) : List (FBB × List FBB) := [
    (-row.is_valid, [1, row.rs1_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.prev_a_timestamp]),
    ( row.is_valid, [1, row.rs1_ptr, row.a[0], row.a[1], row.a[2], row.a[3], row.a_timestamp]),
    (-row.is_valid, [1, row.rs2_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.prev_b_timestamp]),
    ( row.is_valid, [1, row.rs2_ptr, row.b[0], row.b[1], row.b[2], row.b[3], row.b_timestamp]),
  ]

  def BranchLessThan_instruction_fields.range_checks (row : BranchLessThan_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.range_checked_vals[0], 17]),
    (row.is_valid, [row.range_checked_vals[1], 12]),
    (row.is_valid, [row.range_checked_vals[2], 17]),
    (row.is_valid, [row.range_checked_vals[3], 12]),
  ]

  def BranchLessThan_instruction_fields.read_instruction (row : BranchLessThan_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.pc, row.opcode, row.rs1_ptr, row.rs2_ptr, row.imm, 1, 1, 0, 0])
  ]

  def BranchLessThan_instruction_fields.bitwise (row : BranchLessThan_instruction_fields) : List (FBB × List FBB) := [
    (row.is_valid, [row.bitwise_vals[0][0], row.bitwise_vals[0][1], row.bitwise_vals[0][2], 0]),
    (row.prefix_sum, [row.bitwise_vals[1][0], row.bitwise_vals[1][1], row.bitwise_vals[1][2], 0])
  ]

  def bus_from_instruction_fields (rows : List BranchLessThan_instruction_fields) : ℕ → List (FBB × List FBB) :=
    λ index =>
      if index = ExecutionBus then            rows.flatMap BranchLessThan_instruction_fields.execution
      else if index = MemoryBus then          rows.flatMap BranchLessThan_instruction_fields.memory
      else if index = RangeCheckerBus then    rows.flatMap BranchLessThan_instruction_fields.range_checks
      else if index = ProgramBus then rows.flatMap BranchLessThan_instruction_fields.read_instruction
      else if index = BitwiseBus then         rows.flatMap BranchLessThan_instruction_fields.bitwise
      else []

  def allHold_allRows [Field ExtF] (air : Valid_VmAirWrapper_branch_lt FBB ExtF) : Prop :=
    ∀ row : (Fin (air.last_row + 1)), VmAirWrapper_branch_lt.constraints.allHold air row.1 (by grind)

  def get_instruction_fields [Field ExtF] (air : Valid_VmAirWrapper_branch_lt FBB ExtF) : List BranchLessThan_instruction_fields :=
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
      prefix_sum := air.core.prefix_sum row 0 0
      range_checked_vals :=
        #v[air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0,
           air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0,
           air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0,
           air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0,]
      bitwise_vals :=
        #v[
            #v[air.core.a_msb_f row 0 + 128 * (air.core.opcode_blt_flag row 0 + air.core.opcode_bge_flag row 0),
               air.core.b_msb_f row 0 + 128 * (air.core.opcode_blt_flag row 0 + air.core.opcode_bge_flag row 0),
               0],
            #v[air.core.diff_val row 0 - 1, 0, 0]
        ]
      : BranchLessThan_instruction_fields
    })

  set_option maxRecDepth 1_000_000 in
  theorem branch_lt_spec [Field ExtF]
    (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
    (h_constraints : allHold_allRows air)
    (h_bus_axioms : ∀ row ≤ air.last_row, VmAirWrapper_branch_lt.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : ∀ row ≤ air.last_row, VmAirWrapper_branch_lt.constraints.wf_propertiesToAssumePerRow air row)
  :
    ∃ instruction_fields_list : List BranchLessThan_instruction_fields,
      air.buses = bus_from_instruction_fields instruction_fields_list ∧
      instruction_fields_list.Forall BranchLessThan_instruction_fields.spec
  := by
    have h_neg_one : (2013265920 : FBB) = (-1 : FBB) := rfl

    have h_interactions := VmAirWrapper_branch_lt.constraints.constrain_interactions_of_extraction air (h_constraints 0).1
    unfold allHold_allRows at h_constraints
    use get_instruction_fields air
    split_ands
    . unfold VmAirWrapper_branch_lt.constraints.constrain_interactions at h_interactions
      rewrite [h_interactions]; clear h_interactions
      unfold bus_from_instruction_fields BranchLessThan_instruction_fields.execution BranchLessThan_instruction_fields.memory BranchLessThan_instruction_fields.range_checks BranchLessThan_instruction_fields.read_instruction
      simp [
        get_instruction_fields,
        VmAirWrapper_branch_lt_constraint_and_interaction_simplification
      ]
      unfold VmAirWrapper_branch_lt.constraints.executionBus_row
      unfold VmAirWrapper_branch_lt.constraints.memoryBus_row
      unfold VmAirWrapper_branch_lt.constraints.rangeCheckerBus_row
      unfold VmAirWrapper_branch_lt.constraints.programBus_row
      unfold VmAirWrapper_branch_lt.constraints.bitwiseBus_row
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
      . simp [h_index, List.flatMap_map, ← BranchLessThanCoreAir_4_8.expected_opcode_def]
      by_cases h_index: index = BitwiseBus
      . simp [h_index, List.flatMap_map, BranchLessThan_instruction_fields.bitwise]
      . simp [*]
    . apply List.forall_iff_forall_mem.mpr
      intro instruction_fields h_instruction_fields
      unfold BranchLessThan_instruction_fields.spec
      simp [get_instruction_fields] at h_instruction_fields
      obtain ⟨row, ⟨h_row_range, h_fields⟩⟩ := h_instruction_fields
      rewrite [←h_fields]; clear h_fields
      simp

      intro h_is_valid

      have ⟨
        h_pc, h_pc_mod_4,
        h_next_pc, h_next_pc_mod_4,
        ⟨h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3⟩,
        h_opcodes,
        imm_range
      ⟩ := BranchLessThan.ValidRows.essentials
            ExtF
            air
            row
            (by omega)
            (h_constraints ⟨row, by omega⟩)
            h_is_valid
            (h_bus_axioms row (by omega))
            (h_bus_wellformedness row (by omega))

      have ⟨ spec_blt, spec_bltu, spec_bge, spec_bgeu ⟩
      := BranchLessThan.ValidRows.spec_BLT_BLTU_BGE_BGEU_pc
          ExtF
          air
          row
          (by omega)
          (h_constraints ⟨row, by omega⟩)
          h_is_valid
          (h_bus_axioms row (by omega))
          (h_bus_wellformedness row (by omega))

      split_ands <;> [
        grind;
        grind;
        skip; skip; skip; skip
      ]

      . clear spec_bltu spec_bge spec_bgeu h_constraints h_bus_axioms h_bus_wellformedness
        intro h_blt; simp [h_blt] at spec_blt

        split_ifs at spec_blt with h_lt
        . simp [
            BltOutput_matches_BranchLessThan_instruction_fields,
            BltInput_of_BranchLessThan_instruction_fields
          ]
          simp [PureSpec.execute_BLT_pure]
          rewrite [ite_cond_eq_false]
          . split_ands
            . exact h_a0
            . exact h_a1
            . exact h_a2
            . exact h_a3
            . exact h_b0
            . exact h_b1
            . exact h_b2
            . exact h_b3
            . exact spec_blt.symm
            . right
              rewrite [←spec_blt]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . right
              rewrite [←spec_blt]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
          . simp_all
            split_ands
            . convert h_lt
            . intro h; clear h
              rewrite [←spec_blt]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . intro h; clear h
              rewrite [←spec_blt]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
        . simp [BltOutput_matches_BranchLessThan_instruction_fields,
                BltInput_of_BranchLessThan_instruction_fields]
          simp [PureSpec.execute_BLT_pure]
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
          . exact spec_blt.symm
          . left
            apply le_of_not_gt
            convert h_lt
          . left
            apply le_of_not_gt
            convert h_lt
          . apply eq_true
            left
            apply le_of_not_gt
            convert h_lt

      . clear spec_blt spec_bge spec_bgeu
        intro h_bltu; simp [h_bltu] at spec_bltu

        split_ifs at spec_bltu with h_ltu
        . simp [
            BltuOutput_matches_BranchLessThan_instruction_fields,
            BltuInput_of_BranchLessThan_instruction_fields
          ]
          simp [PureSpec.execute_BLTU_pure]
          rewrite [ite_cond_eq_false]
          . split_ands
            . exact h_a0
            . exact h_a1
            . exact h_a2
            . exact h_a3
            . exact h_b0
            . exact h_b1
            . exact h_b2
            . exact h_b3
            . exact spec_bltu.symm
            . right
              rewrite [←spec_bltu]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . right
              rewrite [←spec_bltu]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
          . simp_all
            split_ands
            . convert h_ltu
            . intro h; clear h
              rewrite [←spec_bltu]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . intro h; clear h
              rewrite [←spec_bltu]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
        . simp [BltuOutput_matches_BranchLessThan_instruction_fields,
                BltuInput_of_BranchLessThan_instruction_fields]
          simp [PureSpec.execute_BLTU_pure]
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
          . exact spec_bltu.symm
          . left
            apply le_of_not_gt
            convert h_ltu
          . left
            apply le_of_not_gt
            convert h_ltu
          . apply eq_true
            left
            apply le_of_not_gt
            convert h_ltu

      . clear spec_blt spec_bltu spec_bgeu
        intro h_bge; simp [h_bge] at spec_bge

        split_ifs at spec_bge with h_ge
        . simp [
            BgeOutput_matches_BranchLessThan_instruction_fields,
            BgeInput_of_BranchLessThan_instruction_fields
          ]
          simp [PureSpec.execute_BGE_pure]
          rewrite [ite_cond_eq_false]
          . split_ands
            . exact h_a0
            . exact h_a1
            . exact h_a2
            . exact h_a3
            . exact h_b0
            . exact h_b1
            . exact h_b2
            . exact h_b3
            . exact spec_bge.symm
            . right
              rewrite [←spec_bge]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . right
              rewrite [←spec_bge]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
          . simp_all
            split_ands
            . convert h_ge
            . intro h; clear h
              rewrite [←spec_bge]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . intro h; clear h
              rewrite [←spec_bge]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
        . simp [BgeOutput_matches_BranchLessThan_instruction_fields,
                BgeInput_of_BranchLessThan_instruction_fields]
          simp [PureSpec.execute_BGE_pure]
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
          . exact spec_bge.symm
          . left
            apply lt_of_not_ge
            convert h_ge
          . left
            apply lt_of_not_ge
            convert h_ge
          . apply eq_true
            left
            apply lt_of_not_ge
            convert h_ge

      . clear spec_blt spec_bltu spec_bge
        intro h_bgeu; simp [h_bgeu] at spec_bgeu

        split_ifs at spec_bgeu with h_geu
        . simp [
            BgeuOutput_matches_BranchLessThan_instruction_fields,
            BgeuInput_of_BranchLessThan_instruction_fields
          ]
          simp [PureSpec.execute_BGEU_pure]
          rewrite [ite_cond_eq_false]
          . split_ands
            . exact h_a0
            . exact h_a1
            . exact h_a2
            . exact h_a3
            . exact h_b0
            . exact h_b1
            . exact h_b2
            . exact h_b3
            . exact spec_bgeu.symm
            . right
              rewrite [←spec_bgeu]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . right
              rewrite [←spec_bgeu]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
          . simp_all
            split_ands
            . convert h_geu
            . intro h; clear h
              rewrite [←spec_bgeu]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              have : (air.to_pc row 0).val % 2 = 0 := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                omega
              simp [this]
            . intro h; clear h
              rewrite [←spec_bgeu]
              simp [BitVec.ofBool, BitVec.getElem_eq_testBit_toNat]
              rewrite [Nat.mod_eq_of_lt (by omega)]
              have : (air.to_pc row 0).val.testBit 1 = false := by
                simp [Fin.mod_def] at h_next_pc_mod_4
                clear *-h_next_pc_mod_4
                grind
              simp [this]
        . simp [BgeuOutput_matches_BranchLessThan_instruction_fields,
                BgeuInput_of_BranchLessThan_instruction_fields]
          simp [PureSpec.execute_BGEU_pure]
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
          . exact spec_bgeu.symm
          . left
            apply lt_of_not_ge
            convert h_geu
          . left
            apply lt_of_not_ge
            convert h_geu
          . apply eq_true
            left
            apply lt_of_not_ge
            convert h_geu

end Equivalence.BranchLessThan
