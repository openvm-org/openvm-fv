import OpenvmFv.Airs.Branch.VmAirWrapper_branch_eq
import OpenvmFv.Extraction.VmAirWrapper_branch_eq
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace VmAirWrapper_branch_eq.constraints

  section constraint_simplification

    -- Note: `air` and `row` are not included as section variables
    --       so that the file can still be used with `sorry`
    --       during the extraction process
    --       Additionally, the proofs are split into more stages
    --       than required so that it can be easily checked that all
    --       intending folding is occuring

    variable [Field F] [Field ExtF]

    section row_constraints

      -- constraints and constraints_of_extraction
      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_beq_flag row 0 = 0 ∨ air.core.opcode_beq_flag row 0 = 1

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_0 air row ↔ constraint_0 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_bne_flag row 0 = 0 ∨ air.core.opcode_bne_flag row 0 = 1

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_1 air row ↔ constraint_1 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_2 air row ↔ constraint_2 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.cmp_result row 0 = 0 ∨ air.core.cmp_result row 0 = 1

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_3 air row ↔ constraint_3 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.cmp_eq row 0 = 0 ∨ air.core.a_0 row 0 = air.core.b_0 row 0

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_4 air row ↔ constraint_4 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.cmp_eq row 0 = 0 ∨ air.core.a_1 row 0 = air.core.b_1 row 0

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_5 air row ↔ constraint_5 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.cmp_eq row 0 = 0 ∨ air.core.a_2 row 0 = air.core.b_2 row 0

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_6 air row ↔ constraint_6 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.cmp_eq row 0 = 0 ∨ air.core.a_3 row 0 = air.core.b_3 row 0

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_7 air row ↔ constraint_7 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.sum row 0 = 1

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_8_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_8 air row ↔ constraint_8 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
        air.adapter.from_state.timestamp row 0 - air.adapter.reads_aux.base.prev_timestamp row 0 - 1 =
          air.adapter.reads_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 +
            air.adapter.reads_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_9_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_9 air row ↔ constraint_9 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
        air.adapter.from_state.timestamp row 0 + 1 - air.adapter.columns 7 row 0 - 1 =
          air.adapter.columns 8 row 0 + air.adapter.columns 9 row 0 * 131072

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constraint_10_of_extraction
          (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ)
      : VmAirWrapper_branch_eq.extraction.constraint_10 air row ↔ constraint_10 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h
        exact h

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      --busRows, constrain_interactions, and constrain_interactions_of_extraction
      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def executionBus_row (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.core.is_valid row 0, [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0]),
        (air.core.is_valid row 0, [air.to_pc row 0, air.adapter.from_state.timestamp row 0 + 2])]

      lemma constrain_execution_interactions
        (air : Valid_VmAirWrapper_branch_eq F ExtF)
        (h : VmAirWrapper_branch_eq.extraction.constrain_interactions air)
      :
        air.buses ExecutionBus = (List.range (air.last_row + 1)).flatMap (λ row => executionBus_row air row)
      := by
        unfold VmAirWrapper_branch_eq.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def memoryBus_row (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : List (F × List F) :=
        [(2013265920 * air.core.is_valid row 0,
          [1, air.adapter.rs1_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0,
            air.adapter.reads_aux.base.prev_timestamp row 0]),
        (air.core.is_valid row 0,
          [1, air.adapter.rs1_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0,
            air.adapter.from_state.timestamp row 0]),
        (2013265920 * air.core.is_valid row 0,
          [1, air.adapter.rs2_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0,
            air.adapter.columns 7 row 0]),
        (air.core.is_valid row 0,
          [1, air.adapter.rs2_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0,
            air.adapter.from_state.timestamp row 0 + 1])]

      lemma constrain_memory_interactions
        (air : Valid_VmAirWrapper_branch_eq F ExtF)
        (h : VmAirWrapper_branch_eq.extraction.constrain_interactions air)
      :
        air.buses MemoryBus = (List.range (air.last_row + 1)).flatMap (λ row => memoryBus_row air row)
      := by
        unfold VmAirWrapper_branch_eq.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def rangeCheckerBus_row (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0, [air.adapter.reads_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.reads_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.core.is_valid row 0, [air.adapter.columns 8 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.columns 9 row 0, 12])]

      lemma constrain_rangeChecker_interactions
        (air : Valid_VmAirWrapper_branch_eq F ExtF)
        (h : VmAirWrapper_branch_eq.extraction.constrain_interactions air)
      :
        air.buses RangeCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeCheckerBus_row air row)
      := by
        unfold VmAirWrapper_branch_eq.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
      def readInstructionBus_row (air : Valid_VmAirWrapper_branch_eq F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
          [air.adapter.from_state.pc row 0, air.core.expected_opcode row 0, air.adapter.rs1_ptr row 0,
            air.adapter.rs2_ptr row 0, air.core.imm row 0, 1, 1, 0, 0])]

      lemma constrain_readInstruction_interactions
        (air : Valid_VmAirWrapper_branch_eq F ExtF)
        (h : VmAirWrapper_branch_eq.extraction.constrain_interactions air)
      :
        air.buses ReadInstructionBus = (List.range (air.last_row + 1)).flatMap (λ row => readInstructionBus_row air row)
      := by
        unfold VmAirWrapper_branch_eq.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      def constrain_interactions (air : Valid_VmAirWrapper_branch_eq F ExtF) : Prop :=
      air.buses = fun index ↦
      if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
      else if index = MemoryBus then (List.range (air.last_row + 1)).flatMap (memoryBus_row air)
      else if index = RangeCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeCheckerBus_row air)
      else if index = ReadInstructionBus then (List.range (air.last_row + 1)).flatMap (readInstructionBus_row air)
      else []

      @[VmAirWrapper_branch_eq_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VmAirWrapper_branch_eq F ExtF)
        (h : VmAirWrapper_branch_eq.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold VmAirWrapper_branch_eq.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        exact h

    end interactions

  end constraint_simplification

  section allHold

    -- constraint list and allHold

    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        VmAirWrapper_branch_eq.extraction.constraint_0 air row,
        VmAirWrapper_branch_eq.extraction.constraint_1 air row,
        VmAirWrapper_branch_eq.extraction.constraint_2 air row,
        VmAirWrapper_branch_eq.extraction.constraint_3 air row,
        VmAirWrapper_branch_eq.extraction.constraint_4 air row,
        VmAirWrapper_branch_eq.extraction.constraint_5 air row,
        VmAirWrapper_branch_eq.extraction.constraint_6 air row,
        VmAirWrapper_branch_eq.extraction.constraint_7 air row,
        VmAirWrapper_branch_eq.extraction.constraint_8 air row,
        VmAirWrapper_branch_eq.extraction.constraint_9 air row,
        VmAirWrapper_branch_eq.extraction.constraint_10 air row,
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      VmAirWrapper_branch_eq.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        constraint_0 air row,
        constraint_1 air row,
        constraint_2 air row,
        constraint_3 air row,
        constraint_4 air row,
        constraint_5 air row,
        constraint_6 air row,
        constraint_7 air row,
        constraint_8 air row,
        constraint_9 air row,
        constraint_10 air row,
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold VmAirWrapper_branch_eq.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  VmAirWrapper_branch_eq_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

    lemma single_op
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
    :
      let is_beq := air.core.opcode_beq_flag row 0
      let is_bne := air.core.opcode_bne_flag row 0
      (is_beq = 1 → is_bne = 0) ∧
      (is_bne = 1 → is_beq = 0)
    := by
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at h0 h1 h2
      rw [Valid_BranchEqualCoreAir_4.is_valid] at h2
      grind

    lemma op_from_opcode
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
      (is_valid : air.core.is_valid row 0 = 1)
    :
      let is_beq := air.core.opcode_beq_flag row 0
      let is_bne := air.core.opcode_bne_flag row 0
      (air.core.expected_opcode row 0 = 544 → is_beq = 1) ∧
      (air.core.expected_opcode row 0 = 545 → is_bne = 1)
    := by
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at *
      rw [Valid_BranchEqualCoreAir_4.is_valid] at is_valid h2
      rw [← BranchEqualCoreAir_4.expected_opcode_def]
      grind

    lemma opcode_bounds
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
      (is_valid : air.core.is_valid row 0 = 1)
    :
      air.core.expected_opcode row 0 = 544 ∨
      air.core.expected_opcode row 0 = 545
    := by
      have ⟨ sop1, sop2 ⟩ := single_op air row valid_row cstrs
      rw [← BranchEqualCoreAir_4.expected_opcode_def]
      rw [Valid_BranchEqualCoreAir_4.is_valid] at is_valid
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_branch_eq_constraint_and_interaction_simplification] at *
      grind

  end properties

  section bus_entries

    lemma executionBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_branch_eq FBB ExtF} {row : ℕ}
      (h_in : entry ∈ executionBus_row air row)
    :
      entry.2.length = Interaction.ExecutionBusEntryInstance.data_length
    := by
      unfold executionBus_row at *; simp_all
      grind

    @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
    def _executionBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.ExecutionBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ executionBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (executionBus_row_length x.2)))
          (executionBus_row air row).attach
      List.map Interaction.ExecutionBusEntryInstance.deserialise vectorised_row

    lemma memoryBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_branch_eq FBB ExtF} {row : ℕ}
      (h_in : entry ∈ memoryBus_row air row)
    :
      entry.2.length = Interaction.MemoryBusEntryInstance.data_length
    := by
      unfold memoryBus_row at *; simp_all
      grind (ematch := 8)

    @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
    def _memoryBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.MemoryBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ memoryBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (memoryBus_row_length x.2)))
          (memoryBus_row air row).attach
      List.map Interaction.MemoryBusEntryInstance.deserialise vectorised_row

    lemma rangeCheckerBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_branch_eq FBB ExtF} {row : ℕ}
      (h_in : entry ∈ rangeCheckerBus_row air row)
    :
      entry.2.length = Interaction.RangeCheckerBusEntryInstance.data_length
    := by
      unfold rangeCheckerBus_row at *; simp_all
      grind

    @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
    def _rangeCheckerBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.RangeCheckerBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ rangeCheckerBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (rangeCheckerBus_row_length x.2)))
          (rangeCheckerBus_row air row).attach
      List.map Interaction.RangeCheckerBusEntryInstance.deserialise vectorised_row

    @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
    def readInstructionBus_properties (entry : Interaction.ReadInstructionBusEntry FBB) : Prop :=
      let imm := entry.xc
      -- imm is a 13-bit signed integer represented as a field element
      (-2^12 ≤ BabyBear.toInt imm) ∧ BabyBear.toInt imm < 2^12 ∧
      -- imm is aligned
      BabyBear.toInt imm % 4 = 0

    lemma toInt_mod_eq_zero_of_bitvec_mod_eq_zero (bv: BitVec 13) (h: bv % 4 = 0):
      bv.toInt % 4 = 0
    := by
      simp at h ⊢
      have : (4: Int) = (4#13).toInt := rfl
      rewrite [this]
      apply BitVec.toInt_dvd_toInt_iff.mpr
      bv_decide

    set_option maxHeartbeats 0 in
    lemma readInstructionBus_properties_of_opcode_bounds (entry : Interaction.ReadInstructionBusEntry FBB)
      (h_bounds :
        entry.opcode = 544 ∨
        entry.opcode = 545
      )
      (h_bus : Interaction.ReadInstructionBusEntry.operand_properties entry)
    :
      readInstructionBus_properties entry
    := by
      simp [readInstructionBus_properties.eq_def]
      simp [Interaction.ReadInstructionBusEntry.operand_properties] at h_bus
      obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus
      simp [←h_data] at h_bounds ⊢ h_transpile
      obtain h_opcode | h_opcode := h_bounds <;> [
        have := Transpiler.transpiler_opcode_544 h_transpile h_opcode;
        have := Transpiler.transpiler_opcode_545 h_transpile h_opcode
      ]
      all_goals {
        obtain ⟨imm, rs2, rs1, h_imm, h_instruction⟩ := this
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        dsimp at h_transpile
        simp [-Vector.mk_eq] at h_transpile
        replace h_transpile := h_transpile.2
        rewrite [←h_transpile]
        simp [Transpiler.itof, BabyBear.toInt]
        split_ands
        . clear *- imm
          rewrite [max_eq_left (by omega)]
          by_cases h_sign : imm.toInt ≥ 0
          . have := @BitVec.toInt_le _ imm
            simp at this
            rewrite [ite_cond_eq_true]
            . omega
            . simp
              omega
          . have := BitVec.le_toInt imm
            simp at this
            rewrite [ite_cond_eq_false]
            . omega
            . simp
              omega
        . clear *- imm
          rewrite [max_eq_left (by omega)]
          by_cases h_sign : imm.toInt ≥ 0
          . have := @BitVec.toInt_le _ imm
            simp at this
            rewrite [ite_cond_eq_true]
            . omega
            . simp
              omega
          . have := BitVec.le_toInt imm
            simp at this
            rewrite [ite_cond_eq_false]
            . omega
            . simp
              omega
        . clear *- h_imm
          rewrite [max_eq_left (by omega)]
          by_cases h_sign : imm.toInt ≥ 0
          . have := @BitVec.toInt_le _ imm
            simp at this
            rewrite [ite_cond_eq_true]
            . have : imm.toInt % 2013265921 = imm.toInt := by omega
              rewrite [this]; clear this
              refine Int.dvd_of_emod_eq_zero ?_
              exact toInt_mod_eq_zero_of_bitvec_mod_eq_zero _ h_imm
            . simp
              clear *- h_sign this
              omega
          . have := BitVec.le_toInt imm
            simp at this
            rewrite [ite_cond_eq_false]
            . have : imm.toInt % 2013265921 = imm.toInt + 2013265921 := by omega
              rewrite [this]; clear this
              simp
              refine Int.dvd_of_emod_eq_zero ?_
              exact toInt_mod_eq_zero_of_bitvec_mod_eq_zero _ h_imm
            . simp
              omega
      }

    lemma readInstructionBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_branch_eq FBB ExtF} {row : ℕ}
      (h_in : entry ∈ readInstructionBus_row air row)
    :
      entry.2.length = Interaction.ReadInstructionBusEntryInstance.data_length
    := by
      unfold readInstructionBus_row at *; simp_all

    @[VmAirWrapper_branch_eq_constraint_and_interaction_simplification]
    def _readInstructionBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.ReadInstructionBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ readInstructionBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (readInstructionBus_row_length x.2)))
          (readInstructionBus_row air row).attach
      List.map Interaction.ReadInstructionBusEntryInstance.deserialise vectorised_row

    @[simp]
    def serialiseToList [Interaction.BusEntry FBB α] (rowData : List α) : List (FBB × List FBB) :=
      rowData.map Interaction.BusEntry.serialiseToList

    @[simp]
    def assumptions [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
      List.Forall id (rowData.map (Interaction.BusEntry.assumptions FBB))

    @[simp]
    def propertiesToAssume [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
      List.Forall id (rowData.map (Interaction.BusEntry.assume FBB))

    @[simp]
    def propertiesToAssert [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
      List.Forall id (rowData.map (Interaction.BusEntry.assert FBB))

    @[simp]
    def busRow [Field ExtF] (air : Valid_VmAirWrapper_branch_eq FBB ExtF) (row : ℕ)
    : List (FBB × List FBB) :=
      executionBus_row air row ++
      memoryBus_row air row ++
      rangeCheckerBus_row air row ++
      readInstructionBus_row air row

    @[simp]
    def assumptionsPerRow [Field ExtF]
      (air : Valid_VmAirWrapper_branch_eq FBB ExtF) (row : ℕ)
    : Prop :=
      assumptions (_executionBus_row air row) ∧
      assumptions (_memoryBus_row air row) ∧
      assumptions (_rangeCheckerBus_row air row) ∧
      assumptions (_readInstructionBus_row air row)

    @[simp]
    def wf_propertiesToAssumePerRow [Field ExtF] (air : Valid_VmAirWrapper_branch_eq FBB ExtF) (row : ℕ)
    : Prop :=
      propertiesToAssume (_executionBus_row air row) ∧
      propertiesToAssume (_memoryBus_row air row) ∧
      propertiesToAssume (_rangeCheckerBus_row air row) ∧
      propertiesToAssume (_readInstructionBus_row air row)

    @[simp]
    def wf_propertiesToAssertPerRow [Field ExtF] (air : Valid_VmAirWrapper_branch_eq FBB ExtF) (row : ℕ)
    : Prop :=
      propertiesToAssert (_executionBus_row air row) ∧
      propertiesToAssert (_memoryBus_row air row) ∧
      propertiesToAssert (_rangeCheckerBus_row air row) ∧
      propertiesToAssert (_readInstructionBus_row air row)

  end bus_entries

end VmAirWrapper_branch_eq.constraints
