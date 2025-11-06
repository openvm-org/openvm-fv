import OpenvmFv.Airs.Branch.VmAirWrapper_auipc
import OpenvmFv.Extraction.VmAirWrapper_auipc
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

namespace VmAirWrapper_auipc.constraints

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
      @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_auipc_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ)
      : VmAirWrapper_auipc.extraction.constraint_0 air row ↔ constraint_0 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_auipc_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_auipc_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_auipc_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_auipc_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
      air.core.carry row 0 (air.adapter.from_state.pc row 0) 1 = 0 ∨
        air.core.carry row 0 (air.adapter.from_state.pc row 0) 1 = 1

      @[VmAirWrapper_auipc_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ)
      : VmAirWrapper_auipc.extraction.constraint_1 air row ↔ constraint_1 air row := by
      apply Iff.intro
      . intro h
        unfold extraction.constraint_1 at h
        simp [openvm_encapsulation, VmAirWrapper_auipc_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_auipc_constraint_and_interaction_simplification]
        exact h
      . intro h
        unfold extraction.constraint_1
        simp [openvm_encapsulation, VmAirWrapper_auipc_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_auipc_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.core.carry row 0 (air.adapter.from_state.pc row 0) 2 = 0 ∨
      air.core.carry row 0 (air.adapter.from_state.pc row 0) 2 = 1

      @[VmAirWrapper_auipc_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ)
      : VmAirWrapper_auipc.extraction.constraint_2 air row ↔ constraint_2 air row := by
      apply Iff.intro
      . intro h
        unfold extraction.constraint_2 at h
        simp [openvm_encapsulation, VmAirWrapper_auipc_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_auipc_constraint_and_interaction_simplification]
        exact h
      . intro h
        unfold extraction.constraint_2
        simp [openvm_encapsulation, VmAirWrapper_auipc_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_auipc_constraint_and_interaction_simplification] at h
        exact h


      @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.core.carry row 0 (air.adapter.from_state.pc row 0) 3 = 0 ∨
      air.core.carry row 0 (air.adapter.from_state.pc row 0) 3 = 1

      @[VmAirWrapper_auipc_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ)
      : VmAirWrapper_auipc.extraction.constraint_3 air row ↔ constraint_3 air row := by
      apply Iff.intro
      . intro h
        unfold extraction.constraint_3 at h
        simp [openvm_encapsulation, VmAirWrapper_auipc_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_auipc_constraint_and_interaction_simplification]
        exact h
      . intro h
        unfold extraction.constraint_3
        simp [openvm_encapsulation, VmAirWrapper_auipc_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_auipc_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 - air.adapter.rd_aux_cols.base.prev_timestamp row 0 - 1 =
      air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_auipc_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ)
      : VmAirWrapper_auipc.extraction.constraint_4 air row ↔ constraint_4 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_auipc_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_auipc_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_auipc_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_auipc_constraint_and_interaction_simplification] at h
        exact h

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      --busRows, constrain_interactions, and constrain_interactions_of_extraction
      @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
      def executionBus_row (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ) : List (F × List F) :=
        [
          (-air.core.is_valid row 0, [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0]),
          (air.core.is_valid row 0, [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 1])
        ]

      lemma constrain_execution_interactions
        (air : Valid_VmAirWrapper_auipc F ExtF)
        (h : VmAirWrapper_auipc.extraction.constrain_interactions air)
      :
        air.buses ExecutionBus = (List.range (air.last_row + 1)).flatMap (λ row => executionBus_row air row)
      := by
        unfold VmAirWrapper_auipc.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
      def memoryBus_row (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ) : List (F × List F) :=
        [(2013265920 * air.core.is_valid row 0,
          [1, air.adapter.rd_ptr row 0, air.adapter.rd_aux_cols.prev_data_0 row 0,
            air.adapter.rd_aux_cols.prev_data_1 row 0, air.adapter.rd_aux_cols.prev_data_2 row 0,
            air.adapter.rd_aux_cols.prev_data_3 row 0, air.adapter.rd_aux_cols.base.prev_timestamp row 0]),
        (air.core.is_valid row 0,
          [1, air.adapter.rd_ptr row 0, air.core.rd_data_0 row 0, air.core.rd_data_1 row 0, air.core.rd_data_2 row 0,
            air.core.rd_data_3 row 0, air.adapter.from_state.timestamp row 0])]

      lemma constrain_memory_interactions
        (air : Valid_VmAirWrapper_auipc F ExtF)
        (h : VmAirWrapper_auipc.extraction.constrain_interactions air)
      :
        air.buses MemoryBus = (List.range (air.last_row + 1)).flatMap (λ row => memoryBus_row air row)
      := by
        unfold VmAirWrapper_auipc.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
      def rangeCheckerBus_row (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0, [air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
         (air.core.is_valid row 0, [air.adapter.rd_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0, 12])]

      lemma constrain_rangeChecker_interactions
        (air : Valid_VmAirWrapper_auipc F ExtF)
        (h : VmAirWrapper_auipc.extraction.constrain_interactions air)
      :
        air.buses RangeCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeCheckerBus_row air row)
      := by
        unfold VmAirWrapper_auipc.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
      def readInstructionBus_row (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
          [air.adapter.from_state.pc row 0, 576, air.adapter.rd_ptr row 0, 0, air.core.imm row 0, 1, 0, 0, 0])]

      lemma constrain_readInstruction_interactions
        (air : Valid_VmAirWrapper_auipc F ExtF)
        (h : VmAirWrapper_auipc.extraction.constrain_interactions air)
      :
        air.buses ReadInstructionBus = (List.range (air.last_row + 1)).flatMap (λ row => readInstructionBus_row air row)
      := by
        unfold VmAirWrapper_auipc.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
      def bitwiseBus_row (air : Valid_VmAirWrapper_auipc F ExtF) (row : ℕ) : List (F × List F) :=
        [
          (air.core.is_valid row 0, [air.core.rd_data_0 row 0, air.core.rd_data_1 row 0, 0, 0]),
          (air.core.is_valid row 0, [air.core.rd_data_2 row 0, air.core.rd_data_3 row 0, 0, 0]),
          (air.core.is_valid row 0, [air.core.imm_limbs_0 row 0, air.core.imm_limbs_1 row 0, 0, 0]),
          (air.core.is_valid row 0, [air.core.imm_limbs_2 row 0, air.core.pc_limbs_0 row 0, 0, 0]),
          (air.core.is_valid row 0, [air.core.pc_limbs_1 row 0, air.core.pc_msl row 0 (air.adapter.from_state.pc row 0) * 4, 0, 0])
        ]

      lemma constrain_bitwise_interactions
        (air : Valid_VmAirWrapper_auipc F ExtF)
        (h : VmAirWrapper_auipc.extraction.constrain_interactions air)
      :
        air.buses BitwiseBus = (List.range (air.last_row + 1)).flatMap (λ row => bitwiseBus_row air row)
      := by
        unfold VmAirWrapper_auipc.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      def constrain_interactions (air : Valid_VmAirWrapper_auipc F ExtF) : Prop :=
      air.buses = fun index ↦
      if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
      else if index = MemoryBus then (List.range (air.last_row + 1)).flatMap (memoryBus_row air)
      else if index = RangeCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeCheckerBus_row air)
      else if index = ReadInstructionBus then (List.range (air.last_row + 1)).flatMap (readInstructionBus_row air)
      else if index = BitwiseBus then (List.range (air.last_row + 1)).flatMap (bitwiseBus_row air)
      else []

      @[VmAirWrapper_auipc_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VmAirWrapper_auipc F ExtF)
        (h : VmAirWrapper_auipc.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold VmAirWrapper_auipc.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        exact h

    end interactions

  end constraint_simplification

  section allHold

    -- constraint list and allHold
    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        VmAirWrapper_auipc.extraction.constraint_0 air row,
        VmAirWrapper_auipc.extraction.constraint_1 air row,
        VmAirWrapper_auipc.extraction.constraint_2 air row,
        VmAirWrapper_auipc.extraction.constraint_3 air row,
        VmAirWrapper_auipc.extraction.constraint_4 air row,
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      VmAirWrapper_auipc.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        constraint_0 air row,
        constraint_1 air row,
        constraint_2 air row,
        constraint_3 air row,
        constraint_4 air row
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold VmAirWrapper_auipc.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  VmAirWrapper_auipc_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

  end properties

  section bus_entries

    lemma executionBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_auipc FBB ExtF} {row : ℕ}
      (h_in : entry ∈ executionBus_row air row)
    :
      entry.2.length = Interaction.ExecutionBusEntryInstance.data_length
    := by
      unfold executionBus_row at *; simp_all
      grind

    @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
    def _executionBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.ExecutionBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ executionBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (executionBus_row_length x.2)))
          (executionBus_row air row).attach
      List.map Interaction.ExecutionBusEntryInstance.deserialise vectorised_row

    lemma memoryBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_auipc FBB ExtF} {row : ℕ}
      (h_in : entry ∈ memoryBus_row air row)
    :
      entry.2.length = Interaction.MemoryBusEntryInstance.data_length
    := by
      unfold memoryBus_row at *; simp_all
      grind (ematch := 8)

    @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
    def _memoryBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.MemoryBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ memoryBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (memoryBus_row_length x.2)))
          (memoryBus_row air row).attach
      List.map Interaction.MemoryBusEntryInstance.deserialise vectorised_row

    lemma rangeCheckerBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_auipc FBB ExtF} {row : ℕ}
      (h_in : entry ∈ rangeCheckerBus_row air row)
    :
      entry.2.length = Interaction.RangeCheckerBusEntryInstance.data_length
    := by
      unfold rangeCheckerBus_row at *; simp_all
      grind

    @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
    def _rangeCheckerBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.RangeCheckerBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ rangeCheckerBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (rangeCheckerBus_row_length x.2)))
          (rangeCheckerBus_row air row).attach
      List.map Interaction.RangeCheckerBusEntryInstance.deserialise vectorised_row

    @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
    def readInstructionBus_properties (entry : Interaction.ReadInstructionBusEntry FBB) : Prop :=
      let imm := entry.xc
      -- imm is a 24-bit unsigned integer
      (imm < 2^24) ∧
      -- with its last four bits zeroed out
      (imm % 16 = 0)

    lemma readInstructionBus_properties_of_opcode_bounds (entry : Interaction.ReadInstructionBusEntry FBB)
      (h_bounds : entry.opcode = 576)
      (h_bus : Interaction.ReadInstructionBusEntry.operand_properties entry)
    :
      readInstructionBus_properties entry
    := by
      simp [readInstructionBus_properties.eq_def]
      simp [Interaction.ReadInstructionBusEntry.operand_properties] at h_bus
      obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus
      have h_alignment := Transpiler.pc_aligned_of_some h_transpile
      simp [←h_data] at h_bounds ⊢ h_transpile h_alignment
      clear h_data
      have := Transpiler.transpiler_opcode_576 h_transpile h_bounds
      split_ands
      . obtain ⟨imm, rd, h_instruction, h_rd⟩ := this
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        dsimp at h_transpile
        rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
        split_ifs at h_transpile
        . simp [-Vector.mk_eq] at h_transpile
          rewrite [←h_transpile] at h_bounds
          simp at h_bounds
        . simp [-Vector.mk_eq] at h_transpile
          rewrite [←h_transpile]
          simp [Transpiler.zero_extend_24, Transpiler.utof]
          rewrite [show (16777216: FBB) = ↑(16777216: ℕ) by trivial, Fin.lt_def]
          simp
          rewrite [Nat.mod_eq_of_lt (by omega)]
          apply Nat.mod_lt
          trivial
      . obtain ⟨imm, rd, h_instruction, h_rd⟩ := this
        rewrite [h_instruction] at h_transpile
        unfold Transpiler.transpile_op at h_transpile
        dsimp at h_transpile
        rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
        split_ifs at h_transpile
        . simp [-Vector.mk_eq] at h_transpile
          rewrite [←h_transpile] at h_bounds
          simp at h_bounds
        . simp [-Vector.mk_eq] at h_transpile
          rewrite [←h_transpile]
          simp [
            Transpiler.utof, Transpiler.zero_extend_24, Fin.mod_def,
            Nat.shiftLeft_eq
          ]
          rewrite [
            @Nat.mod_eq_of_lt _ 16777216 (by omega),
            @Nat.mod_eq_of_lt _ 2013265921 (by omega),
          ]
          omega

    lemma readInstructionBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_auipc FBB ExtF} {row : ℕ}
      (h_in : entry ∈ readInstructionBus_row air row)
    :
      entry.2.length = Interaction.ReadInstructionBusEntryInstance.data_length
    := by
      unfold readInstructionBus_row at *; simp_all

    @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
    def _readInstructionBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.ReadInstructionBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ readInstructionBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (readInstructionBus_row_length x.2)))
          (readInstructionBus_row air row).attach
      List.map Interaction.ReadInstructionBusEntryInstance.deserialise vectorised_row

    lemma bitwiseBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_auipc FBB ExtF} {row : ℕ}
      (h_in : entry ∈ bitwiseBus_row air row)
    :
      entry.2.length = Interaction.BitwiseBusEntryInstance.data_length
    := by
      unfold bitwiseBus_row at *; simp_all
      grind

    @[VmAirWrapper_auipc_constraint_and_interaction_simplification]
    def _bitwiseBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.BitwiseBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ bitwiseBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (bitwiseBus_row_length x.2)))
          (bitwiseBus_row air row).attach
      List.map Interaction.BitwiseBusEntryInstance.deserialise vectorised_row

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
    def busRow [Field ExtF] (air : Valid_VmAirWrapper_auipc FBB ExtF) (row : ℕ)
    : List (FBB × List FBB) :=
      executionBus_row air row ++
      memoryBus_row air row ++
      rangeCheckerBus_row air row ++
      readInstructionBus_row air row ++
      bitwiseBus_row air row

    @[simp]
    def assumptionsPerRow [Field ExtF]
      (air : Valid_VmAirWrapper_auipc FBB ExtF) (row : ℕ)
    : Prop :=
      assumptions (_executionBus_row air row) ∧
      assumptions (_memoryBus_row air row) ∧
      assumptions (_rangeCheckerBus_row air row) ∧
      assumptions (_readInstructionBus_row air row) ∧
      assumptions (_bitwiseBus_row air row)

    @[simp]
    def wf_propertiesToAssumePerRow [Field ExtF] (air : Valid_VmAirWrapper_auipc FBB ExtF) (row : ℕ)
    : Prop :=
      propertiesToAssume (_executionBus_row air row) ∧
      propertiesToAssume (_memoryBus_row air row) ∧
      propertiesToAssume (_rangeCheckerBus_row air row) ∧
      propertiesToAssume (_readInstructionBus_row air row) ∧
      propertiesToAssume (_bitwiseBus_row air row)

    @[simp]
    def wf_propertiesToAssertPerRow [Field ExtF] (air : Valid_VmAirWrapper_auipc FBB ExtF) (row : ℕ)
    : Prop :=
      propertiesToAssert (_executionBus_row air row) ∧
      propertiesToAssert (_memoryBus_row air row) ∧
      propertiesToAssert (_rangeCheckerBus_row air row) ∧
      propertiesToAssert (_readInstructionBus_row air row) ∧
      propertiesToAssert (_bitwiseBus_row air row)

  end bus_entries

end VmAirWrapper_auipc.constraints
