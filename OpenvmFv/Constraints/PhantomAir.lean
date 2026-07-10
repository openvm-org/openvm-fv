import OpenvmFv.Airs.PhantomAir
import OpenvmFv.Extraction.PhantomAir
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace PhantomAir.constraints

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

      -- @[PhantomAir_constraint_and_interaction_simplification]
      -- def constraint_0 (air : Valid_PhantomAir F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[PhantomAir_air_simplification]
      -- lemma constraint_0_of_extraction
      --     (air : Valid_PhantomAir F ExtF) (row : ℕ)
      -- : PhantomAir.extraction.constraint_0 air row ↔ constraint_0 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[PhantomAir_constraint_and_interaction_simplification]
      -- def constraint_1 (air : Valid_PhantomAir F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[PhantomAir_air_simplification]
      -- lemma constraint_1_of_extraction
      --     (air : Valid_PhantomAir F ExtF) (row : ℕ)
      -- : PhantomAir.extraction.constraint_0 air row ↔ constraint_0 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[PhantomAir_constraint_and_interaction_simplification]
      -- def constraint_2 (air : Valid_PhantomAir F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[PhantomAir_air_simplification]
      -- lemma constraint_2_of_extraction
      --     (air : Valid_PhantomAir F ExtF) (row : ℕ)
      -- : PhantomAir.extraction.constraint_0 air row ↔ constraint_0 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[PhantomAir_constraint_and_interaction_simplification]
      -- def constraint_3 (air : Valid_PhantomAir F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[PhantomAir_air_simplification]
      -- lemma constraint_3_of_extraction
      --     (air : Valid_PhantomAir F ExtF) (row : ℕ)
      -- : PhantomAir.extraction.constraint_0 air row ↔ constraint_0 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[PhantomAir_constraint_and_interaction_simplification]
      -- def constraint_4 (air : Valid_PhantomAir F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[PhantomAir_air_simplification]
      -- lemma constraint_4_of_extraction
      --     (air : Valid_PhantomAir F ExtF) (row : ℕ)
      -- : PhantomAir.extraction.constraint_0 air row ↔ constraint_0 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_Rv32BaseAluAdapterAir_ShiftCoreAir_4_8_constraint_and_interaction_simplification] at h
      --   exact h

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      --busRows, constrain_interactions, and constrain_interactions_of_extraction
      @[PhantomAir_constraint_and_interaction_simplification]
      def executionBus_row (air : Valid_PhantomAir F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.is_valid row 0, [air.pc row 0, air.timestamp row 0]),
    (air.is_valid row 0, [air.pc row 0 + 4, air.timestamp row 0 + 1])]

      lemma constrain_execution_interactions
        (air : Valid_PhantomAir F ExtF)
        (h : PhantomAir.extraction.constrain_interactions air)
      :
        air.buses ExecutionBus = (List.range (air.last_row + 1)).flatMap (λ row => executionBus_row air row)
      := by
        unfold PhantomAir.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[PhantomAir_constraint_and_interaction_simplification]
      def programBus_row (air : Valid_PhantomAir F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.is_valid row 0, [air.pc row 0, 1, air.operand_0 row 0, air.operand_1 row 0, air.operand_2 row 0, 0, 0, 0, 0])]

      lemma constrain_program_interactions
        (air : Valid_PhantomAir F ExtF)
        (h : PhantomAir.extraction.constrain_interactions air)
      :
        air.buses ProgramBus = (List.range (air.last_row + 1)).flatMap (λ row => programBus_row air row)
      := by
        unfold PhantomAir.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      def constrain_interactions (air : Valid_PhantomAir F ExtF) : Prop :=
      air.buses = fun index ↦
      if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
      else if index = ProgramBus then (List.range (air.last_row + 1)).flatMap (programBus_row air)
      else []

      @[PhantomAir_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_PhantomAir F ExtF)
        (h : PhantomAir.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold PhantomAir.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        exact h

    end interactions

  end constraint_simplification

  section allHold

    -- constraint list and allHold

    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (_air : Valid_PhantomAir FBB ExtF)
      (_row : ℕ)
    : List Prop :=
      [
    --     PhantomAir.extraction.constraint_0 air row,
    --     PhantomAir.extraction.constraint_1 air row,
    --     PhantomAir.extraction.constraint_2 air row,
    --     PhantomAir.extraction.constraint_3 air row,
    --     PhantomAir.extraction.constraint_4 air row,
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_PhantomAir FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      PhantomAir.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (_air : Valid_PhantomAir FBB ExtF)
      (_row : ℕ)
    : List Prop :=
      [
    --     constraint_0 air row,
    --     constraint_1 air row,
    --     constraint_2 air row,
    --     constraint_3 air row,
    --     constraint_4 air row,
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_PhantomAir FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_PhantomAir FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold PhantomAir.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  PhantomAir_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

  end properties

end PhantomAir.constraints
