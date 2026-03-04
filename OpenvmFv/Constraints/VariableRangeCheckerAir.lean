import OpenvmFv.Airs.VariableRangeCheckerAir
import OpenvmFv.Extraction.VariableRangeCheckerAir
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace VariableRangeCheckerAir.constraints

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨ air.main_cols.value row 0 = 0

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_0 air row ↔ constraint_0 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨ air.main_cols.max_bits row 0 = 0

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_1 air row ↔ constraint_1 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨ air.main_cols.two_to_max_bits row 0 = 1

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_2 air row ↔ constraint_2 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          air.main_cols.max_bits row 1 = air.main_cols.max_bits row 0 ∨
            air.main_cols.max_bits row 1 - air.main_cols.max_bits row 0 = 1

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_3 air row ↔ constraint_3 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          air.main_cols.value row 1 = 0 ∨ air.main_cols.value row 1 = air.main_cols.value row 0 + 1

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_4 air row ↔ constraint_4 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          air.main_cols.two_to_max_bits row 1 =
            air.main_cols.two_to_max_bits row 0 * (1 + (air.main_cols.max_bits row 1 - air.main_cols.max_bits row 0))

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_5 air row ↔ constraint_5 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          air.main_cols.value row 0 + air.main_cols.two_to_max_bits row 0 + 1 =
            air.main_cols.value row 1 + air.main_cols.two_to_max_bits row 1

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_6 air row ↔ constraint_6 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨ air.main_cols.value row 0 = 0

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_7 air row ↔ constraint_7 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨ air.main_cols.max_bits row 0 = 18

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_8_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_8 air row ↔ constraint_8 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨ air.main_cols.mult row 0 = 0

      @[VariableRangeCheckerAir_air_simplification]
      lemma constraint_9_of_extraction
          (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ)
      : VariableRangeCheckerAir.extraction.constraint_9 air row ↔ constraint_9 air row := by
        simp_all [openvm_encapsulation,
                  VariableRangeCheckerAir_constraint_and_interaction_simplification]

    end row_constraints

    section interactions

      @[VariableRangeCheckerAir_constraint_and_interaction_simplification]
      def bus_3Bus_row (air : Valid_VariableRangeCheckerAir F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.main_cols.mult row 0, [air.main_cols.value row 0, air.main_cols.max_bits row 0])]

      lemma constrain_bus_3_interactions
        (air : Valid_VariableRangeCheckerAir F ExtF)
        (h : VariableRangeCheckerAir.extraction.constrain_interactions air)
      :
        air.buses 3 = (List.range (air.last_row + 1)).flatMap (λ row => bus_3Bus_row air row)
      := by
        unfold VariableRangeCheckerAir.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      def constrain_interactions (air : Valid_VariableRangeCheckerAir F ExtF) : Prop :=
        air.buses = fun index ↦
        if index = 3 then (List.range (air.last_row + 1)).flatMap (bus_3Bus_row air)
        else []

      @[VariableRangeCheckerAir_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VariableRangeCheckerAir F ExtF)
        (h : VariableRangeCheckerAir.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold constrain_interactions
        unfold VariableRangeCheckerAir.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]
        rfl

    end interactions

  end constraint_simplification

  section allHold

    variable [Field F] [Field ExtF]

    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_VariableRangeCheckerAir F ExtF)
      (row : ℕ)
    : List Prop :=
      [
        VariableRangeCheckerAir.extraction.constraint_0 air row,
        VariableRangeCheckerAir.extraction.constraint_1 air row,
        VariableRangeCheckerAir.extraction.constraint_2 air row,
        VariableRangeCheckerAir.extraction.constraint_3 air row,
        VariableRangeCheckerAir.extraction.constraint_4 air row,
        VariableRangeCheckerAir.extraction.constraint_5 air row,
        VariableRangeCheckerAir.extraction.constraint_6 air row,
        VariableRangeCheckerAir.extraction.constraint_7 air row,
        VariableRangeCheckerAir.extraction.constraint_8 air row,
        VariableRangeCheckerAir.extraction.constraint_9 air row
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_VariableRangeCheckerAir F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      VariableRangeCheckerAir.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_VariableRangeCheckerAir F ExtF)
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
        constraint_9 air row
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_VariableRangeCheckerAir F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    omit [Field ExtF] in
    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_VariableRangeCheckerAir F ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold VariableRangeCheckerAir.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  VariableRangeCheckerAir_air_simplification]

  end allHold

  section properties

    variable [Field ExtF]

  end properties

end VariableRangeCheckerAir.constraints
