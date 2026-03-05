import OpenvmFv.Airs.RangeTupleCheckerAir
import OpenvmFv.Extraction.RangeTupleCheckerAir
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace RangeTupleCheckerAir.constraints

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[RangeTupleCheckerAir_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨ air.main_cols.tuple_0 row 0 = 0

      @[RangeTupleCheckerAir_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir.extraction.constraint_0 air row ↔ constraint_0 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨ air.main_cols.tuple_0 row 0 = 255

      @[RangeTupleCheckerAir_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir.extraction.constraint_1 air row ↔ constraint_1 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨ air.main_cols.tuple_1 row 0 = 0

      @[RangeTupleCheckerAir_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir.extraction.constraint_2 air row ↔ constraint_2 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨ air.main_cols.tuple_1 row 0 = 8191

      @[RangeTupleCheckerAir_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir.extraction.constraint_3 air row ↔ constraint_3 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          air.main_cols.tuple_0 row 1 = air.main_cols.tuple_0 row 0 ∨
            air.main_cols.tuple_0 row 1 - air.main_cols.tuple_0 row 0 = 1

      @[RangeTupleCheckerAir_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir.extraction.constraint_4 air row ↔ constraint_4 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        air.main_cols.tuple_1 row 1 - air.main_cols.tuple_1 row 0 = 1 ∨ air.main_cols.tuple_1 row 0 = 8191

      @[RangeTupleCheckerAir_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir.extraction.constraint_5 air row ↔ constraint_5 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        air.main_cols.tuple_1 row 1 - air.main_cols.tuple_1 row 0 = 1 ∨ air.main_cols.tuple_1 row 1 = 0

      @[RangeTupleCheckerAir_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir.extraction.constraint_6 air row ↔ constraint_6 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_constraint_and_interaction_simplification]

      @[RangeTupleCheckerAir_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : Prop :=
        (air.main_cols.tuple_1 row 1 - air.main_cols.tuple_1 row 0) *
            (air.main_cols.tuple_1 row 1 - air.main_cols.tuple_1 row 0 - 1) *
          ((air.main_cols.tuple_0 row 0 - air.main_cols.tuple_0 row 1) * 2013265667 + 2013265666) +
        (air.main_cols.tuple_0 row 1 - air.main_cols.tuple_0 row 0) *
            (air.main_cols.tuple_0 row 1 - air.main_cols.tuple_0 row 0) *
          ((air.main_cols.tuple_1 row 1 - air.main_cols.tuple_1 row 0) * 2013249538 - 67092481) =
      0

      @[RangeTupleCheckerAir_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ)
      : RangeTupleCheckerAir.extraction.constraint_7 air row ↔ constraint_7 air row := by
        simp_all [openvm_encapsulation,
                  RangeTupleCheckerAir_constraint_and_interaction_simplification]

    end row_constraints

    section interactions

      @[RangeTupleCheckerAir_constraint_and_interaction_simplification]
      def bus_10Bus_row (air : Valid_RangeTupleCheckerAir F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.main_cols.mult row 0, [air.main_cols.tuple_0 row 0, air.main_cols.tuple_1 row 0])]

      lemma constrain_bus_10_interactions
        (air : Valid_RangeTupleCheckerAir F ExtF)
        (h : RangeTupleCheckerAir.extraction.constrain_interactions air)
      :
        air.buses 10 = (List.range (air.last_row + 1)).flatMap (λ row => bus_10Bus_row air row)
      := by
        unfold RangeTupleCheckerAir.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      def constrain_interactions (air : Valid_RangeTupleCheckerAir F ExtF) : Prop :=
        air.buses = fun index ↦
        if index = 10 then (List.range (air.last_row + 1)).flatMap (bus_10Bus_row air)
        else []

      @[RangeTupleCheckerAir_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_RangeTupleCheckerAir F ExtF)
        (h : RangeTupleCheckerAir.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold constrain_interactions
        unfold RangeTupleCheckerAir.extraction.constrain_interactions at h
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
      (air : Valid_RangeTupleCheckerAir F ExtF)
      (row : ℕ)
    : List Prop :=
      [
        RangeTupleCheckerAir.extraction.constraint_0 air row,
        RangeTupleCheckerAir.extraction.constraint_1 air row,
        RangeTupleCheckerAir.extraction.constraint_2 air row,
        RangeTupleCheckerAir.extraction.constraint_3 air row,
        RangeTupleCheckerAir.extraction.constraint_4 air row,
        RangeTupleCheckerAir.extraction.constraint_5 air row,
        RangeTupleCheckerAir.extraction.constraint_6 air row,
        RangeTupleCheckerAir.extraction.constraint_7 air row
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_RangeTupleCheckerAir F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      RangeTupleCheckerAir.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_RangeTupleCheckerAir F ExtF)
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
        constraint_7 air row
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_RangeTupleCheckerAir F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    omit [Field ExtF] in
    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_RangeTupleCheckerAir F ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold RangeTupleCheckerAir.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  RangeTupleCheckerAir_air_simplification]

  end allHold

  section properties

    variable [Field ExtF]

  end properties

end RangeTupleCheckerAir.constraints
