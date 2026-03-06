import OpenvmFv.Airs.BitwiseOperationLookupAir_8
import OpenvmFv.Extraction.BitwiseOperationLookupAir_8
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace BitwiseOperationLookupAir_8.constraints

  section constraint_simplification

    variable [Field F] [Field ExtF]

    section row_constraints

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.x_bits_0 row 0 = 0 ∨ air.main_cols.x_bits_0 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_0 air row ↔ constraint_0 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.y_bits_0 row 0 = 0 ∨ air.main_cols.y_bits_0 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_1 air row ↔ constraint_1 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.x_bits_1 row 0 = 0 ∨ air.main_cols.x_bits_1 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_2 air row ↔ constraint_2 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.y_bits_1 row 0 = 0 ∨ air.main_cols.y_bits_1 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_3 air row ↔ constraint_3 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.x_bits_2 row 0 = 0 ∨ air.main_cols.x_bits_2 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_4 air row ↔ constraint_4 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.y_bits_2 row 0 = 0 ∨ air.main_cols.y_bits_2 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_5 air row ↔ constraint_5 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.x_bits_3 row 0 = 0 ∨ air.main_cols.x_bits_3 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_6 air row ↔ constraint_6 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.y_bits_3 row 0 = 0 ∨ air.main_cols.y_bits_3 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_7 air row ↔ constraint_7 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.x_bits_4 row 0 = 0 ∨ air.main_cols.x_bits_4 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_8_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_8 air row ↔ constraint_8 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.y_bits_4 row 0 = 0 ∨ air.main_cols.y_bits_4 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_9_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_9 air row ↔ constraint_9 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.x_bits_5 row 0 = 0 ∨ air.main_cols.x_bits_5 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_10_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_10 air row ↔ constraint_10 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.y_bits_5 row 0 = 0 ∨ air.main_cols.y_bits_5 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_11_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_11 air row ↔ constraint_11 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.x_bits_6 row 0 = 0 ∨ air.main_cols.x_bits_6 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_12_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_12 air row ↔ constraint_12 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.y_bits_6 row 0 = 0 ∨ air.main_cols.y_bits_6 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_13_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_13 air row ↔ constraint_13 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.x_bits_7 row 0 = 0 ∨ air.main_cols.x_bits_7 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_14_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_14 air row ↔ constraint_14 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        air.main_cols.y_bits_7 row 0 = 0 ∨ air.main_cols.y_bits_7 row 0 = 1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_15_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_15 air row ↔ constraint_15 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        Circuit.isTransitionRow air row = 0 ∨
          (air.main_cols.x_bits_0 row 1 + air.main_cols.x_bits_1 row 1 * 2 + air.main_cols.x_bits_2 row 1 * 4 +
                        air.main_cols.x_bits_3 row 1 * 8 +
                      air.main_cols.x_bits_4 row 1 * 16 +
                    air.main_cols.x_bits_5 row 1 * 32 +
                  air.main_cols.x_bits_6 row 1 * 64 +
                air.main_cols.x_bits_7 row 1 * 128) *
              256 +
            (air.main_cols.y_bits_0 row 1 + air.main_cols.y_bits_1 row 1 * 2 + air.main_cols.y_bits_2 row 1 * 4 +
                      air.main_cols.y_bits_3 row 1 * 8 +
                    air.main_cols.y_bits_4 row 1 * 16 +
                  air.main_cols.y_bits_5 row 1 * 32 +
                air.main_cols.y_bits_6 row 1 * 64 +
              air.main_cols.y_bits_7 row 1 * 128) -
          ((air.main_cols.x_bits_0 row 0 + air.main_cols.x_bits_1 row 0 * 2 + air.main_cols.x_bits_2 row 0 * 4 +
                        air.main_cols.x_bits_3 row 0 * 8 +
                      air.main_cols.x_bits_4 row 0 * 16 +
                    air.main_cols.x_bits_5 row 0 * 32 +
                  air.main_cols.x_bits_6 row 0 * 64 +
                air.main_cols.x_bits_7 row 0 * 128) *
              256 +
            (air.main_cols.y_bits_0 row 0 + air.main_cols.y_bits_1 row 0 * 2 + air.main_cols.y_bits_2 row 0 * 4 +
                      air.main_cols.y_bits_3 row 0 * 8 +
                    air.main_cols.y_bits_4 row 0 * 16 +
                  air.main_cols.y_bits_5 row 0 * 32 +
                air.main_cols.y_bits_6 row 0 * 64 +
              air.main_cols.y_bits_7 row 0 * 128)) =
        1

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_16_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_16 air row ↔ constraint_16 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        Circuit.isFirstRow air row = 0 ∨
          (air.main_cols.x_bits_0 row 0 + air.main_cols.x_bits_1 row 0 * 2 + air.main_cols.x_bits_2 row 0 * 4 +
                      air.main_cols.x_bits_3 row 0 * 8 +
                    air.main_cols.x_bits_4 row 0 * 16 +
                  air.main_cols.x_bits_5 row 0 * 32 +
                air.main_cols.x_bits_6 row 0 * 64 +
              air.main_cols.x_bits_7 row 0 * 128) *
            256 +
          (air.main_cols.y_bits_0 row 0 + air.main_cols.y_bits_1 row 0 * 2 + air.main_cols.y_bits_2 row 0 * 4 +
                    air.main_cols.y_bits_3 row 0 * 8 +
                  air.main_cols.y_bits_4 row 0 * 16 +
                air.main_cols.y_bits_5 row 0 * 32 +
              air.main_cols.y_bits_6 row 0 * 64 +
            air.main_cols.y_bits_7 row 0 * 128) =
        0

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_17_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_17 air row ↔ constraint_17 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : Prop :=
        Circuit.isLastRow air row = 0 ∨
          (air.main_cols.x_bits_0 row 0 + air.main_cols.x_bits_1 row 0 * 2 + air.main_cols.x_bits_2 row 0 * 4 +
                      air.main_cols.x_bits_3 row 0 * 8 +
                    air.main_cols.x_bits_4 row 0 * 16 +
                  air.main_cols.x_bits_5 row 0 * 32 +
                air.main_cols.x_bits_6 row 0 * 64 +
              air.main_cols.x_bits_7 row 0 * 128) *
            256 +
          (air.main_cols.y_bits_0 row 0 + air.main_cols.y_bits_1 row 0 * 2 + air.main_cols.y_bits_2 row 0 * 4 +
                    air.main_cols.y_bits_3 row 0 * 8 +
                  air.main_cols.y_bits_4 row 0 * 16 +
                air.main_cols.y_bits_5 row 0 * 32 +
              air.main_cols.y_bits_6 row 0 * 64 +
            air.main_cols.y_bits_7 row 0 * 128) =
        65535

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constraint_18_of_extraction
          (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ)
      : BitwiseOperationLookupAir_8.extraction.constraint_18 air row ↔ constraint_18 air row := by
        simp_all [openvm_encapsulation,
                  BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]

    end row_constraints

    section interactions

      @[BitwiseOperationLookupAir_8_constraint_and_interaction_simplification]
      def bus_6Bus_row (air : Valid_BitwiseOperationLookupAir_8 F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.main_cols.mult_range row 0,
            [air.main_cols.x_bits_0 row 0 + air.main_cols.x_bits_1 row 0 * 2 + air.main_cols.x_bits_2 row 0 * 4 +
                        air.main_cols.x_bits_3 row 0 * 8 +
                      air.main_cols.x_bits_4 row 0 * 16 +
                    air.main_cols.x_bits_5 row 0 * 32 +
                  air.main_cols.x_bits_6 row 0 * 64 +
                air.main_cols.x_bits_7 row 0 * 128,
              air.main_cols.y_bits_0 row 0 + air.main_cols.y_bits_1 row 0 * 2 + air.main_cols.y_bits_2 row 0 * 4 +
                        air.main_cols.y_bits_3 row 0 * 8 +
                      air.main_cols.y_bits_4 row 0 * 16 +
                    air.main_cols.y_bits_5 row 0 * 32 +
                  air.main_cols.y_bits_6 row 0 * 64 +
                air.main_cols.y_bits_7 row 0 * 128,
              0, 0]),
          (-air.main_cols.mult_xor row 0,
            [air.main_cols.x_bits_0 row 0 + air.main_cols.x_bits_1 row 0 * 2 + air.main_cols.x_bits_2 row 0 * 4 +
                        air.main_cols.x_bits_3 row 0 * 8 +
                      air.main_cols.x_bits_4 row 0 * 16 +
                    air.main_cols.x_bits_5 row 0 * 32 +
                  air.main_cols.x_bits_6 row 0 * 64 +
                air.main_cols.x_bits_7 row 0 * 128,
              air.main_cols.y_bits_0 row 0 + air.main_cols.y_bits_1 row 0 * 2 + air.main_cols.y_bits_2 row 0 * 4 +
                        air.main_cols.y_bits_3 row 0 * 8 +
                      air.main_cols.y_bits_4 row 0 * 16 +
                    air.main_cols.y_bits_5 row 0 * 32 +
                  air.main_cols.y_bits_6 row 0 * 64 +
                air.main_cols.y_bits_7 row 0 * 128,
              air.main_cols.x_bits_0 row 0 + air.main_cols.y_bits_0 row 0 -
                            2 * air.main_cols.x_bits_0 row 0 * air.main_cols.y_bits_0 row 0 +
                          (air.main_cols.x_bits_1 row 0 + air.main_cols.y_bits_1 row 0 -
                              2 * air.main_cols.x_bits_1 row 0 * air.main_cols.y_bits_1 row 0) *
                            2 +
                        (air.main_cols.x_bits_2 row 0 + air.main_cols.y_bits_2 row 0 -
                            2 * air.main_cols.x_bits_2 row 0 * air.main_cols.y_bits_2 row 0) *
                          4 +
                      (air.main_cols.x_bits_3 row 0 + air.main_cols.y_bits_3 row 0 -
                          2 * air.main_cols.x_bits_3 row 0 * air.main_cols.y_bits_3 row 0) *
                        8 +
                    (air.main_cols.x_bits_4 row 0 + air.main_cols.y_bits_4 row 0 -
                        2 * air.main_cols.x_bits_4 row 0 * air.main_cols.y_bits_4 row 0) *
                      16 +
                  (air.main_cols.x_bits_5 row 0 + air.main_cols.y_bits_5 row 0 -
                      2 * air.main_cols.x_bits_5 row 0 * air.main_cols.y_bits_5 row 0) *
                    32 +
                (air.main_cols.x_bits_6 row 0 + air.main_cols.y_bits_6 row 0 -
                    2 * air.main_cols.x_bits_6 row 0 * air.main_cols.y_bits_6 row 0) *
                  64 +
              (air.main_cols.x_bits_7 row 0 + air.main_cols.y_bits_7 row 0 -
                  2 * air.main_cols.x_bits_7 row 0 * air.main_cols.y_bits_7 row 0) *
                128,
              1])]

      lemma constrain_bus_6_interactions
        (air : Valid_BitwiseOperationLookupAir_8 F ExtF)
        (h : BitwiseOperationLookupAir_8.extraction.constrain_interactions air)
      :
        air.buses 6 = (List.range (air.last_row + 1)).flatMap (λ row => bus_6Bus_row air row)
      := by
        unfold BitwiseOperationLookupAir_8.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      def constrain_interactions (air : Valid_BitwiseOperationLookupAir_8 F ExtF) : Prop :=
        air.buses = fun index ↦
        if index = 6 then (List.range (air.last_row + 1)).flatMap (bus_6Bus_row air)
        else []

      @[BitwiseOperationLookupAir_8_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_BitwiseOperationLookupAir_8 F ExtF)
        (h : BitwiseOperationLookupAir_8.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold constrain_interactions
        unfold BitwiseOperationLookupAir_8.extraction.constrain_interactions at h
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
      (air : Valid_BitwiseOperationLookupAir_8 F ExtF)
      (row : ℕ)
    : List Prop :=
      [
        BitwiseOperationLookupAir_8.extraction.constraint_0 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_1 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_2 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_3 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_4 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_5 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_6 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_7 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_8 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_9 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_10 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_11 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_12 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_13 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_14 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_15 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_16 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_17 air row,
        BitwiseOperationLookupAir_8.extraction.constraint_18 air row
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_BitwiseOperationLookupAir_8 F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      BitwiseOperationLookupAir_8.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_BitwiseOperationLookupAir_8 F ExtF)
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
        constraint_11 air row,
        constraint_12 air row,
        constraint_13 air row,
        constraint_14 air row,
        constraint_15 air row,
        constraint_16 air row,
        constraint_17 air row,
        constraint_18 air row
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_BitwiseOperationLookupAir_8 F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    omit [Field ExtF] in
    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_BitwiseOperationLookupAir_8 F ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold BitwiseOperationLookupAir_8.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  BitwiseOperationLookupAir_8_air_simplification]

  end allHold

  section properties

    variable [Field ExtF]

    open BabyBear in
    /-- All constraints hold at every valid row -/
    def all_constraints_hold (air : Valid_BitwiseOperationLookupAir_8 FBB ExtF) : Prop :=
      ∀ row (h_row : row ≤ air.last_row), allHold_simplified air row h_row

    -- Abbreviations matching bus_6Bus_row data fields
    open BabyBear in
    /-- Reconstructed x value from bit decomposition -/
    private abbrev x_ (air : Valid_BitwiseOperationLookupAir_8 FBB ExtF) (row : ℕ) : FBB :=
      air.main_cols.x_bits_0 row 0 + air.main_cols.x_bits_1 row 0 * 2 +
      air.main_cols.x_bits_2 row 0 * 4 + air.main_cols.x_bits_3 row 0 * 8 +
      air.main_cols.x_bits_4 row 0 * 16 + air.main_cols.x_bits_5 row 0 * 32 +
      air.main_cols.x_bits_6 row 0 * 64 + air.main_cols.x_bits_7 row 0 * 128

    open BabyBear in
    /-- Reconstructed y value from bit decomposition -/
    private abbrev y_ (air : Valid_BitwiseOperationLookupAir_8 FBB ExtF) (row : ℕ) : FBB :=
      air.main_cols.y_bits_0 row 0 + air.main_cols.y_bits_1 row 0 * 2 +
      air.main_cols.y_bits_2 row 0 * 4 + air.main_cols.y_bits_3 row 0 * 8 +
      air.main_cols.y_bits_4 row 0 * 16 + air.main_cols.y_bits_5 row 0 * 32 +
      air.main_cols.y_bits_6 row 0 * 64 + air.main_cols.y_bits_7 row 0 * 128

    open BabyBear in
    /-- Reconstructed XOR result from bit-level XOR formula: a ⊕ b = a + b - 2ab -/
    private abbrev xor_ (air : Valid_BitwiseOperationLookupAir_8 FBB ExtF) (row : ℕ) : FBB :=
      air.main_cols.x_bits_0 row 0 + air.main_cols.y_bits_0 row 0 -
          2 * air.main_cols.x_bits_0 row 0 * air.main_cols.y_bits_0 row 0 +
        (air.main_cols.x_bits_1 row 0 + air.main_cols.y_bits_1 row 0 -
            2 * air.main_cols.x_bits_1 row 0 * air.main_cols.y_bits_1 row 0) *
          2 +
        (air.main_cols.x_bits_2 row 0 + air.main_cols.y_bits_2 row 0 -
            2 * air.main_cols.x_bits_2 row 0 * air.main_cols.y_bits_2 row 0) *
          4 +
        (air.main_cols.x_bits_3 row 0 + air.main_cols.y_bits_3 row 0 -
            2 * air.main_cols.x_bits_3 row 0 * air.main_cols.y_bits_3 row 0) *
          8 +
        (air.main_cols.x_bits_4 row 0 + air.main_cols.y_bits_4 row 0 -
            2 * air.main_cols.x_bits_4 row 0 * air.main_cols.y_bits_4 row 0) *
          16 +
        (air.main_cols.x_bits_5 row 0 + air.main_cols.y_bits_5 row 0 -
            2 * air.main_cols.x_bits_5 row 0 * air.main_cols.y_bits_5 row 0) *
          32 +
        (air.main_cols.x_bits_6 row 0 + air.main_cols.y_bits_6 row 0 -
            2 * air.main_cols.x_bits_6 row 0 * air.main_cols.y_bits_6 row 0) *
          64 +
        (air.main_cols.x_bits_7 row 0 + air.main_cols.y_bits_7 row 0 -
            2 * air.main_cols.x_bits_7 row 0 * air.main_cols.y_bits_7 row 0) *
          128

    /-! ### Phase A: Boolean bit extraction -/

    open BabyBear in
    /-- All 16 bit columns are boolean (= 0 or = 1) at every valid row.
        Follows directly from constraints 0–15 (EveryRow boolean gates). -/
    private lemma bits_boolean
        (air : Valid_BitwiseOperationLookupAir_8 FBB ExtF)
        (h_all : all_constraints_hold air)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : (air.main_cols.x_bits_0 row 0 = 0 ∨ air.main_cols.x_bits_0 row 0 = 1) ∧
      (air.main_cols.y_bits_0 row 0 = 0 ∨ air.main_cols.y_bits_0 row 0 = 1) ∧
      (air.main_cols.x_bits_1 row 0 = 0 ∨ air.main_cols.x_bits_1 row 0 = 1) ∧
      (air.main_cols.y_bits_1 row 0 = 0 ∨ air.main_cols.y_bits_1 row 0 = 1) ∧
      (air.main_cols.x_bits_2 row 0 = 0 ∨ air.main_cols.x_bits_2 row 0 = 1) ∧
      (air.main_cols.y_bits_2 row 0 = 0 ∨ air.main_cols.y_bits_2 row 0 = 1) ∧
      (air.main_cols.x_bits_3 row 0 = 0 ∨ air.main_cols.x_bits_3 row 0 = 1) ∧
      (air.main_cols.y_bits_3 row 0 = 0 ∨ air.main_cols.y_bits_3 row 0 = 1) ∧
      (air.main_cols.x_bits_4 row 0 = 0 ∨ air.main_cols.x_bits_4 row 0 = 1) ∧
      (air.main_cols.y_bits_4 row 0 = 0 ∨ air.main_cols.y_bits_4 row 0 = 1) ∧
      (air.main_cols.x_bits_5 row 0 = 0 ∨ air.main_cols.x_bits_5 row 0 = 1) ∧
      (air.main_cols.y_bits_5 row 0 = 0 ∨ air.main_cols.y_bits_5 row 0 = 1) ∧
      (air.main_cols.x_bits_6 row 0 = 0 ∨ air.main_cols.x_bits_6 row 0 = 1) ∧
      (air.main_cols.y_bits_6 row 0 = 0 ∨ air.main_cols.y_bits_6 row 0 = 1) ∧
      (air.main_cols.x_bits_7 row 0 = 0 ∨ air.main_cols.x_bits_7 row 0 = 1) ∧
      (air.main_cols.y_bits_7 row 0 = 0 ∨ air.main_cols.y_bits_7 row 0 = 1) := by
      have h := h_all row h_row
      simp only [allHold_simplified, row_constraint_list, List.forall_cons,
        BitwiseOperationLookupAir_8_constraint_and_interaction_simplification] at h
      exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
             h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
             h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
             h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
             h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

    /-! ### Phase B: Range properties -/

    open BabyBear in
    /-- Sum of 8 boolean BabyBear elements weighted by powers of 2 is < 256.
        Max value: 1+2+4+8+16+32+64+128 = 255 < 256 < BB_prime. -/
    private lemma binary_sum_lt_256 (b0 b1 b2 b3 b4 b5 b6 b7 : FBB)
        (h0 : b0 = 0 ∨ b0 = 1) (h1 : b1 = 0 ∨ b1 = 1)
        (h2 : b2 = 0 ∨ b2 = 1) (h3 : b3 = 0 ∨ b3 = 1)
        (h4 : b4 = 0 ∨ b4 = 1) (h5 : b5 = 0 ∨ b5 = 1)
        (h6 : b6 = 0 ∨ b6 = 1) (h7 : b7 = 0 ∨ b7 = 1)
    : (b0 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16 + b5 * 32 + b6 * 64 + b7 * 128).val < 256 := by
      rcases h0 with ( rfl | rfl ) <;> rcases h1 with ( rfl | rfl ) <;> rcases h2 with ( rfl | rfl ) <;> rcases h3 with ( rfl | rfl ) <;> rcases h4 with ( rfl | rfl ) <;> rcases h5 with ( rfl | rfl ) <;> rcases h6 with ( rfl | rfl ) <;> rcases h7 with ( rfl | rfl ) <;> decide;

    open BabyBear in
    /-- x = Σ x_bits_i * 2^i < 256 -/
    private lemma x_val_lt_256
        (air : Valid_BitwiseOperationLookupAir_8 FBB ExtF)
        (h_all : all_constraints_hold air)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : (x_ air row).val < 256 := by
      obtain ⟨hx0, _, hx1, _, hx2, _, hx3, _, hx4, _, hx5, _, hx6, _, hx7, _⟩ :=
        bits_boolean air h_all row h_row
      exact binary_sum_lt_256 _ _ _ _ _ _ _ _ hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7

    open BabyBear in
    /-- y = Σ y_bits_i * 2^i < 256 -/
    private lemma y_val_lt_256
        (air : Valid_BitwiseOperationLookupAir_8 FBB ExtF)
        (h_all : all_constraints_hold air)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : (y_ air row).val < 256 := by
      obtain ⟨_, hy0, _, hy1, _, hy2, _, hy3, _, hy4, _, hy5, _, hy6, _, hy7⟩ :=
        bits_boolean air h_all row h_row
      exact binary_sum_lt_256 _ _ _ _ _ _ _ _ hy0 hy1 hy2 hy3 hy4 hy5 hy6 hy7

    /-! ### Phase C: XOR correctness -/

    open BabyBear in
    /-- Single-bit XOR identity: for boolean a, b in BabyBear,
        (a + b - 2*a*b).val = a.val ^^^ b.val.
        Proof: 4-case analysis on (a,b) ∈ {0,1}². -/
    private lemma bit_xor_val (a b : FBB)
        (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    : (a + b - 2 * a * b).val = a.val ^^^ b.val := by
      rcases ha with ( rfl | rfl ) <;> rcases hb with ( rfl | rfl ) <;> native_decide

    open BabyBear in
    /-- For boolean a, b in BabyBear, a + b - 2*a*b is boolean. -/
    private lemma bit_xor_boolean (a b : FBB)
        (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    : a + b - 2 * a * b = 0 ∨ a + b - 2 * a * b = 1 := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

    open BabyBear in
    /-- Lifting .val through Fin add/mul for boolean inputs:
        (b0 + b1*2 + ... + b7*128).val = b0.val + b1.val*2 + ... + b7.val*128
        when each b_i ∈ {0, 1}. Holds because max sum = 255 < BB_prime. -/
    private lemma binary_sum_val_eq (b0 b1 b2 b3 b4 b5 b6 b7 : FBB)
        (h0 : b0 = 0 ∨ b0 = 1) (h1 : b1 = 0 ∨ b1 = 1)
        (h2 : b2 = 0 ∨ b2 = 1) (h3 : b3 = 0 ∨ b3 = 1)
        (h4 : b4 = 0 ∨ b4 = 1) (h5 : b5 = 0 ∨ b5 = 1)
        (h6 : b6 = 0 ∨ b6 = 1) (h7 : b7 = 0 ∨ b7 = 1)
    : (b0 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16 + b5 * 32 + b6 * 64 + b7 * 128).val =
      b0.val + b1.val * 2 + b2.val * 4 + b3.val * 8 + b4.val * 16 + b5.val * 32 + b6.val * 64 + b7.val * 128 := by
      grind

    /-- XOR distributes over binary representation (over Fin 2 for decidability). -/
    private lemma nat_xor_binary_decomp (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2)
    : (a0.val + a1.val * 2 + a2.val * 4 + a3.val * 8 + a4.val * 16 + a5.val * 32 + a6.val * 64 + a7.val * 128) ^^^
      (b0.val + b1.val * 2 + b2.val * 4 + b3.val * 8 + b4.val * 16 + b5.val * 32 + b6.val * 64 + b7.val * 128) =
      (a0.val ^^^ b0.val) + (a1.val ^^^ b1.val) * 2 + (a2.val ^^^ b2.val) * 4 + (a3.val ^^^ b3.val) * 8 +
      (a4.val ^^^ b4.val) * 16 + (a5.val ^^^ b5.val) * 32 + (a6.val ^^^ b6.val) * 64 + (a7.val ^^^ b7.val) * 128 := by
      revert a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7; native_decide

    open BabyBear in
    /-- 8-bit XOR decomposition: the weighted sum of per-bit XOR formulas
        equals the Nat.xor of the two 8-bit binary sums.
        This is the core algebraic fact connecting field-level XOR computation
        to natural number XOR. -/
    private lemma binary_xor_sum_correct
        (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : FBB)
        (ha0 : a0 = 0 ∨ a0 = 1) (ha1 : a1 = 0 ∨ a1 = 1)
        (ha2 : a2 = 0 ∨ a2 = 1) (ha3 : a3 = 0 ∨ a3 = 1)
        (ha4 : a4 = 0 ∨ a4 = 1) (ha5 : a5 = 0 ∨ a5 = 1)
        (ha6 : a6 = 0 ∨ a6 = 1) (ha7 : a7 = 0 ∨ a7 = 1)
        (hb0 : b0 = 0 ∨ b0 = 1) (hb1 : b1 = 0 ∨ b1 = 1)
        (hb2 : b2 = 0 ∨ b2 = 1) (hb3 : b3 = 0 ∨ b3 = 1)
        (hb4 : b4 = 0 ∨ b4 = 1) (hb5 : b5 = 0 ∨ b5 = 1)
        (hb6 : b6 = 0 ∨ b6 = 1) (hb7 : b7 = 0 ∨ b7 = 1)
    : (a0 + b0 - 2 * a0 * b0 +
        (a1 + b1 - 2 * a1 * b1) * 2 +
        (a2 + b2 - 2 * a2 * b2) * 4 +
        (a3 + b3 - 2 * a3 * b3) * 8 +
        (a4 + b4 - 2 * a4 * b4) * 16 +
        (a5 + b5 - 2 * a5 * b5) * 32 +
        (a6 + b6 - 2 * a6 * b6) * 64 +
        (a7 + b7 - 2 * a7 * b7) * 128).val =
      (a0 + a1 * 2 + a2 * 4 + a3 * 8 + a4 * 16 + a5 * 32 + a6 * 64 + a7 * 128).val ^^^
      (b0 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16 + b5 * 32 + b6 * 64 + b7 * 128).val := by
      -- Establish per-bit XOR values are boolean
      have hc0 := bit_xor_boolean a0 b0 ha0 hb0
      have hc1 := bit_xor_boolean a1 b1 ha1 hb1
      have hc2 := bit_xor_boolean a2 b2 ha2 hb2
      have hc3 := bit_xor_boolean a3 b3 ha3 hb3
      have hc4 := bit_xor_boolean a4 b4 ha4 hb4
      have hc5 := bit_xor_boolean a5 b5 ha5 hb5
      have hc6 := bit_xor_boolean a6 b6 ha6 hb6
      have hc7 := bit_xor_boolean a7 b7 ha7 hb7
      -- Lift LHS .val through Fin add/mul
      rw [binary_sum_val_eq _ _ _ _ _ _ _ _ hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7]
      -- Rewrite each per-bit (a+b-2ab).val to a.val ^^^ b.val
      simp only [bit_xor_val a0 b0 ha0 hb0, bit_xor_val a1 b1 ha1 hb1,
                  bit_xor_val a2 b2 ha2 hb2, bit_xor_val a3 b3 ha3 hb3,
                  bit_xor_val a4 b4 ha4 hb4, bit_xor_val a5 b5 ha5 hb5,
                  bit_xor_val a6 b6 ha6 hb6, bit_xor_val a7 b7 ha7 hb7]
      -- Lift RHS .val through Fin add/mul for both x and y sums
      rw [binary_sum_val_eq a0 a1 a2 a3 a4 a5 a6 a7 ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7,
          binary_sum_val_eq b0 b1 b2 b3 b4 b5 b6 b7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
      -- Apply XOR binary decomposition (convert FBB .val to Fin 2)
      have val_lt : ∀ (a : FBB), a = 0 ∨ a = 1 → a.val < 2 := by
        rintro a (rfl | rfl) <;> decide
      exact (nat_xor_binary_decomp
        ⟨_, val_lt _ ha0⟩ ⟨_, val_lt _ ha1⟩ ⟨_, val_lt _ ha2⟩ ⟨_, val_lt _ ha3⟩
        ⟨_, val_lt _ ha4⟩ ⟨_, val_lt _ ha5⟩ ⟨_, val_lt _ ha6⟩ ⟨_, val_lt _ ha7⟩
        ⟨_, val_lt _ hb0⟩ ⟨_, val_lt _ hb1⟩ ⟨_, val_lt _ hb2⟩ ⟨_, val_lt _ hb3⟩
        ⟨_, val_lt _ hb4⟩ ⟨_, val_lt _ hb5⟩ ⟨_, val_lt _ hb6⟩ ⟨_, val_lt _ hb7⟩).symm

    /-! ### Main theorems — match BitwiseBusEntryInstance.wf_properties exactly

    BitwiseBusEntryInstance.wf_properties is:
      fun ⟨_, a, b, c, op⟩ =>
        a.val < 256 ∧ b.val < 256 ∧
        (op = 0 ∨ op = 1) ∧
        c.val = if op = 0 then 0 else a.val ^^^ b.val

    bus_6Bus_row emits two entries per row:
      Entry 1: (mult, [x, y, 0, 0])     → a=x_, b=y_, c=0,    op=0
      Entry 2: (mult, [x, y, xor_, 1])  → a=x_, b=y_, c=xor_, op=1
    -/

    open BabyBear in
    /-- wf_properties for bus entry 1 (range-check): a=x_, b=y_, c=0, op=0 -/
    theorem wf_properties_range
        (air : Valid_BitwiseOperationLookupAir_8 FBB ExtF)
        (h_all : all_constraints_hold air)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : (x_ air row).val < 256 ∧ (y_ air row).val < 256 ∧
      ((0 : FBB) = 0 ∨ (0 : FBB) = 1) ∧
      (0 : FBB).val = if (0 : FBB) = 0 then 0 else (x_ air row).val ^^^ (y_ air row).val := by
      exact ⟨x_val_lt_256 air h_all row h_row,
             y_val_lt_256 air h_all row h_row,
             Or.inl rfl,
             rfl⟩

    open BabyBear in
    /-- wf_properties for bus entry 2 (XOR): a=x_, b=y_, c=xor_, op=1 -/
    theorem wf_properties_xor
        (air : Valid_BitwiseOperationLookupAir_8 FBB ExtF)
        (h_all : all_constraints_hold air)
        (row : ℕ) (h_row : row ≤ air.last_row)
    : (x_ air row).val < 256 ∧ (y_ air row).val < 256 ∧
      ((1 : FBB) = 0 ∨ (1 : FBB) = 1) ∧
      (xor_ air row).val = if (1 : FBB) = 0 then 0 else (x_ air row).val ^^^ (y_ air row).val := by
      have hb := bits_boolean air h_all row h_row
      obtain ⟨hx0, hy0, hx1, hy1, hx2, hy2, hx3, hy3, hx4, hy4, hx5, hy5, hx6, hy6, hx7, hy7⟩ := hb
      refine ⟨x_val_lt_256 air h_all row h_row,
              y_val_lt_256 air h_all row h_row,
              Or.inr rfl,
              ?_⟩
      simp only [show (1 : FBB) ≠ 0 from by decide, ↓reduceIte]
      exact binary_xor_sum_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hy0 hy1 hy2 hy3 hy4 hy5 hy6 hy7

  end properties

end BitwiseOperationLookupAir_8.constraints
