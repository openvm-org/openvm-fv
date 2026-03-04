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

  end properties

end BitwiseOperationLookupAir_8.constraints
