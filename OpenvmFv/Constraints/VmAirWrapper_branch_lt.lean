import OpenvmFv.Airs.Branch.VmAirWrapper_branch_lt
import OpenvmFv.Extraction.VmAirWrapper_branch_lt
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace VmAirWrapper_branch_lt.constraints

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
      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_blt_flag row 0 = 0 ∨ air.core.opcode_blt_flag row 0 = 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_0 air row ↔ constraint_0 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_bltu_flag row 0 = 0 ∨ air.core.opcode_bltu_flag row 0 = 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_1 air row ↔ constraint_1 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_bge_flag row 0 = 0 ∨ air.core.opcode_bge_flag row 0 = 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_2 air row ↔ constraint_2 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_bgeu_flag row 0 = 0 ∨ air.core.opcode_bgeu_flag row 0 = 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_3 air row ↔ constraint_3 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_4 air row ↔ constraint_4 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.cmp_result row 0 = 0 ∨ air.core.cmp_result row 0 = 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_5 air row ↔ constraint_5 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.cmp_lt row 0 =
          air.core.cmp_result row 0 * air.core.lt row 0 + (1 - air.core.cmp_result row 0) * air.core.ge row 0

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_6 air row ↔ constraint_6 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.a_diff row 0 = 0 ∨ 256 = air.core.a_diff row 0

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_7 air row ↔ constraint_7 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.b_diff row 0 = 0 ∨ 256 = air.core.b_diff row 0

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_8_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_8 air row ↔ constraint_8 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.prefix_sum row 0 3 = 0 ∨ air.core.prefix_sum row 0 3 = 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_9_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_9 air row ↔ constraint_9 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.core.prefix_sum row 0 3 ∨ air.core.diff row 0 3 = 0

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_10_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_10 air row ↔ constraint_10 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.prefix_sum row 0 3 = 0 ∨ air.core.diff_val row 0 = air.core.diff row 0 3

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_11_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_11 air row ↔ constraint_11 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_2 row 0 = 0 ∨ air.core.diff_marker_2 row 0 = 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_12_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_12 air row ↔ constraint_12 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.core.prefix_sum row 0 2 ∨ air.core.diff row 0 2 = 0

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_13_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_13 air row ↔ constraint_13 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_2 row 0 = 0 ∨ air.core.diff_val row 0 = air.core.diff row 0 2

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_14_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_14 air row ↔ constraint_14 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_1 row 0 = 0 ∨ air.core.diff_marker_1 row 0 = 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_15_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_15 air row ↔ constraint_15 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.core.prefix_sum row 0 1 ∨ air.core.diff row 0 1 = 0

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_16_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_16 air row ↔ constraint_16 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_1 row 0 = 0 ∨ air.core.diff_val row 0 = air.core.diff row 0 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_17_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_17 air row ↔ constraint_17 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_0 row 0 = 0 ∨ air.core.diff_marker_0 row 0 = 1


      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_18_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_18 air row ↔ constraint_18 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.core.prefix_sum row 0 0 ∨ air.core.diff row 0 0 = 0

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_19_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_19 air row ↔ constraint_19 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_0 row 0 = 0 ∨ air.core.diff_val row 0 = air.core.diff row 0 0

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_20_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_20 air row ↔ constraint_20 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.prefix_sum row 0 0 = 0 ∨ air.core.prefix_sum row 0 0 = 1

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_21_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_21 air row ↔ constraint_21 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.core.prefix_sum row 0 0 ∨ air.core.cmp_lt row 0 = 0

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_22_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_22 air row ↔ constraint_22 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 - air.adapter.reads_aux.base.prev_timestamp row 0 - 1 =
      air.adapter.reads_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.reads_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_23_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_23 air row ↔ constraint_23 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 + 1 - air.adapter.columns 7 row 0 - 1 =
      air.adapter.columns 8 row 0 + air.adapter.columns 9 row 0 * 131072

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constraint_24_of_extraction
          (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ)
      : VmAirWrapper_branch_lt.extraction.constraint_24 air row ↔ constraint_24 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h
        exact h

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      --busRows, constrain_interactions, and constrain_interactions_of_extraction
      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def executionBus_row (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.core.is_valid row 0, [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0]),
        (air.core.is_valid row 0, [air.to_pc row 0, air.adapter.from_state.timestamp row 0 + 2])]

      lemma constrain_execution_interactions
        (air : Valid_VmAirWrapper_branch_lt F ExtF)
        (h : VmAirWrapper_branch_lt.extraction.constrain_interactions air)
      :
        air.buses ExecutionBus = (List.range (air.last_row + 1)).flatMap (λ row => executionBus_row air row)
      := by
        unfold VmAirWrapper_branch_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def memoryBus_row (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : List (F × List F) :=
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
        (air : Valid_VmAirWrapper_branch_lt F ExtF)
        (h : VmAirWrapper_branch_lt.extraction.constrain_interactions air)
      :
        air.buses MemoryBus = (List.range (air.last_row + 1)).flatMap (λ row => memoryBus_row air row)
      := by
        unfold VmAirWrapper_branch_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def rangeCheckerBus_row (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0, [air.adapter.reads_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.reads_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.core.is_valid row 0, [air.adapter.columns 8 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.columns 9 row 0, 12])]

      lemma constrain_rangeChecker_interactions
        (air : Valid_VmAirWrapper_branch_lt F ExtF)
        (h : VmAirWrapper_branch_lt.extraction.constrain_interactions air)
      :
        air.buses RangeCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeCheckerBus_row air row)
      := by
        unfold VmAirWrapper_branch_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def readInstructionBus_row (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
          [air.adapter.from_state.pc row 0,
            air.core.opcode_bltu_flag row 0 + air.core.opcode_bge_flag row 0 * 2 + air.core.opcode_bgeu_flag row 0 * 3 +
              549,
            air.adapter.rs1_ptr row 0, air.adapter.rs2_ptr row 0, air.core.imm row 0, 1, 1, 0, 0])]

      lemma constrain_readInstruction_interactions
        (air : Valid_VmAirWrapper_branch_lt F ExtF)
        (h : VmAirWrapper_branch_lt.extraction.constrain_interactions air)
      :
        air.buses ReadInstructionBus = (List.range (air.last_row + 1)).flatMap (λ row => readInstructionBus_row air row)
      := by
        unfold VmAirWrapper_branch_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
      def bitwiseBus_row (air : Valid_VmAirWrapper_branch_lt F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
          [air.core.a_msb_f row 0 + 128 * (air.core.opcode_blt_flag row 0 + air.core.opcode_bge_flag row 0),
            air.core.b_msb_f row 0 + 128 * (air.core.opcode_blt_flag row 0 + air.core.opcode_bge_flag row 0), 0, 0]),
        (air.core.prefix_sum row 0 0, [air.core.diff_val row 0 - 1, 0, 0, 0])]

      lemma constrain_bitwise_interactions
        (air : Valid_VmAirWrapper_branch_lt F ExtF)
        (h : VmAirWrapper_branch_lt.extraction.constrain_interactions air)
      :
        air.buses BitwiseBus = (List.range (air.last_row + 1)).flatMap (λ row => bitwiseBus_row air row)
      := by
        unfold VmAirWrapper_branch_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      def constrain_interactions (air : Valid_VmAirWrapper_branch_lt F ExtF) : Prop :=
      air.buses = fun index ↦
      if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
      else if index = MemoryBus then (List.range (air.last_row + 1)).flatMap (memoryBus_row air)
      else if index = RangeCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeCheckerBus_row air)
      else if index = ReadInstructionBus then (List.range (air.last_row + 1)).flatMap (readInstructionBus_row air)
      else if index = BitwiseBus then (List.range (air.last_row + 1)).flatMap (bitwiseBus_row air)
      else []

      @[VmAirWrapper_branch_lt_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VmAirWrapper_branch_lt F ExtF)
        (h : VmAirWrapper_branch_lt.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold VmAirWrapper_branch_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        exact h

    end interactions

  end constraint_simplification

  section allHold

    -- constraint list and allHold
    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        VmAirWrapper_branch_lt.extraction.constraint_0 air row,
        VmAirWrapper_branch_lt.extraction.constraint_1 air row,
        VmAirWrapper_branch_lt.extraction.constraint_2 air row,
        VmAirWrapper_branch_lt.extraction.constraint_3 air row,
        VmAirWrapper_branch_lt.extraction.constraint_4 air row,
        VmAirWrapper_branch_lt.extraction.constraint_5 air row,
        VmAirWrapper_branch_lt.extraction.constraint_6 air row,
        VmAirWrapper_branch_lt.extraction.constraint_7 air row,
        VmAirWrapper_branch_lt.extraction.constraint_8 air row,
        VmAirWrapper_branch_lt.extraction.constraint_9 air row,
        VmAirWrapper_branch_lt.extraction.constraint_10 air row,
        VmAirWrapper_branch_lt.extraction.constraint_11 air row,
        VmAirWrapper_branch_lt.extraction.constraint_12 air row,
        VmAirWrapper_branch_lt.extraction.constraint_13 air row,
        VmAirWrapper_branch_lt.extraction.constraint_14 air row,
        VmAirWrapper_branch_lt.extraction.constraint_15 air row,
        VmAirWrapper_branch_lt.extraction.constraint_16 air row,
        VmAirWrapper_branch_lt.extraction.constraint_17 air row,
        VmAirWrapper_branch_lt.extraction.constraint_18 air row,
        VmAirWrapper_branch_lt.extraction.constraint_19 air row,
        VmAirWrapper_branch_lt.extraction.constraint_20 air row,
        VmAirWrapper_branch_lt.extraction.constraint_21 air row,
        VmAirWrapper_branch_lt.extraction.constraint_22 air row,
        VmAirWrapper_branch_lt.extraction.constraint_23 air row,
        VmAirWrapper_branch_lt.extraction.constraint_24 air row,
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      VmAirWrapper_branch_lt.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
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
        constraint_18 air row,
        constraint_19 air row,
        constraint_20 air row,
        constraint_21 air row,
        constraint_22 air row,
        constraint_23 air row,
        constraint_24 air row,
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold VmAirWrapper_branch_lt.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  VmAirWrapper_branch_lt_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

    lemma single_op
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
    :
      let is_blt := air.core.opcode_blt_flag row 0
      let is_bltu := air.core.opcode_bltu_flag row 0
      let is_bgt := air.core.opcode_bge_flag row 0
      let is_bgtu := air.core.opcode_bgeu_flag row 0
      (is_blt = 1 → is_bltu = 0 ∧ is_bgt = 0 ∧ is_bgtu = 0) ∧
      (is_bltu = 1 → is_blt = 0 ∧ is_bgt = 0 ∧ is_bgtu = 0) ∧
      (is_bgt = 1 → is_blt = 0 ∧ is_bltu = 0 ∧ is_bgtu = 0) ∧
      (is_bgtu = 1 → is_blt = 0 ∧ is_bltu = 0 ∧ is_bgt = 0)
    := by
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, h3, h4, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at h0 h1 h2 h3 h4
      rw [Valid_BranchLessThanCoreAir_4_8.is_valid] at h4
      grind (splits := 14)

    lemma op_from_opcode
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
      (is_valid : air.core.is_valid row 0 = 1)
    :
      let is_blt := air.core.opcode_blt_flag row 0
      let is_bltu := air.core.opcode_bltu_flag row 0
      let is_bgt := air.core.opcode_bge_flag row 0
      let is_bgtu := air.core.opcode_bgeu_flag row 0
      (air.core.expected_opcode row 0 = 549 → is_blt = 1) ∧
      (air.core.expected_opcode row 0 = 550 → is_bltu = 1) ∧
      (air.core.expected_opcode row 0 = 551 → is_bgt = 1) ∧
      (air.core.expected_opcode row 0 = 552 → is_bgtu = 1)
    := by
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, h3, h4, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at *
      rw [Valid_BranchLessThanCoreAir_4_8.is_valid] at is_valid h4
      rw [← BranchLessThanCoreAir_4_8.expected_opcode_def]
      grind

    lemma opcode_bounds
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
      (is_valid : air.core.is_valid row 0 = 1)
    :
      air.core.expected_opcode row 0 = 549 ∨
      air.core.expected_opcode row 0 = 550 ∨
      air.core.expected_opcode row 0 = 551 ∨
      air.core.expected_opcode row 0 = 552
    := by
      have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op air row valid_row cstrs
      rw [← BranchLessThanCoreAir_4_8.expected_opcode_def]
      rw [Valid_BranchLessThanCoreAir_4_8.is_valid] at is_valid
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, h3, h4, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_branch_lt_constraint_and_interaction_simplification] at *
      grind

  end properties

  section bus_entries

    lemma executionBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_branch_lt FBB ExtF} {row : ℕ}
      (h_in : entry ∈ executionBus_row air row)
    :
      entry.2.length = Interaction.ExecutionBusEntryInstance.data_length
    := by
      unfold executionBus_row at *; simp_all
      grind

    @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
    def _executionBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.ExecutionBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ executionBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (executionBus_row_length x.2)))
          (executionBus_row air row).attach
      List.map Interaction.ExecutionBusEntryInstance.deserialise vectorised_row

    lemma memoryBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_branch_lt FBB ExtF} {row : ℕ}
      (h_in : entry ∈ memoryBus_row air row)
    :
      entry.2.length = Interaction.MemoryBusEntryInstance.data_length
    := by
      unfold memoryBus_row at *; simp_all
      grind (ematch := 8)

    @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
    def _memoryBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.MemoryBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ memoryBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (memoryBus_row_length x.2)))
          (memoryBus_row air row).attach
      List.map Interaction.MemoryBusEntryInstance.deserialise vectorised_row

    lemma rangeCheckerBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_branch_lt FBB ExtF} {row : ℕ}
      (h_in : entry ∈ rangeCheckerBus_row air row)
    :
      entry.2.length = Interaction.RangeCheckerBusEntryInstance.data_length
    := by
      unfold rangeCheckerBus_row at *; simp_all
      grind

    @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
    def _rangeCheckerBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.RangeCheckerBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ rangeCheckerBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (rangeCheckerBus_row_length x.2)))
          (rangeCheckerBus_row air row).attach
      List.map Interaction.RangeCheckerBusEntryInstance.deserialise vectorised_row

    @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
    def readInstructionBus_properties (entry : Interaction.ReadInstructionBusEntry FBB) : Prop :=
      let rs1 := entry.xa
      let rs2 := entry.xb
      let imm := entry.xc
      -- rs1 and rs2 are xregs
      rs1.val < 32 ∧ rs2.val < 32 ∧
      -- imm is a 13-bit signed integer represented as a field element
      -2^12 ≤ BabyBear.toInt imm ∧ BabyBear.toInt imm < 2^12 ∧
      -- imm is aligned
      BabyBear.toInt imm % 4 = 0 ∧
      -- unused parameters
      entry.xd = 1 ∧ entry.xe = 1 ∧ entry.xf = 0 ∧ entry.xg = 0

    lemma readInstructionBus_properties_of_opcode_bounds (entry : Interaction.ReadInstructionBusEntry FBB)
      (h_bounds :
        entry.opcode = 549 ∨
        entry.opcode = 550 ∨
        entry.opcode = 551 ∨
        entry.opcode = 552
      )
      (h_bus : Interaction.ReadInstructionBusEntry.operand_properties entry)
    :
      readInstructionBus_properties entry
    := by
      simp [readInstructionBus_properties.eq_def]
      simp [Interaction.ReadInstructionBusEntry.operand_properties] at h_bus
      omega

    lemma readInstructionBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_branch_lt FBB ExtF} {row : ℕ}
      (h_in : entry ∈ readInstructionBus_row air row)
    :
      entry.2.length = Interaction.ReadInstructionBusEntryInstance.data_length
    := by
      unfold readInstructionBus_row at *; simp_all

    @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
    def _readInstructionBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.ReadInstructionBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ readInstructionBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (readInstructionBus_row_length x.2)))
          (readInstructionBus_row air row).attach
      List.map Interaction.ReadInstructionBusEntryInstance.deserialise vectorised_row

    lemma bitwiseBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_branch_lt FBB ExtF} {row : ℕ}
      (h_in : entry ∈ bitwiseBus_row air row)
    :
      entry.2.length = Interaction.BitwiseBusEntryInstance.data_length
    := by
      unfold bitwiseBus_row at *; simp_all
      grind

    @[VmAirWrapper_branch_lt_constraint_and_interaction_simplification]
    def _bitwiseBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF) (row : ℕ) :=
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
    def busRow [Field ExtF] (air : Valid_VmAirWrapper_branch_lt FBB ExtF) (row : ℕ)
    : List (FBB × List FBB) :=
      executionBus_row air row ++
      memoryBus_row air row ++
      rangeCheckerBus_row air row ++
      readInstructionBus_row air row ++
      bitwiseBus_row air row

    @[simp]
    def assumptionsPerRow [Field ExtF]
      (air : Valid_VmAirWrapper_branch_lt FBB ExtF) (row : ℕ)
    : Prop :=
      assumptions (_executionBus_row air row) ∧
      assumptions (_memoryBus_row air row) ∧
      assumptions (_rangeCheckerBus_row air row) ∧
      assumptions (_readInstructionBus_row air row) ∧
      assumptions (_bitwiseBus_row air row)

    @[simp]
    def wf_propertiesToAssumePerRow [Field ExtF] (air : Valid_VmAirWrapper_branch_lt FBB ExtF) (row : ℕ)
    : Prop :=
      propertiesToAssume (_executionBus_row air row) ∧
      propertiesToAssume (_memoryBus_row air row) ∧
      propertiesToAssume (_rangeCheckerBus_row air row) ∧
      propertiesToAssume (_readInstructionBus_row air row) ∧
      propertiesToAssume (_bitwiseBus_row air row)

    @[simp]
    def wf_propertiesToAssertPerRow [Field ExtF] (air : Valid_VmAirWrapper_branch_lt FBB ExtF) (row : ℕ)
    : Prop :=
      propertiesToAssert (_executionBus_row air row) ∧
      propertiesToAssert (_memoryBus_row air row) ∧
      propertiesToAssert (_rangeCheckerBus_row air row) ∧
      propertiesToAssert (_readInstructionBus_row air row) ∧
      propertiesToAssert (_bitwiseBus_row air row)

  end bus_entries

end VmAirWrapper_branch_lt.constraints
