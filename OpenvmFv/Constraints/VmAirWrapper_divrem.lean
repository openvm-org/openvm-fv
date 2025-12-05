import OpenvmFv.Airs.Alu.VmAirWrapper_divrem
import OpenvmFv.Extraction.VmAirWrapper_divrem
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace VmAirWrapper_divrem.constraints

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

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_div_flag row 0 = 0 ∨ air.core.opcode_div_flag row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_0 air row ↔ constraint_0 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_divu_flag row 0 = 0 ∨ air.core.opcode_divu_flag row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_1 air row ↔ constraint_1 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_rem_flag row 0 = 0 ∨ air.core.opcode_rem_flag row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_2 air row ↔ constraint_2 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_remu_flag row 0 = 0 ∨ air.core.opcode_remu_flag row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_3 air row ↔ constraint_3 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_4 air row ↔ constraint_4 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.special_case row 0 = 0 ∨ air.core.special_case row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_5 air row ↔ constraint_5 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.zero_divisor row 0 = 0 ∨ air.core.zero_divisor row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_6 air row ↔ constraint_6 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.zero_divisor row 0 = 0 ∨ air.core.c_0 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_7 air row ↔ constraint_7 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.zero_divisor row 0 = 0 ∨ air.core.q_0 row 0 = 255

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_8_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_8 air row ↔ constraint_8 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.zero_divisor row 0 = 0 ∨ air.core.c_1 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_9_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_9 air row ↔ constraint_9 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.zero_divisor row 0 = 0 ∨ air.core.q_1 row 0 = 255

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_10_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_10 air row ↔ constraint_10 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.zero_divisor row 0 = 0 ∨ air.core.c_2 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_11_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_11 air row ↔ constraint_11 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.zero_divisor row 0 = 0 ∨ air.core.q_2 row 0 = 255

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_12_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_12 air row ↔ constraint_12 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.zero_divisor row 0 = 0 ∨ air.core.c_3 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_13_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_13 air row ↔ constraint_13 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.zero_divisor row 0 = 0 ∨ air.core.q_3 row 0 = 255

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_14_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_14 air row ↔ constraint_14 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.valid_and_not_zero_divisor row 0 = 0 ∨ air.core.valid_and_not_zero_divisor row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_15_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_15 air row ↔ constraint_15 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.valid_and_not_zero_divisor row 0 = 0 ∨ air.core.c_sum row 0 * air.core.c_sum_inv row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_16_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_16 air row ↔ constraint_16 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.r_zero row 0 = 0 ∨ air.core.r_zero row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_17_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_17 air row ↔ constraint_17 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.r_zero row 0 = 0 ∨ air.core.r_0 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_18_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_18 air row ↔ constraint_18 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.r_zero row 0 = 0 ∨ air.core.r_1 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_19_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_19 air row ↔ constraint_19 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.r_zero row 0 = 0 ∨ air.core.r_2 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_20_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_20 air row ↔ constraint_20 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.r_zero row 0 = 0 ∨ air.core.r_3 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_21_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_21 air row ↔ constraint_21 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.valid_and_not_special_case row 0 = 0 ∨ air.core.valid_and_not_special_case row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_22_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_22 air row ↔ constraint_22 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.valid_and_not_special_case row 0 = 0 ∨ air.core.r_sum row 0 * air.core.r_sum_inv row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_23_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_23 air row ↔ constraint_23 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.b_sign row 0 = 0 ∨ air.core.b_sign row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_24_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_24 air row ↔ constraint_24 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.c_sign row 0 = 0 ∨ air.core.c_sign row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_25_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_25 air row ↔ constraint_25 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.signed row 0 = 1 ∨ air.core.b_sign row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_26_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_26 air row ↔ constraint_26 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.signed row 0 = 1 ∨ air.core.c_sign row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_27_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_27 air row ↔ constraint_27 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.b_sign row 0 + air.core.c_sign row 0 - 2 * air.core.b_sign row 0 * air.core.c_sign row 0 =
    air.core.sign_xor row 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_28_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_28 air row ↔ constraint_28 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.q_sign row 0 = 0 ∨ air.core.q_sign row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_29_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_29 air row ↔ constraint_29 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.nonzero_q row 0 = 0 ∨ air.core.zero_divisor row 0 = 1 ∨ air.core.q_sign row 0 = air.core.sign_xor row 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_30_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_30 air row ↔ constraint_30 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.q_sign row 0 = air.core.sign_xor row 0 ∨ air.core.zero_divisor row 0 = 1 ∨ air.core.q_sign row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_31_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_31 air row ↔ constraint_31 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 1 ∨ air.core.r_0 row 0 = air.core.r_prime_0 row 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_32_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_32 air row ↔ constraint_32 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ air.core.carry_lt row 0 0 = 0 ∨ air.core.carry_lt row 0 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_33_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_33 air row ↔ constraint_33 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ (air.core.r_prime_0 row 0 - 256) * air.core.r_inv_0 row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_34_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_34 air row ↔ constraint_34 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ air.core.carry_lt row 0 0 = 1 ∨ air.core.r_prime_0 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_35_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_35 air row ↔ constraint_35 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 1 ∨ air.core.r_1 row 0 = air.core.r_prime_1 row 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_36_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_36 air row ↔ constraint_36 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ air.core.carry_lt row 0 1 = air.core.carry_lt row 0 0 ∨ air.core.carry_lt row 0 1 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_37_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_37 air row ↔ constraint_37 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ (air.core.r_prime_1 row 0 - 256) * air.core.r_inv_1 row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_38_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_38 air row ↔ constraint_38 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ air.core.carry_lt row 0 1 = 1 ∨ air.core.r_prime_1 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_39_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_39 air row ↔ constraint_39 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 1 ∨ air.core.r_2 row 0 = air.core.r_prime_2 row 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_40_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_40 air row ↔ constraint_40 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ air.core.carry_lt row 0 2 = air.core.carry_lt row 0 1 ∨ air.core.carry_lt row 0 2 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_41_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_41 air row ↔ constraint_41 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ (air.core.r_prime_2 row 0 - 256) * air.core.r_inv_2 row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_42_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_42 air row ↔ constraint_42 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ air.core.carry_lt row 0 2 = 1 ∨ air.core.r_prime_2 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_43_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_43 air row ↔ constraint_43 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 1 ∨ air.core.r_3 row 0 = air.core.r_prime_3 row 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_44_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_44 air row ↔ constraint_44 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ air.core.carry_lt row 0 3 = air.core.carry_lt row 0 2 ∨ air.core.carry_lt row 0 3 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_45_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_45 air row ↔ constraint_45 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ (air.core.r_prime_3 row 0 - 256) * air.core.r_inv_3 row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_46_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_46 air row ↔ constraint_46 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.sign_xor row 0 = 0 ∨ air.core.carry_lt row 0 3 = 1 ∨ air.core.r_prime_3 row 0 = 0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_47_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_47 air row ↔ constraint_47 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.lt_marker_3 row 0 = 0 ∨ air.core.lt_marker_3 row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_48_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_48 air row ↔ constraint_48 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.special_case row 0 + air.core.lt_marker_3 row 0 = 1 ∨
          air.core.r_prime_3 row 0 * (2 * air.core.c_sign row 0 - 1) + air.core.c_3 row 0 * (1 - 2 * air.core.c_sign row 0) =
            0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_49_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_49 air row ↔ constraint_49 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.lt_marker_3 row 0 = 0 ∨
          air.core.lt_diff row 0 =
            air.core.r_prime_3 row 0 * (2 * air.core.c_sign row 0 - 1) + air.core.c_3 row 0 * (1 - 2 * air.core.c_sign row 0)

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_50_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_50 air row ↔ constraint_50 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.lt_marker_2 row 0 = 0 ∨ air.core.lt_marker_2 row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_51_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_51 air row ↔ constraint_51 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.special_case row 0 + air.core.lt_marker_3 row 0 + air.core.lt_marker_2 row 0 = 1 ∨
          air.core.r_prime_2 row 0 * (2 * air.core.c_sign row 0 - 1) + air.core.c_2 row 0 * (1 - 2 * air.core.c_sign row 0) =
            0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_52_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_52 air row ↔ constraint_52 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.lt_marker_2 row 0 = 0 ∨
          air.core.lt_diff row 0 =
            air.core.r_prime_2 row 0 * (2 * air.core.c_sign row 0 - 1) + air.core.c_2 row 0 * (1 - 2 * air.core.c_sign row 0)

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_53_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_53 air row ↔ constraint_53 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.lt_marker_1 row 0 = 0 ∨ air.core.lt_marker_1 row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_54_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_54 air row ↔ constraint_54 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
      air.core.special_case row 0 + air.core.lt_marker_3 row 0 + air.core.lt_marker_2 row 0 +
        air.core.lt_marker_1 row 0 = 1 ∨
    air.core.r_prime_1 row 0 * (2 * air.core.c_sign row 0 - 1) + air.core.c_1 row 0 * (1 - 2 * air.core.c_sign row 0) =
      0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_55_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_55 air row ↔ constraint_55 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.lt_marker_1 row 0 = 0 ∨
    air.core.lt_diff row 0 =
      air.core.r_prime_1 row 0 * (2 * air.core.c_sign row 0 - 1) + air.core.c_1 row 0 * (1 - 2 * air.core.c_sign row 0)

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_56_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_56 air row ↔ constraint_56 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.lt_marker_0 row 0 = 0 ∨ air.core.lt_marker_0 row 0 = 1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_57_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_57 air row ↔ constraint_57 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
      air.core.special_case row 0 + air.core.lt_marker_3 row 0 + air.core.lt_marker_2 row 0 +
          air.core.lt_marker_1 row 0 +
        air.core.lt_marker_0 row 0 = 1 ∨
    air.core.r_prime_0 row 0 * (2 * air.core.c_sign row 0 - 1) + air.core.c_0 row 0 * (1 - 2 * air.core.c_sign row 0) =
      0

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_58_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_58 air row ↔ constraint_58 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        grind
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        grind

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_59 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.lt_marker_0 row 0 = 0 ∨
    air.core.lt_diff row 0 =
      air.core.r_prime_0 row 0 * (2 * air.core.c_sign row 0 - 1) + air.core.c_0 row 0 * (1 - 2 * air.core.c_sign row 0)

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_59_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_59 air row ↔ constraint_59 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_60 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.core.special_case row 0 + air.core.lt_marker_3 row 0 + air.core.lt_marker_2 row 0 + air.core.lt_marker_1 row 0 +
        air.core.lt_marker_0 row 0 =
      1

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_60_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_60 air row ↔ constraint_60 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_61 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 - air.adapter.reads_aux_0.base.prev_timestamp row 0 - 1 =
      air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_61_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_61 air row ↔ constraint_61 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_62 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 + 1 - air.adapter.reads_aux_1.base.prev_timestamp row 0 - 1 =
      air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_62_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_62 air row ↔ constraint_62 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def constraint_63 (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
          air.adapter.from_state.timestamp row 0 + 2 - air.adapter.writes_aux.base.prev_timestamp row 0 - 1 =
            air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 +
              air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_divrem_air_simplification]
      lemma constraint_63_of_extraction
          (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ)
      : VmAirWrapper_divrem.extraction.constraint_63 air row ↔ constraint_63 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_divrem_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_divrem_constraint_and_interaction_simplification] at h
        exact h

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      --busRows, constrain_interactions, and constrain_interactions_of_extraction

      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def executionBus_row (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.core.is_valid row 0, [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0]),
        (air.core.is_valid row 0, [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3])]

      lemma constrain_execution_interactions
        (air : Valid_VmAirWrapper_divrem F ExtF)
        (h : VmAirWrapper_divrem.extraction.constrain_interactions air)
      :
        air.buses ExecutionBus = (List.range (air.last_row + 1)).flatMap (λ row => executionBus_row air row)
      := by
        unfold VmAirWrapper_divrem.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def memoryBus_row (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : List (F × List F) :=
        [(2013265920 * air.core.is_valid row 0,
          [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0,
            air.adapter.reads_aux_0.base.prev_timestamp row 0]),
        (air.core.is_valid row 0,
          [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0,
            air.adapter.from_state.timestamp row 0]),
        (2013265920 * air.core.is_valid row 0,
          [1, air.adapter.rs2_ptr row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0,
            air.adapter.reads_aux_1.base.prev_timestamp row 0]),
        (air.core.is_valid row 0,
          [1, air.adapter.rs2_ptr row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0, air.core.c_3 row 0,
            air.adapter.from_state.timestamp row 0 + 1]),
        (2013265920 * air.core.is_valid row 0,
          [1, air.adapter.rd_ptr row 0, air.adapter.writes_aux.prev_data_0 row 0,
            air.adapter.writes_aux.prev_data_1 row 0, air.adapter.writes_aux.prev_data_2 row 0,
            air.adapter.writes_aux.prev_data_3 row 0, air.adapter.writes_aux.base.prev_timestamp row 0]),
        (air.core.is_valid row 0,
          [1, air.adapter.rd_ptr row 0, air.core.a row 0 0, air.core.a row 0 1, air.core.a row 0 2, air.core.a row 0 3,
            air.adapter.from_state.timestamp row 0 + 2])]

      lemma constrain_memory_interactions
        (air : Valid_VmAirWrapper_divrem F ExtF)
        (h : VmAirWrapper_divrem.extraction.constrain_interactions air)
      :
        air.buses MemoryBus = (List.range (air.last_row + 1)).flatMap (λ row => memoryBus_row air row)
      := by
        unfold VmAirWrapper_divrem.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def rangeCheckerBus_row (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0, [air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.core.is_valid row 0, [air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.core.is_valid row 0, [air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12])]

      lemma constrain_rangeChecker_interactions
        (air : Valid_VmAirWrapper_divrem F ExtF)
        (h : VmAirWrapper_divrem.extraction.constrain_interactions air)
      :
        air.buses RangeCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeCheckerBus_row air row)
      := by
        unfold VmAirWrapper_divrem.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def programBus_row (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
          [air.adapter.from_state.pc row 0,
            air.core.opcode_divu_flag row 0 + air.core.opcode_rem_flag row 0 * 2 + air.core.opcode_remu_flag row 0 * 3 +
              596,
            air.adapter.rd_ptr row 0, air.adapter.rs1_ptr row 0, air.adapter.rs2_ptr row 0, 1, 0, 0, 0])]

      lemma constrain_program_interactions
        (air : Valid_VmAirWrapper_divrem F ExtF)
        (h : VmAirWrapper_divrem.extraction.constrain_interactions air)
      :
        air.buses ProgramBus = (List.range (air.last_row + 1)).flatMap (λ row => programBus_row air row)
      := by
        unfold VmAirWrapper_divrem.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def bitwiseBus_row (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.signed row 0,
          [2 * (air.core.b_3 row 0 - air.core.b_sign row 0 * 128),
            2 * (air.core.c_3 row 0 - air.core.c_sign row 0 * 128), 0, 0]),
        (air.core.valid_and_not_special_case row 0, [air.core.lt_diff row 0 - 1, 0, 0, 0])]

      lemma constrain_bitwise_interactions
        (air : Valid_VmAirWrapper_divrem F ExtF)
        (h : VmAirWrapper_divrem.extraction.constrain_interactions air)
      :
        air.buses BitwiseBus = (List.range (air.last_row + 1)).flatMap (λ row => bitwiseBus_row air row)
      := by
        unfold VmAirWrapper_divrem.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
      def rangeTupleCheckerBus_row (air : Valid_VmAirWrapper_divrem F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0, [air.core.q_0 row 0, air.core.carry row 0 0]),
        (air.core.is_valid row 0, [air.core.q_1 row 0, air.core.carry row 0 1]),
        (air.core.is_valid row 0, [air.core.q_2 row 0, air.core.carry row 0 2]),
        (air.core.is_valid row 0, [air.core.q_3 row 0, air.core.carry row 0 3]),
        (air.core.is_valid row 0, [air.core.r_0 row 0, air.core.carry_ext row 0 0]),
        (air.core.is_valid row 0, [air.core.r_1 row 0, air.core.carry_ext row 0 1]),
        (air.core.is_valid row 0, [air.core.r_2 row 0, air.core.carry_ext row 0 2]),
        (air.core.is_valid row 0, [air.core.r_3 row 0, air.core.carry_ext row 0 3])]

      lemma constrain_rangeTupleChecker_interactions
        (air : Valid_VmAirWrapper_divrem F ExtF)
        (h : VmAirWrapper_divrem.extraction.constrain_interactions air)
      :
        air.buses RangeTupleCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeTupleCheckerBus_row air row)
      := by
        unfold VmAirWrapper_divrem.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      def constrain_interactions (air : Valid_VmAirWrapper_divrem F ExtF) : Prop :=
      air.buses = fun index ↦
      if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
      else if index = MemoryBus then (List.range (air.last_row + 1)).flatMap (memoryBus_row air)
      else if index = RangeCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeCheckerBus_row air)
      else if index = ProgramBus then (List.range (air.last_row + 1)).flatMap (programBus_row air)
      else if index = BitwiseBus then (List.range (air.last_row + 1)).flatMap (bitwiseBus_row air)
      else if index = RangeTupleCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeTupleCheckerBus_row air)
      else []

      @[VmAirWrapper_divrem_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VmAirWrapper_divrem F ExtF)
        (h : VmAirWrapper_divrem.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold VmAirWrapper_divrem.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        exact h

    end interactions

  end constraint_simplification

  section allHold

    -- constraint list and allHold

    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        VmAirWrapper_divrem.extraction.constraint_0 air row,
        VmAirWrapper_divrem.extraction.constraint_1 air row,
        VmAirWrapper_divrem.extraction.constraint_2 air row,
        VmAirWrapper_divrem.extraction.constraint_3 air row,
        VmAirWrapper_divrem.extraction.constraint_4 air row,
        VmAirWrapper_divrem.extraction.constraint_5 air row,
        VmAirWrapper_divrem.extraction.constraint_6 air row,
        VmAirWrapper_divrem.extraction.constraint_7 air row,
        VmAirWrapper_divrem.extraction.constraint_8 air row,
        VmAirWrapper_divrem.extraction.constraint_9 air row,
        VmAirWrapper_divrem.extraction.constraint_10 air row,
        VmAirWrapper_divrem.extraction.constraint_11 air row,
        VmAirWrapper_divrem.extraction.constraint_12 air row,
        VmAirWrapper_divrem.extraction.constraint_13 air row,
        VmAirWrapper_divrem.extraction.constraint_14 air row,
        VmAirWrapper_divrem.extraction.constraint_15 air row,
        VmAirWrapper_divrem.extraction.constraint_16 air row,
        VmAirWrapper_divrem.extraction.constraint_17 air row,
        VmAirWrapper_divrem.extraction.constraint_18 air row,
        VmAirWrapper_divrem.extraction.constraint_19 air row,
        VmAirWrapper_divrem.extraction.constraint_20 air row,
        VmAirWrapper_divrem.extraction.constraint_21 air row,
        VmAirWrapper_divrem.extraction.constraint_22 air row,
        VmAirWrapper_divrem.extraction.constraint_23 air row,
        VmAirWrapper_divrem.extraction.constraint_24 air row,
        VmAirWrapper_divrem.extraction.constraint_25 air row,
        VmAirWrapper_divrem.extraction.constraint_26 air row,
        VmAirWrapper_divrem.extraction.constraint_27 air row,
        VmAirWrapper_divrem.extraction.constraint_28 air row,
        VmAirWrapper_divrem.extraction.constraint_29 air row,
        VmAirWrapper_divrem.extraction.constraint_30 air row,
        VmAirWrapper_divrem.extraction.constraint_31 air row,
        VmAirWrapper_divrem.extraction.constraint_32 air row,
        VmAirWrapper_divrem.extraction.constraint_33 air row,
        VmAirWrapper_divrem.extraction.constraint_34 air row,
        VmAirWrapper_divrem.extraction.constraint_35 air row,
        VmAirWrapper_divrem.extraction.constraint_36 air row,
        VmAirWrapper_divrem.extraction.constraint_37 air row,
        VmAirWrapper_divrem.extraction.constraint_38 air row,
        VmAirWrapper_divrem.extraction.constraint_39 air row,
        VmAirWrapper_divrem.extraction.constraint_40 air row,
        VmAirWrapper_divrem.extraction.constraint_41 air row,
        VmAirWrapper_divrem.extraction.constraint_42 air row,
        VmAirWrapper_divrem.extraction.constraint_43 air row,
        VmAirWrapper_divrem.extraction.constraint_44 air row,
        VmAirWrapper_divrem.extraction.constraint_45 air row,
        VmAirWrapper_divrem.extraction.constraint_46 air row,
        VmAirWrapper_divrem.extraction.constraint_47 air row,
        VmAirWrapper_divrem.extraction.constraint_48 air row,
        VmAirWrapper_divrem.extraction.constraint_49 air row,
        VmAirWrapper_divrem.extraction.constraint_50 air row,
        VmAirWrapper_divrem.extraction.constraint_51 air row,
        VmAirWrapper_divrem.extraction.constraint_52 air row,
        VmAirWrapper_divrem.extraction.constraint_53 air row,
        VmAirWrapper_divrem.extraction.constraint_54 air row,
        VmAirWrapper_divrem.extraction.constraint_55 air row,
        VmAirWrapper_divrem.extraction.constraint_56 air row,
        VmAirWrapper_divrem.extraction.constraint_57 air row,
        VmAirWrapper_divrem.extraction.constraint_58 air row,
        VmAirWrapper_divrem.extraction.constraint_59 air row,
        VmAirWrapper_divrem.extraction.constraint_60 air row,
        VmAirWrapper_divrem.extraction.constraint_61 air row,
        VmAirWrapper_divrem.extraction.constraint_62 air row,
        VmAirWrapper_divrem.extraction.constraint_63 air row,
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      VmAirWrapper_divrem.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF)
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
        constraint_25 air row,
        constraint_26 air row,
        constraint_27 air row,
        constraint_28 air row,
        constraint_29 air row,
        constraint_30 air row,
        constraint_31 air row,
        constraint_32 air row,
        constraint_33 air row,
        constraint_34 air row,
        constraint_35 air row,
        constraint_36 air row,
        constraint_37 air row,
        constraint_38 air row,
        constraint_39 air row,
        constraint_40 air row,
        constraint_41 air row,
        constraint_42 air row,
        constraint_43 air row,
        constraint_44 air row,
        constraint_45 air row,
        constraint_46 air row,
        constraint_47 air row,
        constraint_48 air row,
        constraint_49 air row,
        constraint_50 air row,
        constraint_51 air row,
        constraint_52 air row,
        constraint_53 air row,
        constraint_54 air row,
        constraint_55 air row,
        constraint_56 air row,
        constraint_57 air row,
        constraint_58 air row,
        constraint_59 air row,
        constraint_60 air row,
        constraint_61 air row,
        constraint_62 air row,
        constraint_63 air row
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold VmAirWrapper_divrem.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  VmAirWrapper_divrem_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

    lemma single_op
      (air : Valid_VmAirWrapper_divrem FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
    :
      let is_div := air.core.opcode_div_flag row 0
      let is_divu := air.core.opcode_divu_flag row 0
      let is_rem := air.core.opcode_rem_flag row 0
      let is_remu := air.core.opcode_remu_flag row 0
      (is_div = 1 → is_divu = 0 ∧ is_rem = 0 ∧ is_remu = 0) ∧
      (is_divu = 1 → is_div = 0 ∧ is_rem = 0 ∧ is_remu = 0) ∧
      (is_rem = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_remu = 0) ∧
      (is_remu = 1 → is_div = 0 ∧ is_divu = 0 ∧ is_rem = 0)
    := by
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, h3, h4, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at *
      rw [← DivRemCoreAir_4_8.is_valid_def] at h4
      grind (splits := 14)

    lemma op_from_opcode
      (air : Valid_VmAirWrapper_divrem FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
      (is_valid : air.core.is_valid row 0 = 1)
    :
      let is_div := air.core.opcode_div_flag row 0
      let is_divu := air.core.opcode_divu_flag row 0
      let is_rem := air.core.opcode_rem_flag row 0
      let is_remu := air.core.opcode_remu_flag row 0
      ((air.core.ctx row 0).instruction.opcode = 596 → is_div = 1) ∧
      ((air.core.ctx row 0).instruction.opcode = 597 → is_divu = 1) ∧
      ((air.core.ctx row 0).instruction.opcode = 598 → is_rem = 1) ∧
      ((air.core.ctx row 0).instruction.opcode = 599 → is_remu = 1)
    := by
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, h3, h4, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at *
      rw [← DivRemCoreAir_4_8.is_valid_def] at *
      rw [← DivRemCoreAir_4_8.ctx_opcode_def]
      grind

    lemma opcode_bounds
      (air : Valid_VmAirWrapper_divrem FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
      (is_valid : air.core.is_valid row 0 = 1)
    :
      (air.core.ctx row 0).instruction.opcode = 596 ∨
      (air.core.ctx row 0).instruction.opcode = 597 ∨
      (air.core.ctx row 0).instruction.opcode = 598 ∨
      (air.core.ctx row 0).instruction.opcode = 599
    := by
      have ⟨ sop1, sop2, sop3, sop4 ⟩ := single_op air row valid_row cstrs
      rw [← DivRemCoreAir_4_8.ctx_opcode_def]
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, h3, h4, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_divrem_constraint_and_interaction_simplification] at *
      rw [← DivRemCoreAir_4_8.is_valid_def] at *
      grind

  end properties

  section bus_entries

    lemma executionBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_divrem FBB ExtF} {row : ℕ}
      (h_in : entry ∈ executionBus_row air row)
    :
      entry.2.length = Interaction.ExecutionBusEntryInstance.data_length
    := by
      unfold executionBus_row at *; simp_all
      grind

    @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
    def _executionBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.ExecutionBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ executionBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (executionBus_row_length x.2)))
          (executionBus_row air row).attach
      List.map Interaction.ExecutionBusEntryInstance.deserialise vectorised_row

    lemma memoryBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_divrem FBB ExtF} {row : ℕ}
      (h_in : entry ∈ memoryBus_row air row)
    :
      entry.2.length = Interaction.MemoryBusEntryInstance.data_length
    := by
      unfold memoryBus_row at *; simp_all
      grind (ematch := 8)

    @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
    def _memoryBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.MemoryBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ memoryBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (memoryBus_row_length x.2)))
          (memoryBus_row air row).attach
      List.map Interaction.MemoryBusEntryInstance.deserialise vectorised_row

    lemma rangeCheckerBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_divrem FBB ExtF} {row : ℕ}
      (h_in : entry ∈ rangeCheckerBus_row air row)
    :
      entry.2.length = Interaction.RangeCheckerBusEntryInstance.data_length
    := by
      unfold rangeCheckerBus_row at *; simp_all
      grind (splits := 10)

    @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
    def _rangeCheckerBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.RangeCheckerBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ rangeCheckerBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (rangeCheckerBus_row_length x.2)))
          (rangeCheckerBus_row air row).attach
      List.map Interaction.RangeCheckerBusEntryInstance.deserialise vectorised_row

    lemma programBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_divrem FBB ExtF} {row : ℕ}
      (h_in : entry ∈ programBus_row air row)
    :
      entry.2.length = Interaction.ProgramBusEntryInstance.data_length
    := by
      unfold programBus_row at *; simp_all

    @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
    def _programBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.ProgramBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ programBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (programBus_row_length x.2)))
          (programBus_row air row).attach
      List.map Interaction.ProgramBusEntryInstance.deserialise vectorised_row

    lemma rangeTupleCheckerBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_divrem FBB ExtF} {row : ℕ}
      (h_in : entry ∈ rangeTupleCheckerBus_row air row)
    :
      entry.2.length = Interaction.RangeTupleCheckerBusEntryInstance.data_length
    := by
      unfold rangeTupleCheckerBus_row at *; simp_all
      grind

    @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
    def _rangeTupleCheckerBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.RangeTupleCheckerBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ rangeTupleCheckerBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (rangeTupleCheckerBus_row_length x.2)))
          (rangeTupleCheckerBus_row air row).attach
      List.map Interaction.RangeTupleCheckerBusEntryInstance.deserialise vectorised_row

    lemma bitwiseBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_divrem FBB ExtF} {row : ℕ}
      (h_in : entry ∈ bitwiseBus_row air row)
    :
      entry.2.length = Interaction.BitwiseBusEntryInstance.data_length
    := by
      unfold bitwiseBus_row at *; simp_all
      grind

    @[VmAirWrapper_divrem_constraint_and_interaction_simplification]
    def _bitwiseBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ) :=
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
    def axioms [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
      List.Forall id (rowData.map (Interaction.BusEntry.axioms FBB))

    @[simp]
    def propertiesToAssume [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
      List.Forall id (rowData.map (Interaction.BusEntry.assume FBB))

    @[simp]
    def propertiesToAssert [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
      List.Forall id (rowData.map (Interaction.BusEntry.assert FBB))

    @[simp]
    def busRow [Field ExtF] (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ)
    : List (FBB × List FBB) :=
      executionBus_row air row ++
      memoryBus_row air row ++
      rangeCheckerBus_row air row ++
      programBus_row air row ++
      rangeTupleCheckerBus_row air row ++
      bitwiseBus_row air row

    @[simp]
    def axiomsPerRow [Field ExtF]
      (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ)
    : Prop :=
      axioms (_executionBus_row air row) ∧
      axioms (_memoryBus_row air row) ∧
      axioms (_rangeCheckerBus_row air row) ∧
      axioms (_programBus_row air row) ∧
      axioms (_rangeTupleCheckerBus_row air row) ∧
      axioms (_bitwiseBus_row air row)

    @[simp]
    def wf_propertiesToAssumePerRow [Field ExtF] (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ)
    : Prop :=
      propertiesToAssume (_executionBus_row air row) ∧
      propertiesToAssume (_memoryBus_row air row) ∧
      propertiesToAssume (_rangeCheckerBus_row air row) ∧
      propertiesToAssume (_programBus_row air row) ∧
      propertiesToAssume (_rangeTupleCheckerBus_row air row) ∧
      propertiesToAssume (_bitwiseBus_row air row)

    @[simp]
    def wf_propertiesToAssertPerRow [Field ExtF] (air : Valid_VmAirWrapper_divrem FBB ExtF) (row : ℕ)
    : Prop :=
      propertiesToAssert (_executionBus_row air row) ∧
      propertiesToAssert (_memoryBus_row air row) ∧
      propertiesToAssert (_rangeCheckerBus_row air row) ∧
      propertiesToAssert (_programBus_row air row) ∧
      propertiesToAssert (_rangeTupleCheckerBus_row air row) ∧
      propertiesToAssert (_bitwiseBus_row air row)

  end bus_entries

end VmAirWrapper_divrem.constraints
