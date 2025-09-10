import OpenvmFv.Airs.Alu.VmAirWrapper_shift
import OpenvmFv.Extraction.VmAirWrapper_shift
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace VmAirWrapper_shift.constraints

  section constraint_simplification

    -- Note: `air` and `row` are not included as section variables
    --       so that the file can still be used with `sorry`
    --       during the extraction process
    --       Additionally, the proofs are split into more stages
    --       than required so that it can be easily checked that all
    --       intending folding is occuring

    variable [Field F] [Field ExtF]

    section row_constraints

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_sll_flag row 0 = 0 ∨ air.core.opcode_sll_flag row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_0_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_0 air row ↔ constraint_0 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_srl_flag row 0 = 0 ∨ air.core.opcode_srl_flag row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_1_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_1 air row ↔ constraint_1 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_sra_flag row 0 = 0 ∨ air.core.opcode_sra_flag row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_2_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_2 air row ↔ constraint_2 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_3_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_3 air row ↔ constraint_3 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
         air.core.bit_shift_marker_0 row 0 = 0 ∨ air.core.bit_shift_marker_0 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_4_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_4 air row ↔ constraint_4 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_0 row 0 = 0 ∨ air.core.bit_multiplier_left row 0 = air.core.opcode_sll_flag row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_5_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_5 air row ↔ constraint_5 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_0 row 0 = 0 ∨ air.core.bit_multiplier_right row 0 = air.core.right_shift row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_6_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_6 air row ↔ constraint_6 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_1 row 0 = 0 ∨ air.core.bit_shift_marker_1 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_7_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_7 air row ↔ constraint_7 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_1 row 0 = 0 ∨ air.core.bit_multiplier_left row 0 = 2 * air.core.opcode_sll_flag row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_8_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_8 air row ↔ constraint_8 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_1 row 0 = 0 ∨ air.core.bit_multiplier_right row 0 = 2 * air.core.right_shift row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_9_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_9 air row ↔ constraint_9 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_2 row 0 = 0 ∨ air.core.bit_shift_marker_2 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_10_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_10 air row ↔ constraint_10 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_2 row 0 = 0 ∨ air.core.bit_multiplier_left row 0 = 4 * air.core.opcode_sll_flag row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_11_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_11 air row ↔ constraint_11 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_2 row 0 = 0 ∨ air.core.bit_multiplier_right row 0 = 4 * air.core.right_shift row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_12_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_12 air row ↔ constraint_12 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_3 row 0 = 0 ∨ air.core.bit_shift_marker_3 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_13_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_13 air row ↔ constraint_13 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_3 row 0 = 0 ∨ air.core.bit_multiplier_left row 0 = 8 * air.core.opcode_sll_flag row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_14_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_14 air row ↔ constraint_14 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_3 row 0 = 0 ∨ air.core.bit_multiplier_right row 0 = 8 * air.core.right_shift row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_15_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_15 air row ↔ constraint_15 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_4 row 0 = 0 ∨ air.core.bit_shift_marker_4 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_16_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_16 air row ↔ constraint_16 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_4 row 0 = 0 ∨ air.core.bit_multiplier_left row 0 = 16 * air.core.opcode_sll_flag row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_17_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_17 air row ↔ constraint_17 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_4 row 0 = 0 ∨ air.core.bit_multiplier_right row 0 = 16 * air.core.right_shift row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_18_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_18 air row ↔ constraint_18 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_5 row 0 = 0 ∨ air.core.bit_shift_marker_5 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_19_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_19 air row ↔ constraint_19 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_5 row 0 = 0 ∨ air.core.bit_multiplier_left row 0 = 32 * air.core.opcode_sll_flag row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_20_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_20 air row ↔ constraint_20 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_5 row 0 = 0 ∨ air.core.bit_multiplier_right row 0 = 32 * air.core.right_shift row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_21_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_21 air row ↔ constraint_21 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_6 row 0 = 0 ∨ air.core.bit_shift_marker_6 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_22_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_22 air row ↔ constraint_22 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_6 row 0 = 0 ∨ air.core.bit_multiplier_left row 0 = 64 * air.core.opcode_sll_flag row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_23_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_23 air row ↔ constraint_23 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_6 row 0 = 0 ∨ air.core.bit_multiplier_right row 0 = 64 * air.core.right_shift row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_24_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_24 air row ↔ constraint_24 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_25 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_7 row 0 = 0 ∨ air.core.bit_shift_marker_7 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_25_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_25 air row ↔ constraint_25 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_26 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_7 row 0 = 0 ∨ air.core.bit_multiplier_left row 0 = 128 * air.core.opcode_sll_flag row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_26_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_26 air row ↔ constraint_26 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_27 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.bit_shift_marker_7 row 0 = 0 ∨ air.core.bit_multiplier_right row 0 = 128 * air.core.right_shift row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_27_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_27 air row ↔ constraint_27 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_28 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.bit_marker_sum row 0 7 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_28_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_28 air row ↔ constraint_28 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_29 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_0 row 0 = 0 ∨ air.core.limb_shift_marker_0 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_29_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_29 air row ↔ constraint_29 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_30 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_0 row 0 = 0 ∨
    air.core.a_0 row 0 * air.core.opcode_sll_flag row 0 = air.core.expected_a_left row 0 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_30_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_30 air row ↔ constraint_30 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_31 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_0 row 0 = 0 ∨
    air.core.a_0 row 0 * air.core.bit_multiplier_right row 0 = air.core.expected_a_right row 0 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_31_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_31 air row ↔ constraint_31 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_32 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_0 row 0 = 0 ∨
    air.core.a_1 row 0 * air.core.opcode_sll_flag row 0 = air.core.expected_a_left row 0 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_32_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_32 air row ↔ constraint_32 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_33 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_0 row 0 = 0 ∨
    air.core.a_1 row 0 * air.core.bit_multiplier_right row 0 = air.core.expected_a_right row 0 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_33_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_33 air row ↔ constraint_33 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_34 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_0 row 0 = 0 ∨
    air.core.a_2 row 0 * air.core.opcode_sll_flag row 0 = air.core.expected_a_left row 0 2

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_34_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_34 air row ↔ constraint_34 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_35 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_0 row 0 = 0 ∨
    air.core.a_2 row 0 * air.core.bit_multiplier_right row 0 = air.core.expected_a_right row 0 2

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_35_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_35 air row ↔ constraint_35 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_36 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_0 row 0 = 0 ∨
    air.core.a_3 row 0 * air.core.opcode_sll_flag row 0 = air.core.expected_a_left row 0 3

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_36_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_36 air row ↔ constraint_36 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_37 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_0 row 0 = 0 ∨
    air.core.a_3 row 0 * air.core.bit_multiplier_right row 0 = air.core.expected_a_right row 0 3

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_37_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_37 air row ↔ constraint_37 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_38 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_1 row 0 = 0 ∨ air.core.limb_shift_marker_1 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_38_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_38 air row ↔ constraint_38 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_39 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_1 row 0 = 0 ∨ air.core.a_0 row 0 = 0 ∨ air.core.opcode_sll_flag row 0 = 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_39_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_39 air row ↔ constraint_39 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_40 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_1 row 0 = 0 ∨
    air.core.a_0 row 0 * air.core.bit_multiplier_right row 0 = air.core.expected_a_right row 0 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_40_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_40 air row ↔ constraint_40 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_41 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_1 row 0 = 0 ∨
    air.core.a_1 row 0 * air.core.opcode_sll_flag row 0 = air.core.expected_a_left row 0 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_41_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_41 air row ↔ constraint_41 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_42 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_1 row 0 = 0 ∨
    air.core.a_1 row 0 * air.core.bit_multiplier_right row 0 = air.core.expected_a_right row 0 2

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_42_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_42 air row ↔ constraint_42 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_43 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_1 row 0 = 0 ∨
    air.core.a_2 row 0 * air.core.opcode_sll_flag row 0 = air.core.expected_a_left row 0 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_43_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_43 air row ↔ constraint_43 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_44 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_1 row 0 = 0 ∨
    air.core.a_2 row 0 * air.core.bit_multiplier_right row 0 = air.core.expected_a_right row 0 3

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_44_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_44 air row ↔ constraint_44 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_45 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_1 row 0 = 0 ∨
    air.core.a_3 row 0 * air.core.opcode_sll_flag row 0 = air.core.expected_a_left row 0 2

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_45_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_45 air row ↔ constraint_45 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_46 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_1 row 0 = 0 ∨
    air.core.a_3 row 0 * air.core.right_shift row 0 = air.core.b_sign_shifted row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_46_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_46 air row ↔ constraint_46 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_47 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_2 row 0 = 0 ∨ air.core.limb_shift_marker_2 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_47_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_47 air row ↔ constraint_47 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_48 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_2 row 0 = 0 ∨ air.core.a_0 row 0 = 0 ∨ air.core.opcode_sll_flag row 0 = 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_48_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_48 air row ↔ constraint_48 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_49 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_2 row 0 = 0 ∨
    air.core.a_0 row 0 * air.core.bit_multiplier_right row 0 = air.core.expected_a_right row 0 2

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_49_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_49 air row ↔ constraint_49 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_50 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_2 row 0 = 0 ∨ air.core.a_1 row 0 = 0 ∨ air.core.opcode_sll_flag row 0 = 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_50_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_50 air row ↔ constraint_50 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_51 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_2 row 0 = 0 ∨
    air.core.a_1 row 0 * air.core.bit_multiplier_right row 0 = air.core.expected_a_right row 0 3

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_51_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_51 air row ↔ constraint_51 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_52 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_2 row 0 = 0 ∨
    air.core.a_2 row 0 * air.core.opcode_sll_flag row 0 = air.core.expected_a_left row 0 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_52_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_52 air row ↔ constraint_52 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_53 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_2 row 0 = 0 ∨
    air.core.a_2 row 0 * air.core.right_shift row 0 = air.core.b_sign_shifted row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_53_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_53 air row ↔ constraint_53 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_54 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_2 row 0 = 0 ∨
  air.core.a_3 row 0 * air.core.opcode_sll_flag row 0 = air.core.expected_a_left row 0 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_54_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_54 air row ↔ constraint_54 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_55 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_2 row 0 = 0 ∨
    air.core.a_3 row 0 * air.core.right_shift row 0 = air.core.b_sign_shifted row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_55_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_55 air row ↔ constraint_55 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_56 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_3 row 0 = 0 ∨ air.core.limb_shift_marker_3 row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_56_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_56 air row ↔ constraint_56 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_57 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_3 row 0 = 0 ∨ air.core.a_0 row 0 = 0 ∨ air.core.opcode_sll_flag row 0 = 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_57_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_57 air row ↔ constraint_57 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_58 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_3 row 0 = 0 ∨
    air.core.a_0 row 0 * air.core.bit_multiplier_right row 0 = air.core.expected_a_right row 0 3

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_58_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_58 air row ↔ constraint_58 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_59 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_3 row 0 = 0 ∨ air.core.a_1 row 0 = 0 ∨ air.core.opcode_sll_flag row 0 = 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_59_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_59 air row ↔ constraint_59 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_60 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_3 row 0 = 0 ∨
    air.core.a_1 row 0 * air.core.right_shift row 0 = air.core.b_sign_shifted row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_60_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_60 air row ↔ constraint_60 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_61 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_3 row 0 = 0 ∨ air.core.a_2 row 0 = 0 ∨ air.core.opcode_sll_flag row 0 = 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_61_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_61 air row ↔ constraint_61 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_62 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_3 row 0 = 0 ∨
    air.core.a_2 row 0 * air.core.right_shift row 0 = air.core.b_sign_shifted row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_62_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_62 air row ↔ constraint_62 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_63 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_3 row 0 = 0 ∨
  air.core.a_3 row 0 * air.core.opcode_sll_flag row 0 = air.core.expected_a_left row 0 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_63_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_63 air row ↔ constraint_63 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_64 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.limb_shift_marker_3 row 0 = 0 ∨
    air.core.a_3 row 0 * air.core.right_shift row 0 = air.core.b_sign_shifted row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_64_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_64 air row ↔ constraint_64 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_65 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.core.limb_shift_marker_0 row 0 + air.core.limb_shift_marker_1 row 0 + air.core.limb_shift_marker_2 row 0 +
        air.core.limb_shift_marker_3 row 0 =
      1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_65_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_65 air row ↔ constraint_65 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_66 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.b_sign row 0 = 0 ∨ air.core.b_sign row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_66_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_66 air row ↔ constraint_66 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_67 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        1 = air.core.opcode_sra_flag row 0 ∨ air.core.b_sign row 0 = 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_67_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_67 air row ↔ constraint_67 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_68 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 0 ∨ air.adapter.rs2_as row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_68_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_68 air row ↔ constraint_68 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_69 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        1 = air.adapter.rs2_as row 0 ∨ air.adapter.rs2 row 0 = air.rs2_imm row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_69_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_69 air row ↔ constraint_69 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_70 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        1 = air.adapter.rs2_as row 0 ∨ air.rs2_sign row 0 = air.rs2_limbs row 0 3

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_70_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_70 air row ↔ constraint_70 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_71 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        1 = air.adapter.rs2_as row 0 ∨ air.core.c_2 row 0 = 0 ∨ 255 = air.core.c_2 row 0

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_71_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_71 air row ↔ constraint_71 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_72 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 - air.adapter.reads_aux_0.base.prev_timestamp row 0 - 1 =
      air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_72_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_72 air row ↔ constraint_72 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_73 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_73_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_73 air row ↔ constraint_73 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_74 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 + 1 - air.adapter.reads_aux_1.base.prev_timestamp row 0 - 1 =
      air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_74_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_74 air row ↔ constraint_74 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def constraint_75 (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 + 2 - air.adapter.writes_aux.base.prev_timestamp row 0 - 1 =
      air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_shift_air_simplification]
      lemma constraint_75_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ)
      : VmAirWrapper_shift.extraction.constraint_75 air row ↔ constraint_75 air row := by
        apply Iff.intro
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification]
          exact h
        . intro h
          simp [openvm_encapsulation, VmAirWrapper_shift_constraint_and_interaction_simplification]
          simp only [VmAirWrapper_shift_constraint_and_interaction_simplification] at h
          exact h

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def executionBus_row (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.core.is_valid row 0, [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0]),
        (air.core.is_valid row 0, [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3])]

      lemma constrain_execution_interactions
        (air : Valid_VmAirWrapper_shift F ExtF)
        (h : VmAirWrapper_shift.extraction.constrain_interactions air)
      :
        air.buses ExecutionBus = (List.range (air.last_row + 1)).flatMap (λ row => executionBus_row air row)
      := by
        unfold VmAirWrapper_shift.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def memoryBus_row (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : List (F × List F) :=
        [(2013265920 * air.core.is_valid row 0,
          [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0,
            air.adapter.reads_aux_0.base.prev_timestamp row 0]),
        (air.core.is_valid row 0,
          [1, air.adapter.rs1_ptr row 0, air.core.b_0 row 0, air.core.b_1 row 0, air.core.b_2 row 0, air.core.b_3 row 0,
            air.adapter.from_state.timestamp row 0]),
        (2013265920 * air.adapter.rs2_as row 0,
          [air.adapter.rs2_as row 0, air.adapter.rs2 row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0,
            air.core.c_3 row 0, air.adapter.reads_aux_1.base.prev_timestamp row 0]),
        (air.adapter.rs2_as row 0,
          [air.adapter.rs2_as row 0, air.adapter.rs2 row 0, air.core.c_0 row 0, air.core.c_1 row 0, air.core.c_2 row 0,
            air.core.c_3 row 0, air.adapter.from_state.timestamp row 0 + 1]),
        (2013265920 * air.core.is_valid row 0,
          [1, air.adapter.rd_ptr row 0, air.adapter.writes_aux.prev_data_0 row 0,
            air.adapter.writes_aux.prev_data_1 row 0, air.adapter.writes_aux.prev_data_2 row 0,
            air.adapter.writes_aux.prev_data_3 row 0, air.adapter.writes_aux.base.prev_timestamp row 0]),
        (air.core.is_valid row 0,
          [1, air.adapter.rd_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0,
            air.adapter.from_state.timestamp row 0 + 2])]

      lemma constrain_memory_interactions
        (air : Valid_VmAirWrapper_shift F ExtF)
        (h : VmAirWrapper_shift.extraction.constrain_interactions air)
      :
        air.buses MemoryBus = (List.range (air.last_row + 1)).flatMap (λ row => memoryBus_row air row)
      := by
        unfold VmAirWrapper_shift.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def rangeBus_row (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
          [(air.core.c_0 row 0 - air.core.limb_shift row 0 3 * 8 - air.core.bit_shift row 0) * 1950351361, 3]),
        (air.core.is_valid row 0, [air.core.bit_shift_carry_0 row 0, air.core.bit_shift row 0]),
        (air.core.is_valid row 0, [air.core.bit_shift_carry_1 row 0, air.core.bit_shift row 0]),
        (air.core.is_valid row 0, [air.core.bit_shift_carry_2 row 0, air.core.bit_shift row 0]),
        (air.core.is_valid row 0, [air.core.bit_shift_carry_3 row 0, air.core.bit_shift row 0]),
        (air.core.is_valid row 0, [air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.adapter.rs2_as row 0, [air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.adapter.rs2_as row 0, [air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.core.is_valid row 0, [air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12])]

      lemma constrain_range_interactions
        (air : Valid_VmAirWrapper_shift F ExtF)
        (h : VmAirWrapper_shift.extraction.constrain_interactions air)
      :
        air.buses RangeCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeBus_row air row)
      := by
        unfold VmAirWrapper_shift.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def readInstructionBus_row (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
          [air.adapter.from_state.pc row 0, (air.core.ctx row 0).instruction.opcode, air.adapter.rd_ptr row 0,
            air.adapter.rs1_ptr row 0, air.adapter.rs2 row 0, 1, air.adapter.rs2_as row 0, 0, 0])]

      lemma constrain_readInstruction_interactions
        (air : Valid_VmAirWrapper_shift F ExtF)
        (h : VmAirWrapper_shift.extraction.constrain_interactions air)
      :
        air.buses ReadInstructionBus = (List.range (air.last_row + 1)).flatMap (λ row => readInstructionBus_row air row)
      := by
        unfold VmAirWrapper_shift.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      @[VmAirWrapper_shift_constraint_and_interaction_simplification]
      def bitwiseBus_row (air : Valid_VmAirWrapper_shift F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.opcode_sra_flag row 0,
          [air.core.b_3 row 0, 128, air.core.b_3 row 0 + 128 - 2 * (air.core.b_sign row 0 * 128), 1]),
        (air.core.is_valid row 0, [air.core.a_0 row 0, air.core.a_1 row 0, 0, 0]),
        (air.core.is_valid row 0, [air.core.a_2 row 0, air.core.a_3 row 0, 0, 0]),
        (air.core.is_valid row 0 - air.adapter.rs2_as row 0, [air.core.c_0 row 0, air.core.c_1 row 0, 0, 0])]

      lemma constrain_bitwise_interactions
        (air : Valid_VmAirWrapper_shift F ExtF)
        (h : VmAirWrapper_shift.extraction.constrain_interactions air)
      :
        air.buses BitwiseBus = (List.range (air.last_row + 1)).flatMap (λ row => bitwiseBus_row air row)
      := by
        unfold VmAirWrapper_shift.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      def constrain_interactions (air : Valid_VmAirWrapper_shift F ExtF) : Prop :=
        air.buses = fun index ↦
        if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
        else if index = MemoryBus then (List.range (air.last_row + 1)).flatMap (memoryBus_row air)
        else if index = RangeCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeBus_row air)
        else if index = ReadInstructionBus then (List.range (air.last_row + 1)).flatMap (readInstructionBus_row air)
        else if index = BitwiseBus then (List.range (air.last_row + 1)).flatMap (bitwiseBus_row air)
        else []

      @[VmAirWrapper_shift_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VmAirWrapper_shift F ExtF)
        (h : VmAirWrapper_shift.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold VmAirWrapper_shift.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        exact h

    end interactions

  end constraint_simplification

  section allHold

    -- TODO have extractor generate this and put in extraction file
    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_shift FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        VmAirWrapper_shift.extraction.constraint_0 air row,
        VmAirWrapper_shift.extraction.constraint_1 air row,
        VmAirWrapper_shift.extraction.constraint_2 air row,
        VmAirWrapper_shift.extraction.constraint_3 air row,
        VmAirWrapper_shift.extraction.constraint_4 air row,
        VmAirWrapper_shift.extraction.constraint_5 air row,
        VmAirWrapper_shift.extraction.constraint_6 air row,
        VmAirWrapper_shift.extraction.constraint_7 air row,
        VmAirWrapper_shift.extraction.constraint_8 air row,
        VmAirWrapper_shift.extraction.constraint_9 air row,
        VmAirWrapper_shift.extraction.constraint_10 air row,
        VmAirWrapper_shift.extraction.constraint_11 air row,
        VmAirWrapper_shift.extraction.constraint_12 air row,
        VmAirWrapper_shift.extraction.constraint_13 air row,
        VmAirWrapper_shift.extraction.constraint_14 air row,
        VmAirWrapper_shift.extraction.constraint_15 air row,
        VmAirWrapper_shift.extraction.constraint_16 air row,
        VmAirWrapper_shift.extraction.constraint_17 air row,
        VmAirWrapper_shift.extraction.constraint_18 air row,
        VmAirWrapper_shift.extraction.constraint_19 air row,
        VmAirWrapper_shift.extraction.constraint_20 air row,
        VmAirWrapper_shift.extraction.constraint_21 air row,
        VmAirWrapper_shift.extraction.constraint_22 air row,
        VmAirWrapper_shift.extraction.constraint_23 air row,
        VmAirWrapper_shift.extraction.constraint_24 air row,
        VmAirWrapper_shift.extraction.constraint_25 air row,
        VmAirWrapper_shift.extraction.constraint_26 air row,
        VmAirWrapper_shift.extraction.constraint_27 air row,
        VmAirWrapper_shift.extraction.constraint_28 air row,
        VmAirWrapper_shift.extraction.constraint_29 air row,
        VmAirWrapper_shift.extraction.constraint_30 air row,
        VmAirWrapper_shift.extraction.constraint_31 air row,
        VmAirWrapper_shift.extraction.constraint_32 air row,
        VmAirWrapper_shift.extraction.constraint_33 air row,
        VmAirWrapper_shift.extraction.constraint_34 air row,
        VmAirWrapper_shift.extraction.constraint_35 air row,
        VmAirWrapper_shift.extraction.constraint_36 air row,
        VmAirWrapper_shift.extraction.constraint_37 air row,
        VmAirWrapper_shift.extraction.constraint_38 air row,
        VmAirWrapper_shift.extraction.constraint_39 air row,
        VmAirWrapper_shift.extraction.constraint_40 air row,
        VmAirWrapper_shift.extraction.constraint_41 air row,
        VmAirWrapper_shift.extraction.constraint_42 air row,
        VmAirWrapper_shift.extraction.constraint_43 air row,
        VmAirWrapper_shift.extraction.constraint_44 air row,
        VmAirWrapper_shift.extraction.constraint_45 air row,
        VmAirWrapper_shift.extraction.constraint_46 air row,
        VmAirWrapper_shift.extraction.constraint_47 air row,
        VmAirWrapper_shift.extraction.constraint_48 air row,
        VmAirWrapper_shift.extraction.constraint_49 air row,
        VmAirWrapper_shift.extraction.constraint_50 air row,
        VmAirWrapper_shift.extraction.constraint_51 air row,
        VmAirWrapper_shift.extraction.constraint_52 air row,
        VmAirWrapper_shift.extraction.constraint_53 air row,
        VmAirWrapper_shift.extraction.constraint_54 air row,
        VmAirWrapper_shift.extraction.constraint_55 air row,
        VmAirWrapper_shift.extraction.constraint_56 air row,
        VmAirWrapper_shift.extraction.constraint_57 air row,
        VmAirWrapper_shift.extraction.constraint_58 air row,
        VmAirWrapper_shift.extraction.constraint_59 air row,
        VmAirWrapper_shift.extraction.constraint_60 air row,
        VmAirWrapper_shift.extraction.constraint_61 air row,
        VmAirWrapper_shift.extraction.constraint_62 air row,
        VmAirWrapper_shift.extraction.constraint_63 air row,
        VmAirWrapper_shift.extraction.constraint_64 air row,
        VmAirWrapper_shift.extraction.constraint_65 air row,
        VmAirWrapper_shift.extraction.constraint_66 air row,
        VmAirWrapper_shift.extraction.constraint_67 air row,
        VmAirWrapper_shift.extraction.constraint_68 air row,
        VmAirWrapper_shift.extraction.constraint_69 air row,
        VmAirWrapper_shift.extraction.constraint_70 air row,
        VmAirWrapper_shift.extraction.constraint_71 air row,
        VmAirWrapper_shift.extraction.constraint_72 air row,
        VmAirWrapper_shift.extraction.constraint_73 air row,
        VmAirWrapper_shift.extraction.constraint_74 air row,
        VmAirWrapper_shift.extraction.constraint_75 air row,
      ]

    -- TODO have extractor generate this and put in extraction file
    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_shift FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      VmAirWrapper_shift.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_shift FBB ExtF)
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
        constraint_63 air row,
        constraint_64 air row,
        constraint_65 air row,
        constraint_66 air row,
        constraint_67 air row,
        constraint_68 air row,
        constraint_69 air row,
        constraint_70 air row,
        constraint_71 air row,
        constraint_72 air row,
        constraint_73 air row,
        constraint_74 air row,
        constraint_75 air row,
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_VmAirWrapper_shift FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_shift FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
        unfold allHold allHold_simplified
        apply Iff.and
        . unfold VmAirWrapper_shift.extraction.constrain_interactions
          simp [openvm_encapsulation]
          rfl
        . simp only [extracted_row_constraint_list,
                    row_constraint_list,
                    VmAirWrapper_shift_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

    -- lemma single_op
    --   (air : Valid_VmAirWrapper_shift FBB ExtF)
    --   (row : ℕ)
    --   (valid_row : row ≤ air.last_row)
    --   (cstrs : allHold air row valid_row)
    -- :
    --   let is_slt := air.core.opcode_slt_flag row 0
    --   let is_sltu := air.core.opcode_sltu_flag row 0
    --   (is_slt = 1 → is_sltu = 0) ∧
    --   (is_sltu = 1 → is_slt = 0)
    -- := by
    --   rw [allHold_simplified_of_allHold air row valid_row] at cstrs
    --   obtain ⟨ hint, h0, h1, h2, rest ⟩ := cstrs
    --   clear hint rest
    --   simp [VmAirWrapper_shift_constraint_and_interaction_simplification] at *
    --   rw [Valid_LessThanCoreAir_4.is_valid] at h2
    --   grind

    -- lemma op_from_opcode
    --   (air : Valid_VmAirWrapper_shift FBB ExtF)
    --   (row : ℕ)
    --   (valid_row : row ≤ air.last_row)
    --   (cstrs : allHold air row valid_row)
    --   (is_valid : air.core.is_valid row 0 = 1)
    -- :
    --   let is_slt := air.core.opcode_slt_flag row 0
    --   let is_sltu := air.core.opcode_sltu_flag row 0
    --   ((air.core.ctx row 0).instruction.opcode = 520 → is_slt = 1) ∧
    --   ((air.core.ctx row 0).instruction.opcode = 521 → is_sltu = 1)
    -- := by
    --   rw [allHold_simplified_of_allHold air row valid_row] at cstrs
    --   obtain ⟨ hint, h0, h1, h2, rest ⟩ := cstrs
    --   clear hint rest
    --   simp [VmAirWrapper_shift_constraint_and_interaction_simplification] at *
    --   rw [Valid_LessThanCoreAir_4.is_valid] at h2
    --   rw [← LessThanCoreAir_4.is_valid_def] at is_valid
    --   rw [← LessThanCoreAir_4.ctx.instruction.opcode_def]
    --   grind

    -- lemma opcode_bounds
    --   (air : Valid_VmAirWrapper_shift FBB ExtF)
    --   (row : ℕ)
    --   (valid_row : row ≤ air.last_row)
    --   (cstrs : allHold air row valid_row)
    --   (is_valid : air.core.is_valid row 0 = 1)
    -- :
    --   (air.core.ctx row 0).instruction.opcode = 520 ∨
    --   (air.core.ctx row 0).instruction.opcode = 521
    -- := by
    --   have ⟨ sop1, sop2 ⟩ := single_op air row valid_row cstrs
    --   rw [← LessThanCoreAir_4.ctx.instruction.opcode_def]
    --   rw [← LessThanCoreAir_4.is_valid_def] at is_valid
    --   rw [allHold_simplified_of_allHold air row valid_row] at cstrs
    --   obtain ⟨ hint, h0, h1, h2, rest ⟩ := cstrs
    --   clear hint rest
    --   simp [VmAirWrapper_shift_constraint_and_interaction_simplification] at *
    --   grind

  end properties

end VmAirWrapper_shift.constraints

namespace Interaction

/-- ALU-related ReadInstruction bus assumptions -/
def readInstructionBus_assumptions_Lt
  (mul _ _ rd rs1 rs2 xd rs2_as xf xg : FBB)
: Prop :=
  ¬ mul = 0 →
    -- rd and rs1 boundaries
    rd.val < 32 ∧ rs1.val < 32 ∧
    -- non-immediate rs2
    (rs2_as = 1 → rs2.val < 32) ∧
    -- immediate rs2
    (rs2_as = 0 →
      -- immediate fits 24 bits
      rs2.val < 2 ^ 24 ∧
      -- immediate is a sign-extended 12-bit value
      (BitVec.ofNat 24 rs2.val).toInt = (BitVec.ofNat 12 rs2.val).toInt) ∧
    -- unused parameters
    xd = 1 ∧ xf = 0 ∧ xg = 0

end Interaction
