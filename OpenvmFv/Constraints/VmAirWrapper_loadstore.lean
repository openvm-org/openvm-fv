import OpenvmFv.Airs.LoadStore.VmAirWrapper_loadstore
import OpenvmFv.Extraction.VmAirWrapper_loadstore
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

-- removes "environment already contains
-- 'iop.enumToBitVec' from
-- OpenvmFv.Constraints.VmAirWrapper_alu" error
import OpenvmFv.Constraints.VmAirWrapper_alu

namespace VmAirWrapper_loadstore.constraints

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
      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_0 air row ↔ constraint_0 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.flags_0 row 0 = 0 ∨ air.core.flags_0 row 0 = 1 ∨ air.core.flags_0 row 0 = 2

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_1 air row ↔ constraint_1 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.flags_1 row 0 = 0 ∨ air.core.flags_1 row 0 = 1 ∨ air.core.flags_1 row 0 = 2

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_2 air row ↔ constraint_2 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.flags_2 row 0 = 0 ∨ air.core.flags_2 row 0 = 1 ∨ air.core.flags_2 row 0 = 2

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_3 air row ↔ constraint_3 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.flags_3 row 0 = 0 ∨ air.core.flags_3 row 0 = 1 ∨ air.core.flags_3 row 0 = 2


      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_4 air row ↔ constraint_4 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.sum row 0 = 0 ∨ air.core.sum row 0 = 1 ∨ air.core.sum row 0 = 2

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_5 air row ↔ constraint_5 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        (air.core.sum row 0 = 1 ∨ air.core.sum row 0 = 2) ∨ air.core.is_valid row 0 = 0

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_6 air row ↔ constraint_6 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_load row 0 = air.core.opcode_when row 0 [0, 1, 2, 3, 4, 5, 6]

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_7 air row ↔ constraint_7 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_load row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_8_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_8 air row ↔ constraint_8 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.write_data_0 row 0 = air.core.expected_val row 0 0

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_9_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_9 air row ↔ constraint_9 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.write_data_1 row 0 = air.core.expected_val row 0 1

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_10_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_10 air row ↔ constraint_10 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.write_data_2 row 0 = air.core.expected_val row 0 2

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_11_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_11 air row ↔ constraint_11 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.write_data_3 row 0 = air.core.expected_val row 0 3

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_12_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_12 air row ↔ constraint_12 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.adapter.needs_write row 0 = 0 ∨ air.adapter.needs_write row 0 = 1

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_13_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_13 air row ↔ constraint_13 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.adapter.needs_write row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_14_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_14 air row ↔ constraint_14 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = air.adapter.needs_write row 0 ∨ air.core.is_load row 0 = 1

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_15_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_15 air row ↔ constraint_15 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = air.adapter.needs_write row 0 ∨ air.adapter.rd_rs2_ptr row 0 = 0

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_16_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_16 air row ↔ constraint_16 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 - air.adapter.rs1_aux_cols.base.prev_timestamp row 0 - 1 =
      air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_17_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_17 air row ↔ constraint_17 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.adapter.carry row 0 = 0 ∨ air.adapter.carry row 0 = 1

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_18_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_18 air row ↔ constraint_18 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.adapter.imm_sign row 0 = 0 ∨ air.adapter.imm_sign row 0 = 1

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_19_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_19 air row ↔ constraint_19 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.adapter.carry' row 0 = 0 ∨ air.adapter.carry' row 0 = 1

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_20_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_20 air row ↔ constraint_20 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        (air.adapter.mem_as row 0 = air.is_store row 0 * 2 ∨ air.adapter.mem_as row 0 - air.is_store row 0 * 2 = 1) ∨
    air.adapter.mem_as row 0 - air.is_store row 0 * 2 = 2

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_21_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_21 air row ↔ constraint_21 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_22 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 1 ∨ air.adapter.mem_as row 0 = 0

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_22_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_22 air row ↔ constraint_22 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp [eq_constant_1] at h
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp [eq_constant_1]
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_23 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 + 1 - air.adapter.read_data_aux.base.prev_timestamp row 0 - 1 =
      air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_23_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_23 air row ↔ constraint_23 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def constraint_24 (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : Prop :=
        air.adapter.needs_write row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 + 2 - air.adapter.write_base_aux.prev_timestamp row 0 - 1 =
      air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constraint_24_of_extraction
          (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ)
      : VmAirWrapper_loadstore.extraction.constraint_24 air row ↔ constraint_24 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_loadstore_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h
        exact h

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      --busRows, constrain_interactions, and constrain_interactions_of_extraction
      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def executionBus_row (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.core.is_valid row 0, [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0]),
        (air.core.is_valid row 0, [air.to_pc row 0, air.adapter.from_state.timestamp row 0 + 3])]

      lemma constrain_execution_interactions
        (air : Valid_VmAirWrapper_loadstore F ExtF)
        (h : VmAirWrapper_loadstore.extraction.constrain_interactions air)
      :
        air.buses ExecutionBus = (List.range (air.last_row + 1)).flatMap (λ row => executionBus_row air row)
      := by
        unfold VmAirWrapper_loadstore.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def memoryBus_row (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : List (F × List F) :=
        [(2013265920 * air.core.is_valid row 0,
          [1, air.adapter.rs1_ptr row 0, air.adapter.rs1_data_0 row 0, air.adapter.rs1_data_1 row 0,
            air.adapter.rs1_data_2 row 0, air.adapter.rs1_data_3 row 0,
            air.adapter.rs1_aux_cols.base.prev_timestamp row 0]),
        (air.core.is_valid row 0,
          [1, air.adapter.rs1_ptr row 0, air.adapter.rs1_data_0 row 0, air.adapter.rs1_data_1 row 0,
            air.adapter.rs1_data_2 row 0, air.adapter.rs1_data_3 row 0, air.adapter.from_state.timestamp row 0]),
        (2013265920 * air.core.is_valid row 0,
          [air.read_as row 0, air.read_ptr row 0, air.core.read_data_0 row 0, air.core.read_data_1 row 0,
            air.core.read_data_2 row 0, air.core.read_data_3 row 0,
            air.adapter.read_data_aux.base.prev_timestamp row 0]),
        (air.core.is_valid row 0,
          [air.read_as row 0, air.read_ptr row 0, air.core.read_data_0 row 0, air.core.read_data_1 row 0,
            air.core.read_data_2 row 0, air.core.read_data_3 row 0, air.adapter.from_state.timestamp row 0 + 1]),
        (2013265920 * air.adapter.needs_write row 0,
          [air.write_as row 0, air.write_ptr row 0, air.core.prev_data_0 row 0, air.core.prev_data_1 row 0,
            air.core.prev_data_2 row 0, air.core.prev_data_3 row 0, air.adapter.write_base_aux.prev_timestamp row 0]),
        (air.adapter.needs_write row 0,
          [air.write_as row 0, air.write_ptr row 0, air.core.write_data_0 row 0, air.core.write_data_1 row 0,
            air.core.write_data_2 row 0, air.core.write_data_3 row 0, air.adapter.from_state.timestamp row 0 + 2])]

      lemma constrain_memory_interactions
        (air : Valid_VmAirWrapper_loadstore F ExtF)
        (h : VmAirWrapper_loadstore.extraction.constrain_interactions air)
      :
        air.buses MemoryBus = (List.range (air.last_row + 1)).flatMap (λ row => memoryBus_row air row)
      := by
        unfold VmAirWrapper_loadstore.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def rangeCheckerBus_row (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0, [air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.core.is_valid row 0, [(air.adapter.mem_ptr_limbs_0 row 0 - air.shift_amount row 0) * 1509949441, 14]),
        (air.core.is_valid row 0, [air.adapter.mem_ptr_limbs_1 row 0, 13]),
        (air.core.is_valid row 0, [air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.adapter.needs_write row 0, [air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.adapter.needs_write row 0, [air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_1 row 0, 12])]

      lemma constrain_rangeChecker_interactions
        (air : Valid_VmAirWrapper_loadstore F ExtF)
        (h : VmAirWrapper_loadstore.extraction.constrain_interactions air)
      :
        air.buses RangeCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeCheckerBus_row air row)
      := by
        unfold VmAirWrapper_loadstore.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
      def programBus_row (air : Valid_VmAirWrapper_loadstore F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
          [air.adapter.from_state.pc row 0, air.core.expected_opcode row 0, air.adapter.rd_rs2_ptr row 0,
            air.adapter.rs1_ptr row 0, air.adapter.imm row 0, 1, air.adapter.mem_as row 0,
            air.adapter.needs_write row 0, air.adapter.imm_sign row 0])]

      lemma constrain_program_interactions
        (air : Valid_VmAirWrapper_loadstore F ExtF)
        (h : VmAirWrapper_loadstore.extraction.constrain_interactions air)
      :
        air.buses ProgramBus = (List.range (air.last_row + 1)).flatMap (λ row => programBus_row air row)
      := by
        unfold VmAirWrapper_loadstore.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      def constrain_interactions (air : Valid_VmAirWrapper_loadstore F ExtF) : Prop :=
      air.buses = fun index ↦
      if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
      else if index = MemoryBus then (List.range (air.last_row + 1)).flatMap (memoryBus_row air)
      else if index = RangeCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeCheckerBus_row air)
      else if index = ProgramBus then (List.range (air.last_row + 1)).flatMap (programBus_row air)
      else []

      @[VmAirWrapper_loadstore_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VmAirWrapper_loadstore F ExtF)
        (h : VmAirWrapper_loadstore.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold VmAirWrapper_loadstore.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        exact h

    end interactions

  end constraint_simplification

  section allHold

    -- constraint list and allHold
    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_loadstore FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        VmAirWrapper_loadstore.extraction.constraint_0 air row,
        VmAirWrapper_loadstore.extraction.constraint_1 air row,
        VmAirWrapper_loadstore.extraction.constraint_2 air row,
        VmAirWrapper_loadstore.extraction.constraint_3 air row,
        VmAirWrapper_loadstore.extraction.constraint_4 air row,
        VmAirWrapper_loadstore.extraction.constraint_5 air row,
        VmAirWrapper_loadstore.extraction.constraint_6 air row,
        VmAirWrapper_loadstore.extraction.constraint_7 air row,
        VmAirWrapper_loadstore.extraction.constraint_8 air row,
        VmAirWrapper_loadstore.extraction.constraint_9 air row,
        VmAirWrapper_loadstore.extraction.constraint_10 air row,
        VmAirWrapper_loadstore.extraction.constraint_11 air row,
        VmAirWrapper_loadstore.extraction.constraint_12 air row,
        VmAirWrapper_loadstore.extraction.constraint_13 air row,
        VmAirWrapper_loadstore.extraction.constraint_14 air row,
        VmAirWrapper_loadstore.extraction.constraint_15 air row,
        VmAirWrapper_loadstore.extraction.constraint_16 air row,
        VmAirWrapper_loadstore.extraction.constraint_17 air row,
        VmAirWrapper_loadstore.extraction.constraint_18 air row,
        VmAirWrapper_loadstore.extraction.constraint_19 air row,
        VmAirWrapper_loadstore.extraction.constraint_20 air row,
        VmAirWrapper_loadstore.extraction.constraint_21 air row,
        VmAirWrapper_loadstore.extraction.constraint_22 air row,
        VmAirWrapper_loadstore.extraction.constraint_23 air row,
        VmAirWrapper_loadstore.extraction.constraint_24 air row,
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_loadstore FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      VmAirWrapper_loadstore.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_loadstore FBB ExtF)
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
      (air : Valid_VmAirWrapper_loadstore FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_loadstore FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold VmAirWrapper_loadstore.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  VmAirWrapper_loadstore_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

  end properties

  section bus_entries

    lemma executionBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_loadstore FBB ExtF} {row : ℕ}
      (h_in : entry ∈ executionBus_row air row)
    :
      entry.2.length = Interaction.ExecutionBusEntryInstance.data_length
    := by
      unfold executionBus_row at *; simp_all
      grind

    @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
    def _executionBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_loadstore FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.ExecutionBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ executionBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (executionBus_row_length x.2)))
          (executionBus_row air row).attach
      List.map Interaction.ExecutionBusEntryInstance.deserialise vectorised_row

    lemma memoryBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_loadstore FBB ExtF} {row : ℕ}
      (h_in : entry ∈ memoryBus_row air row)
    :
      entry.2.length = Interaction.MemoryBusEntryInstance.data_length
    := by
      unfold memoryBus_row at *; simp_all
      grind (ematch := 8)

    @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
    def _memoryBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_loadstore FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.MemoryBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ memoryBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (memoryBus_row_length x.2)))
          (memoryBus_row air row).attach
      List.map Interaction.MemoryBusEntryInstance.deserialise vectorised_row

    lemma rangeCheckerBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_loadstore FBB ExtF} {row : ℕ}
      (h_in : entry ∈ rangeCheckerBus_row air row)
    :
      entry.2.length = Interaction.RangeCheckerBusEntryInstance.data_length
    := by
      unfold rangeCheckerBus_row at *; simp_all
      grind

    @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
    def _rangeCheckerBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_loadstore FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.RangeCheckerBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ rangeCheckerBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (rangeCheckerBus_row_length x.2)))
          (rangeCheckerBus_row air row).attach
      List.map Interaction.RangeCheckerBusEntryInstance.deserialise vectorised_row

    -- @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
    -- def programBus_properties (entry : Interaction.ProgramBusEntry FBB) : Prop :=
    --   let rs2 := entry.xc
    --   let rs2_as := entry.xe
    --   (rs2_as = 0 →
    --     -- opcode cannot be SUB
    --     ¬ entry.opcode = 513 ∧
    --     -- immediate fits 24 bits
    --     rs2.val < 2 ^ 24 ∧
    --     -- immediate is a sign-extended 12-bit value
    --     (BitVec.ofNat 24 rs2.val).toInt = (BitVec.ofNat 12 rs2.val).toInt)

    -- set_option maxHeartbeats 0
    -- lemma programBus_properties_of_opcode_bounds (entry : Interaction.ProgramBusEntry FBB)
    --   (h_bounds : entry.opcode = 528)
    --   (h_bus : Interaction.ProgramBusEntry.operand_properties entry)
    -- :
    --   programBus_properties entry
    -- := by
    --   simp [programBus_properties.eq_def]
    --   simp [Interaction.ProgramBusEntry.operand_properties] at h_bus
    --   obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus
    --   have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    --   simp [←h_data] at h_bounds ⊢ h_transpile h_alignment
    --   clear h_data
    --   have h_supported_types := Transpiler.transpiler_supported_opcode_types h_transpile
    --   have : data = #v[data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7], data[8]] := by
    --     clear *-data
    --     apply Vector.ext
    --     intro i h_i
    --     by_cases i=0; simp [*]
    --     by_cases i=1; simp [*]
    --     by_cases i=2; simp [*]
    --     by_cases i=3; simp [*]
    --     by_cases i=4; simp [*]
    --     by_cases i=5; simp [*]
    --     by_cases i=6; simp [*]
    --     by_cases i=7; simp [*]
    --     by_cases i=8; simp [*]
    --     exfalso; omega
    --   rcases h_supported_types with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
    --   . obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type -- RTYPE
    --     cases op <;> {
    --       rewrite [h_op_data] at h_transpile
    --       unfold Transpiler.transpile_op at h_transpile
    --       rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
    --       simp at h_transpile
    --       rewrite [this] at h_transpile
    --       dsimp at h_transpile
    --       split_ifs at h_transpile
    --       . exfalso; grind
    --       . grind
    --     }
    --   . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
    --     cases op <;> {
    --       rewrite [h_op_data] at h_transpile
    --       unfold Transpiler.transpile_op at h_transpile
    --       rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
    --       simp at h_transpile
    --       rewrite [this] at h_transpile
    --       dsimp at h_transpile
    --       split_ifs at h_transpile
    --       . exfalso; grind
    --       . intro h_rs2_as
    --         have : data[4] = Transpiler.utof (Transpiler.sign_extend_24 imm) := by grind
    --         split_ands
    --         . grind
    --         . simp [this, Transpiler.utof, Transpiler.sign_extend_24]
    --           omega
    --         . simp [this, Transpiler.utof, Transpiler.sign_extend_24]
    --           rewrite [
    --             Nat.mod_eq_of_lt (by omega), BitVec.ofNat_toNat, BitVec.ofNat_toNat,
    --             BitVec.setWidth_eq, (show BitVec.setWidth 12 (BitVec.signExtend 24 imm) = imm by bv_decide)
    --           ]
    --           clear * - imm
    --           simp [BitVec.toInt_signExtend]
    --           exact Int.bmod_eq_of_le (by grind) (by grind)
    --     }
    --   . obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type -- SHIFTIOP
    --     cases op <;> {
    --       rewrite [h_op_data] at h_transpile
    --       unfold Transpiler.transpile_op at h_transpile
    --       rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
    --       simp at h_transpile
    --       rewrite [this] at h_transpile
    --       dsimp at h_transpile
    --       split_ifs at h_transpile
    --       . exfalso; grind
    --       . exfalso; grind
    --     }
    --   . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- BTYPE
    --     cases op <;> {
    --       rewrite [h_op_data] at h_transpile
    --       unfold Transpiler.transpile_op at h_transpile
    --       rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
    --       simp at h_transpile
    --       rewrite [this] at h_transpile
    --       dsimp at h_transpile
    --       exfalso
    --       grind
    --     }
    --   . obtain ⟨⟨imm, rs1, op⟩, h_op_data⟩ := h_type -- UTYPE
    --     cases op <;> {
    --       rewrite [h_op_data] at h_transpile
    --       unfold Transpiler.transpile_op at h_transpile
    --       rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
    --       exfalso
    --       dsimp at h_transpile
    --       grind
    --     }
    --   . obtain ⟨⟨rs2, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
    --     cases high <;> cases signed_rs1 <;> cases signed_rs2 <;> {
    --       rewrite [h_op_data] at h_transpile
    --       unfold Transpiler.transpile_op at h_transpile
    --       rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
    --       exfalso
    --       dsimp at h_transpile
    --       grind
    --     }
    --   . obtain ⟨⟨rs2, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
    --     cases signed <;> {
    --       rewrite [h_op_data] at h_transpile
    --       unfold Transpiler.transpile_op at h_transpile
    --       rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
    --       exfalso
    --       dsimp at h_transpile
    --       split_ifs at h_transpile <;> simp at h_transpile <;> grind
    --     }
    --   . obtain ⟨⟨rs2, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
    --     cases signed <;> {
    --       rewrite [h_op_data] at h_transpile
    --       unfold Transpiler.transpile_op at h_transpile
    --       rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
    --       exfalso
    --       dsimp at h_transpile
    --       split_ifs at h_transpile <;> simp at h_transpile <;> grind
    --     }
    --   . obtain ⟨⟨imm, rs1, rd, is_unsigned, w⟩, h_op_data⟩ := h_type -- LOAD
    --     rewrite [h_op_data] at h_transpile
    --     unfold Transpiler.transpile_op at h_transpile
    --     rewrite [ite_cond_eq_true _ _ (eq_true h_alignment)] at h_transpile
    --     dsimp at h_transpile
    --     split_ifs at h_transpile <;> {
    --       simp [-Vector.mk_eq] at h_transpile
    --       rewrite [←h_transpile]
    --       simp
    --     }

    lemma programBus_row_length [Field ExtF]
      {air : Valid_VmAirWrapper_loadstore FBB ExtF} {row : ℕ}
      (h_in : entry ∈ programBus_row air row)
    :
      entry.2.length = Interaction.ProgramBusEntryInstance.data_length
    := by
      unfold programBus_row at *; simp_all

    @[VmAirWrapper_loadstore_constraint_and_interaction_simplification]
    def _programBus_row [Field ExtF]
      (air : Valid_VmAirWrapper_loadstore FBB ExtF) (row : ℕ) :=
      let vectorised_row : List (FBB × Vector FBB Interaction.ProgramBusEntryInstance.data_length) := by
        exact
        List.map
          (fun x : { row' // row' ∈ programBus_row air row} =>
          (x.1.1, Vector.mk x.1.2.toArray (programBus_row_length x.2)))
          (programBus_row air row).attach
      List.map Interaction.ProgramBusEntryInstance.deserialise vectorised_row

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
    def busRow [Field ExtF] (air : Valid_VmAirWrapper_loadstore FBB ExtF) (row : ℕ)
    : List (FBB × List FBB) :=
      executionBus_row air row ++
      memoryBus_row air row ++
      rangeCheckerBus_row air row ++
      programBus_row air row

    @[simp]
    def axiomsPerRow [Field ExtF]
      (air : Valid_VmAirWrapper_loadstore FBB ExtF) (row : ℕ)
    : Prop :=
      axioms (_executionBus_row air row) ∧
      axioms (_memoryBus_row air row) ∧
      axioms (_rangeCheckerBus_row air row) ∧
      axioms (_programBus_row air row)

    @[simp]
    def wf_propertiesToAssumePerRow [Field ExtF] (air : Valid_VmAirWrapper_loadstore FBB ExtF) (row : ℕ)
    : Prop :=
      propertiesToAssume (_executionBus_row air row) ∧
      propertiesToAssume (_memoryBus_row air row) ∧
      propertiesToAssume (_rangeCheckerBus_row air row) ∧
      propertiesToAssume (_programBus_row air row)

    @[simp]
    def wf_propertiesToAssertPerRow [Field ExtF] (air : Valid_VmAirWrapper_loadstore FBB ExtF) (row : ℕ)
    : Prop :=
      propertiesToAssert (_executionBus_row air row) ∧
      propertiesToAssert (_memoryBus_row air row) ∧
      propertiesToAssert (_rangeCheckerBus_row air row) ∧
      propertiesToAssert (_programBus_row air row)

  end bus_entries

end VmAirWrapper_loadstore.constraints
