import OpenvmFv.Airs.Alu.VmAirWrapper_mulh
import OpenvmFv.Extraction.VmAirWrapper_mulh
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace VmAirWrapper_mulh.constraints

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

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_mulh_flag row 0 = 0 ∨ air.core.opcode_mulh_flag row 0 = 1

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_0_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_0 air row ↔ constraint_0 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_mulhsu_flag row 0 = 0 ∨ air.core.opcode_mulhsu_flag row 0 = 1

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_1_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_1 air row ↔ constraint_1 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_mulhu_flag row 0 = 0 ∨ air.core.opcode_mulhu_flag row 0 = 1

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_2_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_2 air row ↔ constraint_2 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_3_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_3 air row ↔ constraint_3 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.b_sign row 0 = 0 ∨ air.core.b_sign row 0 = 1

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_4_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_4 air row ↔ constraint_4 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.c_sign row 0 = 0 ∨ air.core.c_sign row 0 = 1

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_5_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_5 air row ↔ constraint_5 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_mulhu_flag row 0 = 0 ∨ air.core.b_sign row 0 = 0

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_6_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_6 air row ↔ constraint_6 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_mulhu_flag row 0 + air.core.opcode_mulhsu_flag row 0 = 0 ∨ air.core.c_sign row 0 = 0

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_7_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_7 air row ↔ constraint_7 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 - air.adapter.reads_aux_0.base.prev_timestamp row 0 - 1 =
      air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_8_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_8 air row ↔ constraint_8 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 + 1 - air.adapter.reads_aux_1.base.prev_timestamp row 0 - 1 =
      air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_9_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_9 air row ↔ constraint_9 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 + 2 - air.adapter.writes_aux.base.prev_timestamp row 0 - 1 =
      air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_mulh_air_simplification]
      lemma constraint_10_of_extraction
          (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      : VmAirWrapper_mulh.extraction.constraint_10 air row ↔ constraint_10 air row := by
      apply Iff.intro
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
        exact h
      . intro h
        simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
        simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
        exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_11 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_11_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_11 air row ↔ constraint_11 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_12 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_12_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_12 air row ↔ constraint_12 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_13 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_13_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_13 air row ↔ constraint_13 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_14 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_14_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_14 air row ↔ constraint_14 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_15 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_15_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_15 air row ↔ constraint_15 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_16 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_16_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_16 air row ↔ constraint_16 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_17 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_17_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_17 air row ↔ constraint_17 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_18 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_18_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_18 air row ↔ constraint_18 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_19 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_19_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_19 air row ↔ constraint_19 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_20 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_20_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_20 air row ↔ constraint_20 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_21 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_21_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_21 air row ↔ constraint_21 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_22 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_22_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_22 air row ↔ constraint_22 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_23 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_23_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_23 air row ↔ constraint_23 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_24 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_24_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_24 air row ↔ constraint_24 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_25 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_25_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_25 air row ↔ constraint_25 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_26 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_26_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_26 air row ↔ constraint_26 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_27 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_27_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_27 air row ↔ constraint_27 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_28 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_28_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_28 air row ↔ constraint_28 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_29 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_29_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_29 air row ↔ constraint_29 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

      -- @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      -- def constraint_30 (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : Prop :=
      --   sorry
      --
      -- @[VmAirWrapper_mulh_air_simplification]
      -- lemma constraint_30_of_extraction
      --     (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ)
      -- : VmAirWrapper_mulh.extraction.constraint_30 air row ↔ constraint_30 air row := by
      -- apply Iff.intro
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   exact h
      -- . intro h
      --   simp [openvm_encapsulation, VmAirWrapper_mulh_constraint_and_interaction_simplification]
      --   simp only [VmAirWrapper_mulh_constraint_and_interaction_simplification] at h
      --   exact h

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      --busRows, constrain_interactions, and constrain_interactions_of_extraction

      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def executionBus_row (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : List (F × List F) :=
        [(-air.core.is_valid row 0, [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0]),
        (air.core.is_valid row 0, [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3])]

      lemma constrain_execution_interactions
        (air : Valid_VmAirWrapper_mulh F ExtF)
        (h : VmAirWrapper_mulh.extraction.constrain_interactions air)
      :
        air.buses ExecutionBus = (List.range (air.last_row + 1)).flatMap (λ row => executionBus_row air row)
      := by
        unfold VmAirWrapper_mulh.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def memoryBus_row (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : List (F × List F) :=
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
          [1, air.adapter.rd_ptr row 0, air.core.a_0 row 0, air.core.a_1 row 0, air.core.a_2 row 0, air.core.a_3 row 0,
            air.adapter.from_state.timestamp row 0 + 2])]

      lemma constrain_memory_interactions
        (air : Valid_VmAirWrapper_mulh F ExtF)
        (h : VmAirWrapper_mulh.extraction.constrain_interactions air)
      :
        air.buses MemoryBus = (List.range (air.last_row + 1)).flatMap (λ row => memoryBus_row air row)
      := by
        unfold VmAirWrapper_mulh.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def rangeCheckerBus_row (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0, [air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.core.is_valid row 0, [air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.core.is_valid row 0, [air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12])]

      lemma constrain_rangeChecker_interactions
        (air : Valid_VmAirWrapper_mulh F ExtF)
        (h : VmAirWrapper_mulh.extraction.constrain_interactions air)
      :
        air.buses RangeCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeCheckerBus_row air row)
      := by
        unfold VmAirWrapper_mulh.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def readInstructionBus_row (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
          [air.adapter.from_state.pc row 0,
            593 + (air.core.opcode_mulhsu_flag row 0 + air.core.opcode_mulhu_flag row 0 * 2), air.adapter.rd_ptr row 0,
            air.adapter.rs1_ptr row 0, air.adapter.rs2_ptr row 0, 1, 0, 0, 0])]

      lemma constrain_readInstruction_interactions
        (air : Valid_VmAirWrapper_mulh F ExtF)
        (h : VmAirWrapper_mulh.extraction.constrain_interactions air)
      :
        air.buses ReadInstructionBus = (List.range (air.last_row + 1)).flatMap (λ row => readInstructionBus_row air row)
      := by
        unfold VmAirWrapper_mulh.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def bitwiseBus_row (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.opcode_mulh_flag row 0 + air.core.opcode_mulhsu_flag row 0,
          [2 * (air.core.b_3 row 0 - air.core.b_sign row 0 * 128),
            (air.core.opcode_mulh_flag row 0 + 1) * (air.core.c_3 row 0 - air.core.c_sign row 0 * 128), 0, 0])]

      lemma constrain_bitwise_interactions
        (air : Valid_VmAirWrapper_mulh F ExtF)
        (h : VmAirWrapper_mulh.extraction.constrain_interactions air)
      :
        air.buses BitwiseBus = (List.range (air.last_row + 1)).flatMap (λ row => bitwiseBus_row air row)
      := by
        unfold VmAirWrapper_mulh.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      @[VmAirWrapper_mulh_constraint_and_interaction_simplification]
      def rangeTupleCheckerBus_row (air : Valid_VmAirWrapper_mulh F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0, [air.core.a_mul_0 row 0, air.core.carry_mul row 0 0]),
        (air.core.is_valid row 0, [air.core.a_mul_1 row 0, air.core.carry_mul row 0 1]),
        (air.core.is_valid row 0, [air.core.a_mul_2 row 0, air.core.carry_mul row 0 2]),
        (air.core.is_valid row 0, [air.core.a_mul_3 row 0, air.core.carry_mul row 0 3]),
        (air.core.is_valid row 0,
          [air.core.a_0 row 0,
            2005401601 *
              (air.core.carry_mul row 0 3 +
                    (air.core.b_1 row 0 * air.core.c_3 row 0 + air.core.b_2 row 0 * air.core.c_2 row 0 +
                      air.core.b_3 row 0 * air.core.c_1 row 0) +
                  (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0) -
                air.core.a_0 row 0)]),
        (air.core.is_valid row 0,
          [air.core.a_1 row 0,
            2005401601 *
              (2005401601 *
                      (air.core.carry_mul row 0 3 +
                            (air.core.b_1 row 0 * air.core.c_3 row 0 + air.core.b_2 row 0 * air.core.c_2 row 0 +
                              air.core.b_3 row 0 * air.core.c_1 row 0) +
                          (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0) -
                        air.core.a_0 row 0) +
                    (air.core.b_2 row 0 * air.core.c_3 row 0 + air.core.b_3 row 0 * air.core.c_2 row 0) +
                  (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 +
                      air.core.b_1 row 0 * air.core.c_ext row 0 +
                    air.core.c_1 row 0 * air.core.b_ext row 0) -
                air.core.a_1 row 0)]),
        (air.core.is_valid row 0,
          [air.core.a_2 row 0,
            2005401601 *
              (2005401601 *
                      (2005401601 *
                              (air.core.carry_mul row 0 3 +
                                    (air.core.b_1 row 0 * air.core.c_3 row 0 + air.core.b_2 row 0 * air.core.c_2 row 0 +
                                      air.core.b_3 row 0 * air.core.c_1 row 0) +
                                  (air.core.b_0 row 0 * air.core.c_ext row 0 +
                                    air.core.c_0 row 0 * air.core.b_ext row 0) -
                                air.core.a_0 row 0) +
                            (air.core.b_2 row 0 * air.core.c_3 row 0 + air.core.b_3 row 0 * air.core.c_2 row 0) +
                          (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 +
                              air.core.b_1 row 0 * air.core.c_ext row 0 +
                            air.core.c_1 row 0 * air.core.b_ext row 0) -
                        air.core.a_1 row 0) +
                    air.core.b_3 row 0 * air.core.c_3 row 0 +
                  (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 +
                          air.core.b_1 row 0 * air.core.c_ext row 0 +
                        air.core.c_1 row 0 * air.core.b_ext row 0 +
                      air.core.b_2 row 0 * air.core.c_ext row 0 +
                    air.core.c_2 row 0 * air.core.b_ext row 0) -
                air.core.a_2 row 0)]),
        (air.core.is_valid row 0,
          [air.core.a_3 row 0,
            2005401601 *
              (2005401601 *
                    (2005401601 *
                            (2005401601 *
                                    (air.core.carry_mul row 0 3 +
                                          (air.core.b_1 row 0 * air.core.c_3 row 0 +
                                              air.core.b_2 row 0 * air.core.c_2 row 0 +
                                            air.core.b_3 row 0 * air.core.c_1 row 0) +
                                        (air.core.b_0 row 0 * air.core.c_ext row 0 +
                                          air.core.c_0 row 0 * air.core.b_ext row 0) -
                                      air.core.a_0 row 0) +
                                  (air.core.b_2 row 0 * air.core.c_3 row 0 + air.core.b_3 row 0 * air.core.c_2 row 0) +
                                (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 +
                                    air.core.b_1 row 0 * air.core.c_ext row 0 +
                                  air.core.c_1 row 0 * air.core.b_ext row 0) -
                              air.core.a_1 row 0) +
                          air.core.b_3 row 0 * air.core.c_3 row 0 +
                        (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 +
                                air.core.b_1 row 0 * air.core.c_ext row 0 +
                              air.core.c_1 row 0 * air.core.b_ext row 0 +
                            air.core.b_2 row 0 * air.core.c_ext row 0 +
                          air.core.c_2 row 0 * air.core.b_ext row 0) -
                      air.core.a_2 row 0) +
                  (air.core.b_0 row 0 * air.core.c_ext row 0 + air.core.c_0 row 0 * air.core.b_ext row 0 +
                              air.core.b_1 row 0 * air.core.c_ext row 0 +
                            air.core.c_1 row 0 * air.core.b_ext row 0 +
                          air.core.b_2 row 0 * air.core.c_ext row 0 +
                        air.core.c_2 row 0 * air.core.b_ext row 0 +
                      air.core.b_3 row 0 * air.core.c_ext row 0 +
                    air.core.c_3 row 0 * air.core.b_ext row 0) -
                air.core.a_3 row 0)])]

      lemma constrain_rangeTupleChecker_interactions
        (air : Valid_VmAirWrapper_mulh F ExtF)
        (h : VmAirWrapper_mulh.extraction.constrain_interactions air)
      :
        air.buses RangeTupleCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeTupleCheckerBus_row air row)
      := by
        unfold VmAirWrapper_mulh.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl


      def constrain_interactions (air : Valid_VmAirWrapper_mulh F ExtF) : Prop :=
      air.buses = fun index ↦
      if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
      else if index = MemoryBus then (List.range (air.last_row + 1)).flatMap (memoryBus_row air)
      else if index = RangeCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeCheckerBus_row air)
      else if index = ReadInstructionBus then (List.range (air.last_row + 1)).flatMap (readInstructionBus_row air)
      else if index = BitwiseBus then (List.range (air.last_row + 1)).flatMap (bitwiseBus_row air)
      else if index = RangeTupleCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeTupleCheckerBus_row air)
      else []

      @[VmAirWrapper_mulh_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VmAirWrapper_mulh F ExtF)
        (h : VmAirWrapper_mulh.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold VmAirWrapper_mulh.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        exact h

    end interactions

  end constraint_simplification

  section allHold

    -- constraint list and allHold

    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_mulh FBB ExtF)
      (row : ℕ)
    : List Prop :=
      [
        VmAirWrapper_mulh.extraction.constraint_0 air row,
        VmAirWrapper_mulh.extraction.constraint_1 air row,
        VmAirWrapper_mulh.extraction.constraint_2 air row,
        VmAirWrapper_mulh.extraction.constraint_3 air row,
        VmAirWrapper_mulh.extraction.constraint_4 air row,
        VmAirWrapper_mulh.extraction.constraint_5 air row,
        VmAirWrapper_mulh.extraction.constraint_6 air row,
        VmAirWrapper_mulh.extraction.constraint_7 air row,
        VmAirWrapper_mulh.extraction.constraint_8 air row,
        VmAirWrapper_mulh.extraction.constraint_9 air row,
        VmAirWrapper_mulh.extraction.constraint_10 air row,
    --     VmAirWrapper_mulh.extraction.constraint_11 air row,
    --     VmAirWrapper_mulh.extraction.constraint_12 air row,
    --     VmAirWrapper_mulh.extraction.constraint_13 air row,
    --     VmAirWrapper_mulh.extraction.constraint_14 air row,
    --     VmAirWrapper_mulh.extraction.constraint_15 air row,
    --     VmAirWrapper_mulh.extraction.constraint_16 air row,
    --     VmAirWrapper_mulh.extraction.constraint_17 air row,
    --     VmAirWrapper_mulh.extraction.constraint_18 air row,
    --     VmAirWrapper_mulh.extraction.constraint_19 air row,
      ]

    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_mulh FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      VmAirWrapper_mulh.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_mulh FBB ExtF)
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
    --     constraint_11 air row,
    --     constraint_12 air row,
    --     constraint_13 air row,
    --     constraint_14 air row,
    --     constraint_15 air row,
    --     constraint_16 air row,
    --     constraint_17 air row,
    --     constraint_18 air row,
    --     constraint_19 air row,
      ]

    @[simp]
    def allHold_simplified
      [Field ExtF]
      (air : Valid_VmAirWrapper_mulh FBB ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    lemma allHold_simplified_of_allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_mulh FBB ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold VmAirWrapper_mulh.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                  row_constraint_list,
                  VmAirWrapper_mulh_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

  end properties

end VmAirWrapper_mulh.constraints
