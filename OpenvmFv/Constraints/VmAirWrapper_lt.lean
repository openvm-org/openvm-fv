import OpenvmFv.Airs.Alu.VmAirWrapper_lt
import OpenvmFv.Extraction.VmAirWrapper_lt
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

namespace VmAirWrapper_lt.constraints

  section constraint_simplification
    -- air and row not included in here so that it still works with sorries during extraction
    variable [Field F] [Field ExtF]

    section row_constraints
      def constraint_0 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_slt_flag row 0 = 0 ∨ air.core.opcode_slt_flag row 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_0_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_0 air row)
      : constraint_0 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_0 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_1 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_sltu_flag row 0 = 0 ∨ air.core.opcode_sltu_flag row 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_1_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_1 air row)
      : constraint_1 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_1 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_2 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_2_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_2 air row)
      : constraint_2 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_2 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_3 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.cmp_result row 0 = 0 ∨ air.core.cmp_result row 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_3_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_3 air row)
      : constraint_3 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_3 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_4 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.b_3 row 0 = air.core.b_msb_f row 0 ∨ 256 = air.core.b_3 row 0 - air.core.b_msb_f row 0

      @[VmAirWrapper_lt_simplification]
      lemma constraint_4_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_4 air row)
      : constraint_4 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_4 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_5 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.c_3 row 0 = air.core.c_msb_f row 0 ∨ 256 = air.core.c_3 row 0 - air.core.c_msb_f row 0

      @[VmAirWrapper_lt_simplification]
      lemma constraint_5_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_5 air row)
      : constraint_5 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_5 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_6 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_3 row 0 = 0 ∨ air.core.diff_marker_3 row 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_6_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_6 air row)
      : constraint_6 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_6 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_7 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.core.diff_marker_3 row 0 ∨ air.core.diff row 0 3 = 0

      @[VmAirWrapper_lt_simplification]
      lemma constraint_7_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_7 air row)
      : constraint_7 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_7 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_8 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_3 row 0 = 0 ∨ air.core.diff_val row 0 = air.core.diff row 0 3

      @[VmAirWrapper_lt_simplification]
      lemma constraint_8_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_8 air row)
      : constraint_8 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_8 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_9 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_2 row 0 = 0 ∨ air.core.diff_marker_2 row 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_9_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_9 air row)
      : constraint_9 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_9 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_10 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.core.prefix_sum row 0 2 ∨ air.core.diff row 0 2 = 0

      @[VmAirWrapper_lt_simplification]
      lemma constraint_10_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_10 air row)
      : constraint_10 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_10 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_11 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_2 row 0 = 0 ∨ air.core.diff_val row 0 = air.core.diff row 0 2

      @[VmAirWrapper_lt_simplification]
      lemma constraint_11_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_11 air row)
      : constraint_11 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_11 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_12 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_1 row 0 = 0 ∨ air.core.diff_marker_1 row 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_12_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_12 air row)
      : constraint_12 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_12 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_13 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.core.prefix_sum row 0 1 ∨ air.core.diff row 0 1 = 0

      @[VmAirWrapper_lt_simplification]
      lemma constraint_13_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_13 air row)
      : constraint_13 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_13 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_14 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_1 row 0 = 0 ∨ air.core.diff_val row 0 = air.core.diff row 0 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_14_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_14 air row)
      : constraint_14 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_14 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_15 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_0 row 0 = 0 ∨ air.core.diff_marker_0 row 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_15_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_15 air row)
      : constraint_15 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_15 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_16 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.core.prefix_sum row 0 0 ∨ air.core.diff row 0 0 = 0

      @[VmAirWrapper_lt_simplification]
      lemma constraint_16_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_16 air row)
      : constraint_16 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_16 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_17 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.diff_marker_0 row 0 = 0 ∨ air.core.diff_val row 0 = air.core.diff row 0 0

      @[VmAirWrapper_lt_simplification]
      lemma constraint_17_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_17 air row)
      : constraint_17 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_17 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_18 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.prefix_sum row 0 0 = 0 ∨ air.core.prefix_sum row 0 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_18_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_18 air row)
      : constraint_18 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_18 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_19 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.core.prefix_sum row 0 0 ∨ air.core.cmp_result row 0 = 0

      @[VmAirWrapper_lt_simplification]
      lemma constraint_19_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_19 air row)
      : constraint_19 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_19 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_20 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 0 ∨ air.adapter.rs2_as row 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_20_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_20 air row)
      : constraint_20 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_20 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_21 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.adapter.rs2_as row 0 ∨ air.adapter.rs2 row 0 = air.rs2_imm row 0

      @[VmAirWrapper_lt_simplification]
      lemma constraint_21_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_21 air row)
      : constraint_21 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_21 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_22 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.adapter.rs2_as row 0 ∨ air.rs2_sign row 0 = air.rs2_limbs row 0 3

      @[VmAirWrapper_lt_simplification]
      lemma constraint_22_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_22 air row)
      : constraint_22 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_22 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_23 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        1 = air.adapter.rs2_as row 0 ∨ air.core.c_2 row 0 = 0 ∨ 255 = air.core.c_2 row 0

      @[VmAirWrapper_lt_simplification]
      lemma constraint_23_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_23 air row)
      : constraint_23 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_23 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_24 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
        air.adapter.from_state.timestamp row 0 - air.adapter.reads_aux_0.base.prev_timestamp row 0 - 1 =
          air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0 +
            air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_lt_simplification]
      lemma constraint_24_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_24 air row)
      : constraint_24 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_24 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_25 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_lt_simplification]
      lemma constraint_25_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_25 air row)
      : constraint_25 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_25 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_26 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 + 1 - air.adapter.reads_aux_1.base.prev_timestamp row 0 - 1 =
      air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_lt_simplification]
      lemma constraint_26_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_26 air row)
      : constraint_26 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_26 at h
        simp [openvm_encapsulation] at h
        exact h

      def constraint_27 (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨
    air.adapter.from_state.timestamp row 0 + 2 - air.adapter.writes_aux.base.prev_timestamp row 0 - 1 =
      air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_lt_simplification]
      lemma constraint_27_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ)
        (h: VmAirWrapper_lt.extraction.constraint_27 air row)
      : constraint_27 air row := by
        unfold VmAirWrapper_lt.extraction.constraint_27 at h
        simp [openvm_encapsulation] at h
        exact h
    end row_constraints

    section interactions
      def executionBus_row (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : List (F × List F) :=
        [
          (-air.core.is_valid row 0, [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0]),
          (air.core.is_valid row 0, [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3])
        ]

      lemma constrain_execution_interactions
        (air : Valid_VmAirWrapper_lt F ExtF)
        (h : VmAirWrapper_lt.extraction.constrain_interactions air)
      :
        air.buses ExecutionBus = (List.range (air.last_row + 1)).flatMap (λ row => executionBus_row air row)
      := by
        unfold VmAirWrapper_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        -- uncomment this during extraction to get the expression in infoview
        -- congr; funext row
        rfl

      def memoryBus_row (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : List (F × List F) :=
        [
          (2013265920 * air.core.is_valid row 0,
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
            [1, air.adapter.rd_ptr row 0, air.adapter.writes_aux.prev_data_0 row 0, air.adapter.writes_aux.prev_data_1 row 0,
              air.adapter.writes_aux.prev_data_2 row 0, air.adapter.writes_aux.prev_data_3 row 0,
              air.adapter.writes_aux.base.prev_timestamp row 0]),
          (air.core.is_valid row 0,
            [1, air.adapter.rd_ptr row 0, air.core.cmp_result row 0, 0, 0, 0, air.adapter.from_state.timestamp row 0 + 2])
        ]

      lemma constrain_memory_interactions
        (air : Valid_VmAirWrapper_lt F ExtF)
        (h : VmAirWrapper_lt.extraction.constrain_interactions air)
      :
        air.buses MemoryBus = (List.range (air.last_row + 1)).flatMap (λ row => memoryBus_row air row)
      := by
        unfold VmAirWrapper_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        -- uncomment this during extraction to get the expression in infoview
        -- congr; funext row
        rfl

      def rangeBus_row (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0, [air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.adapter.rs2_as row 0, [air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.adapter.rs2_as row 0, [air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        (air.core.is_valid row 0, [air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
        (air.core.is_valid row 0, [air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12])]

      lemma constrain_range_interactions
        (air : Valid_VmAirWrapper_lt F ExtF)
        (h : VmAirWrapper_lt.extraction.constrain_interactions air)
      :
        air.buses RangeCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeBus_row air row)
      := by
        unfold VmAirWrapper_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        -- uncomment this during extraction to get the expression in infoview
        -- congr; funext row
        rfl

      def readInstructionBus_row (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
        [air.adapter.from_state.pc row 0, air.core.opcode_sltu_flag row 0 + 520, air.adapter.rd_ptr row 0,
          air.adapter.rs1_ptr row 0, air.adapter.rs2 row 0, 1, air.adapter.rs2_as row 0, 0, 0])]

      lemma constrain_readInstruction_interactions
        (air : Valid_VmAirWrapper_lt F ExtF)
        (h : VmAirWrapper_lt.extraction.constrain_interactions air)
      :
        air.buses ReadInstructionBus = (List.range (air.last_row + 1)).flatMap (λ row => readInstructionBus_row air row)
      := by
        unfold VmAirWrapper_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        -- uncomment this during extraction to get the expression in infoview
        -- congr; funext row
        rfl

      def bitwiseBus_row (air : Valid_VmAirWrapper_lt F ExtF) (row : ℕ) : List (F × List F) :=
        [(air.core.is_valid row 0,
          [air.core.b_msb_f row 0 + 128 * air.core.opcode_slt_flag row 0,
            air.core.c_msb_f row 0 + 128 * air.core.opcode_slt_flag row 0, 0, 0]),
        (air.core.prefix_sum row 0 0, [air.core.diff_val row 0 - 1, 0, 0, 0]),
        (air.core.is_valid row 0 - air.adapter.rs2_as row 0, [air.core.c_0 row 0, air.core.c_1 row 0, 0, 0])]

      lemma constrain_bitwise_interactions
        (air : Valid_VmAirWrapper_lt F ExtF)
        (h : VmAirWrapper_lt.extraction.constrain_interactions air)
      :
        air.buses BitwiseBus = (List.range (air.last_row + 1)).flatMap (λ row => bitwiseBus_row air row)
      := by
        unfold VmAirWrapper_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        -- uncomment this during extraction to get the expression in infoview
        -- congr; funext row
        rfl

      def constrain_interactions (air : Valid_VmAirWrapper_lt F ExtF) : Prop :=
        air.buses = fun index ↦
        if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
        else if index = MemoryBus then (List.range (air.last_row + 1)).flatMap (memoryBus_row air)
        else if index = RangeCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeBus_row air)
        else if index = ReadInstructionBus then (List.range (air.last_row + 1)).flatMap (readInstructionBus_row air)
        else if index = BitwiseBus then (List.range (air.last_row + 1)).flatMap (bitwiseBus_row air)
        else []

      @[VmAirWrapper_lt_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VmAirWrapper_lt F ExtF)
        (h : VmAirWrapper_lt.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold VmAirWrapper_lt.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        exact h
    end interactions


  end constraint_simplification

  -- TODO have extractor generate this and put in extraction file
  @[simp]
  def extracted_row_constraint_list
    [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
  : List Prop :=
    [
      VmAirWrapper_lt.extraction.constraint_0 air row,
      VmAirWrapper_lt.extraction.constraint_1 air row,
      VmAirWrapper_lt.extraction.constraint_2 air row,
      VmAirWrapper_lt.extraction.constraint_3 air row,
      VmAirWrapper_lt.extraction.constraint_4 air row,
      VmAirWrapper_lt.extraction.constraint_5 air row,
      VmAirWrapper_lt.extraction.constraint_6 air row,
      VmAirWrapper_lt.extraction.constraint_7 air row,
      VmAirWrapper_lt.extraction.constraint_8 air row,
      VmAirWrapper_lt.extraction.constraint_9 air row,
      VmAirWrapper_lt.extraction.constraint_10 air row,
      VmAirWrapper_lt.extraction.constraint_11 air row,
      VmAirWrapper_lt.extraction.constraint_12 air row,
      VmAirWrapper_lt.extraction.constraint_13 air row,
      VmAirWrapper_lt.extraction.constraint_14 air row,
      VmAirWrapper_lt.extraction.constraint_15 air row,
      VmAirWrapper_lt.extraction.constraint_16 air row,
      VmAirWrapper_lt.extraction.constraint_17 air row,
      VmAirWrapper_lt.extraction.constraint_18 air row,
      VmAirWrapper_lt.extraction.constraint_19 air row,
      VmAirWrapper_lt.extraction.constraint_20 air row,
      VmAirWrapper_lt.extraction.constraint_21 air row,
      VmAirWrapper_lt.extraction.constraint_22 air row,
      VmAirWrapper_lt.extraction.constraint_23 air row,
      VmAirWrapper_lt.extraction.constraint_24 air row,
      VmAirWrapper_lt.extraction.constraint_25 air row,
      VmAirWrapper_lt.extraction.constraint_26 air row,
      VmAirWrapper_lt.extraction.constraint_27 air row
    ]

  -- TODO have extractor generate this and put in extraction file
  @[simp]
  def allHold
    [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (_ : row ≤ air.last_row)
  : Prop :=
    VmAirWrapper_lt.extraction.constrain_interactions air ∧
    List.Forall (·) (extracted_row_constraint_list air row)

  @[simp]
  def row_constraint_list
    [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
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
      constraint_27 air row
    ]

  @[simp]
  def allHold_simplified
    [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (_ : row ≤ air.last_row)
  : Prop :=
    constrain_interactions air ∧
    List.Forall (·) (row_constraint_list air row)

  lemma allHold_simplified_of_allHold
    [Field ExtF]
    (air : Valid_VmAirWrapper_lt FBB ExtF)
    (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h : allHold air row h_row)
  : allHold_simplified air row h_row := by
    simp at h
    simp [VmAirWrapper_lt_simplification, h]

end VmAirWrapper_lt.constraints
