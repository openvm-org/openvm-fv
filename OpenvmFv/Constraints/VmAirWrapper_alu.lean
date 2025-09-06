import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Extraction.VmAirWrapper_alu
import OpenvmFv.Fundamentals.Interaction
import OpenvmFv.Util

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

namespace VmAirWrapper_alu.constraints

  section constraint_simplification

    -- Note: `air` and `row` are not included as section variables
    --       so that the file can still be used with `sorry`
    --       during the extraction process

    variable [Field F] [Field ExtF]

    section row_constraints

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_0 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_add_flag row 0 = 0 ∨ air.core.opcode_add_flag row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_0_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_0 air row ↔ constraint_0 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_1 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_sub_flag row 0 = 0 ∨ air.core.opcode_sub_flag row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_1_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_1 air row ↔ constraint_1 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_2 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_xor_flag row 0 = 0 ∨ air.core.opcode_xor_flag row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_2_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_2 air row ↔ constraint_2 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_3 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_or_flag row 0 = 0 ∨ air.core.opcode_or_flag row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_3_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_3 air row ↔ constraint_3 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_4 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_and_flag row 0 = 0 ∨ air.core.opcode_and_flag row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_4_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_4 air row ↔ constraint_4 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_5 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_5_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_5 air row ↔ constraint_5 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_6 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_add_flag row 0 = 0 ∨ air.core.carry_add_0 row 0 = 0 ∨ air.core.carry_add_0 row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_6_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_6 air row ↔ constraint_6 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_7 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_sub_flag row 0 = 0 ∨ air.core.carry_sub_0 row 0 = 0 ∨ air.core.carry_sub_0 row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_7_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_7 air row ↔ constraint_7 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_8 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_add_flag row 0 = 0 ∨ air.core.carry_add_1 row 0 = 0 ∨ air.core.carry_add_1 row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_8_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_8 air row ↔ constraint_8 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_9 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_sub_flag row 0 = 0 ∨ air.core.carry_sub_1 row 0 = 0 ∨ air.core.carry_sub_1 row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_9_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_9 air row ↔ constraint_9 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_10 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_add_flag row 0 = 0 ∨ air.core.carry_add_2 row 0 = 0 ∨ air.core.carry_add_2 row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_10_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_10 air row ↔ constraint_10 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_11 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_sub_flag row 0 = 0 ∨ air.core.carry_sub_2 row 0 = 0 ∨ air.core.carry_sub_2 row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_11_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_11 air row ↔ constraint_11 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_12 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_add_flag row 0 = 0 ∨ air.core.carry_add_3 row 0 = 0 ∨ air.core.carry_add_3 row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_12_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_12 air row ↔ constraint_12 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_13 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.opcode_sub_flag row 0 = 0 ∨ air.core.carry_sub_3 row 0 = 0 ∨ air.core.carry_sub_3 row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_13_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_13 air row ↔ constraint_13 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_14 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 0 ∨ air.adapter.rs2_as row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_14_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_14 air row ↔ constraint_14 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_15 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 1 ∨ air.adapter.rs2 row 0 = air.rs2_imm row 0

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_15_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_15 air row ↔ constraint_15 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]
        grind

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_16 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 1 ∨ air.rs2_sign row 0 = air.rs2_limbs row 0 3

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_16_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_16 air row ↔ constraint_16 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]
        grind

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_17 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        (air.adapter.rs2_as row 0 = 1 ∨ air.core.c_2 row 0 = 0 ∨ air.core.c_2 row 0 = 255)

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_17_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_17 air row ↔ constraint_17 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]
        grind

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_18 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.adapter.from_state.timestamp row 0 - air.adapter.reads_aux_0.base.prev_timestamp row 0 - 1 = air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0 + air.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_18_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_18 air row ↔ constraint_18 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_19 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 0 ∨ air.core.is_valid row 0 = 1

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_19_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_19 air row ↔ constraint_19 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_20 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.adapter.rs2_as row 0 = 0 ∨ air.adapter.from_state.timestamp row 0 + 1 - air.adapter.reads_aux_1.base.prev_timestamp row 0 - 1 = air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0 + air.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_20_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_20 air row ↔ constraint_20 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constraint_21 (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ) : Prop :=
        air.core.is_valid row 0 = 0 ∨ air.adapter.from_state.timestamp row 0 + 2 - air.adapter.writes_aux.base.prev_timestamp row 0 - 1 = air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 + air.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072

      @[VmAirWrapper_alu_air_simplification]
      lemma constraint_21_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF) (row : ℕ)
      : VmAirWrapper_alu.extraction.constraint_21 air row ↔ constraint_21 air row := by
        simp_all [openvm_encapsulation,
                  VmAirWrapper_alu_constraint_and_interaction_simplification]

    end row_constraints

    section interactions

      -- Note: use `congr; funext row` after `simp [h]; clear h` in
      --       the lemmas below to get the expression in the infoview

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def executionBus_row [Field ExtF]
        (air : Valid_VmAirWrapper_alu F ExtF)
        (row : ℕ)
      : List (F × List F) :=
        let aa := air.adapter
        let ac := air.core
        [
          (-ac.is_valid row 0, [aa.from_state.pc row 0, aa.from_state.timestamp row 0]),
          (ac.is_valid row 0, [aa.from_state.pc row 0 + 4, aa.from_state.timestamp row 0 + 3])
        ]

      lemma constrain_execution_interactions
        (air : Valid_VmAirWrapper_alu F ExtF)
        (h : VmAirWrapper_alu.extraction.constrain_interactions air)
      :
        air.buses ExecutionBus = (List.range (air.last_row + 1)).flatMap (λ row => executionBus_row air row)
      := by
        unfold VmAirWrapper_alu.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def memoryBus_row [Field ExtF]
        (air : Valid_VmAirWrapper_alu F ExtF)
        (row : ℕ)
      : List (F × List F) :=
        let aa := air.adapter
        let ac := air.core
        [
          (2013265920 * ac.is_valid row 0, [1, aa.rs1_ptr row 0, ac.b_0 row 0, ac.b_1 row 0, ac.b_2 row 0, ac.b_3 row 0, aa.reads_aux_0.base.prev_timestamp row 0]),
          (ac.is_valid row 0, [1, aa.rs1_ptr row 0, ac.b_0 row 0, ac.b_1 row 0, ac.b_2 row 0, ac.b_3 row 0, aa.from_state.timestamp row 0]),
          (2013265920 * aa.rs2_as row 0, [aa.rs2_as row 0, aa.rs2 row 0, ac.c_0 row 0, ac.c_1 row 0, ac.c_2 row 0, ac.c_3 row 0, aa.reads_aux_1.base.prev_timestamp row 0]),
          (aa.rs2_as row 0, [aa.rs2_as row 0, aa.rs2 row 0, ac.c_0 row 0, ac.c_1 row 0, ac.c_2 row 0, ac.c_3 row 0, aa.from_state.timestamp row 0 + 1]),
          (2013265920 * ac.is_valid row 0, [1, aa.rd_ptr row 0, aa.writes_aux.prev_data_0 row 0, aa.writes_aux.prev_data_1 row 0, aa.writes_aux.prev_data_2 row 0, aa.writes_aux.prev_data_3 row 0, aa.writes_aux.base.prev_timestamp row 0]),
          (ac.is_valid row 0, [1, aa.rd_ptr row 0, ac.a_0 row 0, ac.a_1 row 0, ac.a_2 row 0, ac.a_3 row 0, aa.from_state.timestamp row 0 + 2])
        ]

      lemma constrain_memory_interactions
        (air : Valid_VmAirWrapper_alu F ExtF)
        (h : VmAirWrapper_alu.extraction.constrain_interactions air)
      :
        air.buses MemoryBus = (List.range (air.last_row + 1)).flatMap (λ row => memoryBus_row air row)
      := by
        unfold VmAirWrapper_alu.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def rangeBus_row [Field ExtF]
        (air : Valid_VmAirWrapper_alu F ExtF)
        (row : ℕ)
      : List (F × List F) :=
        let aa := air.adapter
        let ac := air.core
        [
          (ac.is_valid row 0, [aa.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
          (ac.is_valid row 0, [aa.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
          (aa.rs2_as row 0, [aa.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
          (aa.rs2_as row 0, [aa.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
          (ac.is_valid row 0, [aa.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
          (ac.is_valid row 0, [aa.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
        ]

      lemma constrain_range_interactions
        (air : Valid_VmAirWrapper_alu F ExtF)
        (h : VmAirWrapper_alu.extraction.constrain_interactions air)
      :
        air.buses RangeCheckerBus = (List.range (air.last_row + 1)).flatMap (λ row => rangeBus_row air row)
      := by
        unfold VmAirWrapper_alu.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def readInstructionBus_row [Field ExtF]
        (air : Valid_VmAirWrapper_alu F ExtF)
        (row : ℕ)
      : List (F × List F) :=
        let aa := air.adapter
        let ac := air.core
        [
          (ac.is_valid row 0, [aa.from_state.pc row 0,
                              (ac.ctx row 0).instruction.opcode,
                              aa.rd_ptr row 0,
                              aa.rs1_ptr row 0,
                              aa.rs2 row 0,
                              1,
                              aa.rs2_as row 0,
                              0,
                              0])
        ]

      lemma constrain_readInstruction_interactions
        (air : Valid_VmAirWrapper_alu F ExtF)
        (h : VmAirWrapper_alu.extraction.constrain_interactions air)
      :
        air.buses ReadInstructionBus = (List.range (air.last_row + 1)).flatMap (λ row => readInstructionBus_row air row)
      := by
        unfold VmAirWrapper_alu.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def bitwiseBus_row [Field ExtF]
        (air : Valid_VmAirWrapper_alu F ExtF)
        (row : ℕ)
      : List (F × List F) :=
        let aa := air.adapter
        let ac := air.core
        [
          (ac.is_valid row 0, [ac.x_0 row 0, ac.y_0 row 0, ac.x_xor_y_0 row 0, 1]),
          (ac.is_valid row 0, [ac.x_1 row 0, ac.y_1 row 0, ac.x_xor_y_1 row 0, 1]),
          (ac.is_valid row 0, [ac.x_2 row 0, ac.y_2 row 0, ac.x_xor_y_2 row 0, 1]),
          (ac.is_valid row 0, [ac.x_3 row 0, ac.y_3 row 0, ac.x_xor_y_3 row 0, 1]),
          (ac.is_valid row 0 - aa.rs2_as row 0, [ac.c_0 row 0, ac.c_1 row 0, 0, 0])
        ]

      lemma constrain_bitwise_interactions
        (air : Valid_VmAirWrapper_alu F ExtF)
        (h : VmAirWrapper_alu.extraction.constrain_interactions air)
      :
        air.buses BitwiseBus = (List.range (air.last_row + 1)).flatMap (λ row => bitwiseBus_row air row)
      := by
        unfold VmAirWrapper_alu.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        simp [h]; clear h
        rfl

      @[VmAirWrapper_alu_constraint_and_interaction_simplification]
      def constrain_interactions (air : Valid_VmAirWrapper_alu F ExtF) : Prop :=
        air.buses = fun index ↦
        if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
        else if index = MemoryBus then (List.range (air.last_row + 1)).flatMap (memoryBus_row air)
        else if index = RangeCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeBus_row air)
        else if index = ReadInstructionBus then (List.range (air.last_row + 1)).flatMap (readInstructionBus_row air)
        else if index = BitwiseBus then (List.range (air.last_row + 1)).flatMap (bitwiseBus_row air)
        else []

      @[VmAirWrapper_alu_air_simplification]
      lemma constrain_interactions_of_extraction
        (air : Valid_VmAirWrapper_alu F ExtF)
        (h : VmAirWrapper_alu.extraction.constrain_interactions air)
      : constrain_interactions air := by
        unfold VmAirWrapper_alu.extraction.constrain_interactions at h
        simp [openvm_encapsulation] at h
        exact h

    end interactions

  end constraint_simplification

  section allHold

    variable [Field F] [Field ExtF]

    -- TODO: have extractor generate this and put it in extraction file
    @[simp]
    def extracted_row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_alu F ExtF)
      (row : ℕ)
    : List Prop :=
      [
        VmAirWrapper_alu.extraction.constraint_0 air row,
        VmAirWrapper_alu.extraction.constraint_1 air row,
        VmAirWrapper_alu.extraction.constraint_2 air row,
        VmAirWrapper_alu.extraction.constraint_3 air row,
        VmAirWrapper_alu.extraction.constraint_4 air row,
        VmAirWrapper_alu.extraction.constraint_5 air row,
        VmAirWrapper_alu.extraction.constraint_6 air row,
        VmAirWrapper_alu.extraction.constraint_7 air row,
        VmAirWrapper_alu.extraction.constraint_8 air row,
        VmAirWrapper_alu.extraction.constraint_9 air row,
        VmAirWrapper_alu.extraction.constraint_10 air row,
        VmAirWrapper_alu.extraction.constraint_11 air row,
        VmAirWrapper_alu.extraction.constraint_12 air row,
        VmAirWrapper_alu.extraction.constraint_13 air row,
        VmAirWrapper_alu.extraction.constraint_14 air row,
        VmAirWrapper_alu.extraction.constraint_15 air row,
        VmAirWrapper_alu.extraction.constraint_16 air row,
        VmAirWrapper_alu.extraction.constraint_17 air row,
        VmAirWrapper_alu.extraction.constraint_18 air row,
        VmAirWrapper_alu.extraction.constraint_19 air row,
        VmAirWrapper_alu.extraction.constraint_20 air row,
        VmAirWrapper_alu.extraction.constraint_21 air row
      ]

    -- TODO have extractor generate this and put in extraction file
    @[simp]
    def allHold
      [Field ExtF]
      (air : Valid_VmAirWrapper_alu F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      VmAirWrapper_alu.extraction.constrain_interactions air ∧
      List.Forall (·) (extracted_row_constraint_list air row)

    @[simp]
    def row_constraint_list
      [Field ExtF]
      (air : Valid_VmAirWrapper_alu F ExtF)
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
        constraint_21 air row
      ]

    @[simp]
    def allHold_simplified
      (air : Valid_VmAirWrapper_alu F ExtF)
      (row : ℕ)
      (_ : row ≤ air.last_row)
    : Prop :=
      constrain_interactions air ∧
      List.Forall (·) (row_constraint_list air row)

    lemma allHold_simplified_of_allHold
      (air : Valid_VmAirWrapper_alu F ExtF)
      (row : ℕ)
      (h_row : row ≤ air.last_row)
    : allHold air row h_row ↔ allHold_simplified air row h_row := by
      unfold allHold allHold_simplified
      apply Iff.and
      . unfold VmAirWrapper_alu.extraction.constrain_interactions
        simp [openvm_encapsulation]
        rfl
      . simp only [extracted_row_constraint_list,
                   row_constraint_list,
                   VmAirWrapper_alu_air_simplification]

  end allHold

  section properties

    variable[Field ExtF]

    lemma single_op
      (air : Valid_VmAirWrapper_alu FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
    :
      let is_add := air.core.opcode_add_flag row 0
      let is_sub := air.core.opcode_sub_flag row 0
      let is_xor := air.core.opcode_xor_flag row 0
      let is_or := air.core.opcode_or_flag row 0
      let is_and := air.core.opcode_and_flag row 0
      (is_add = 1 → is_sub = 0 ∧ is_xor = 0 ∧ is_or = 0 ∧ is_and = 0) ∧
      (is_sub = 1 → is_add = 0 ∧ is_xor = 0 ∧ is_or = 0 ∧ is_and = 0) ∧
      (is_xor = 1 → is_add = 0 ∧ is_sub = 0 ∧ is_or = 0 ∧ is_and = 0) ∧
      (is_or = 1 → is_add = 0 ∧ is_sub = 0 ∧ is_xor = 0 ∧ is_and = 0) ∧
      (is_and = 1 → is_add = 0 ∧ is_sub = 0 ∧ is_xor = 0 ∧ is_or = 0)
    := by
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, h3, h4, h5, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_alu_constraint_and_interaction_simplification] at h0 h1 h2 h3 h4 h5
      rw [Valid_BaseAluCoreAir.is_valid] at h5
      grind (splits := 23)

    lemma op_from_opcode
      (air : Valid_VmAirWrapper_alu FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
      (is_valid : air.core.is_valid row 0 = 1)
    :
      let is_add := air.core.opcode_add_flag row 0
      let is_sub := air.core.opcode_sub_flag row 0
      let is_xor := air.core.opcode_xor_flag row 0
      let is_or := air.core.opcode_or_flag row 0
      let is_and := air.core.opcode_and_flag row 0
      ((air.core.ctx row 0).instruction.opcode = 512 → is_add = 1) ∧
      ((air.core.ctx row 0).instruction.opcode = 513 → is_sub = 1) ∧
      ((air.core.ctx row 0).instruction.opcode = 514 → is_xor = 1) ∧
      ((air.core.ctx row 0).instruction.opcode = 515 → is_or = 1) ∧
      ((air.core.ctx row 0).instruction.opcode = 516 → is_and = 1)
    := by
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, h3, h4, h5, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_alu_constraint_and_interaction_simplification] at *
      rw [Valid_BaseAluCoreAir.is_valid] at h5
      rw [← BaseAluCoreAir.is_valid_def] at is_valid
      rw [← BaseAluCoreAir.ctx.instruction.opcode_def]
      grind

    lemma opcode_bounds
      (air : Valid_VmAirWrapper_alu FBB ExtF)
      (row : ℕ)
      (valid_row : row ≤ air.last_row)
      (cstrs : allHold air row valid_row)
      (is_valid : air.core.is_valid row 0 = 1)
    :
      (air.core.ctx row 0).instruction.opcode = 512 ∨
      (air.core.ctx row 0).instruction.opcode = 513 ∨
      (air.core.ctx row 0).instruction.opcode = 514 ∨
      (air.core.ctx row 0).instruction.opcode = 515 ∨
      (air.core.ctx row 0).instruction.opcode = 516
    := by
      have ⟨ sop1, sop2, sop3, sop4, sop5 ⟩ := single_op air row valid_row cstrs
      rw [← BaseAluCoreAir.ctx.instruction.opcode_def]
      rw [← BaseAluCoreAir.is_valid_def] at is_valid
      rw [allHold_simplified_of_allHold air row valid_row] at cstrs
      obtain ⟨ hint, h0, h1, h2, h3, h4, h5, rest ⟩ := cstrs
      clear hint rest
      simp [VmAirWrapper_alu_constraint_and_interaction_simplification] at *
      grind

  end properties

end VmAirWrapper_alu.constraints

namespace Interaction

/-- ALU-related ReadInstruction bus assumptions -/
def readInstructionBus_assumptions_ALU
  (mul _ opcode rd rs1 rs2 xd rs2_as xf xg : FBB)
: Prop :=
  ¬ mul = 0 →
    -- rd and rs1 boundaries
    rd.val < 32 ∧ rs1.val < 32 ∧
    -- non-immediate rs2
    (rs2_as = 1 → rs2.val < 32) ∧
    -- immediate rs2
    (rs2_as = 0 →
      -- opcode cannot be SUB
      ¬ opcode = 513 ∧
      -- immediate fits 24 bits
      rs2.val < 2 ^ 24 ∧
      -- immediate is a sign-extended 12-bit value
      (BitVec.ofNat 24 rs2.val).toInt = (BitVec.ofNat 12 rs2.val).toInt) ∧
    -- unused parameters
    xd = 1 ∧ xf = 0 ∧ xg = 0

end Interaction

namespace VmAirWrapper_alu.auxiliaries

lemma byte_xor_as_and
  {a b : ℕ}
  (ub_a : a < 256)
  (ub_b : b < 256)
:
  a ^^^ b = (a + b) - 2 * (a &&& b)
:= by
  have lt_b_and_c := @Nat.and_le_left a b
  have bv_xor_as_and : forall (a b : BitVec 9), a ^^^ b = (a + b) - 2 * (a &&& b) := by bv_decide
  specialize bv_xor_as_and { toFin := ⟨ a, by omega⟩ } { toFin := ⟨ b, by omega⟩ }
  simp [← BitVec.toNat_inj, Fin.add_def] at bv_xor_as_and
  rw [Nat.mod_eq_of_lt (a := 2 * (a &&& b)) (by omega)] at bv_xor_as_and
  have : (512 - 2 * (a &&& b) + (a + b)) % 512 < 256 := by rw [← bv_xor_as_and]; exact Nat.xor_lt_two_pow (n := 8) ub_a ub_b
  have : (512 - 2 * (a &&& b) + (a + b)) % 512 = (a + b) - 2 * (a &&& b) := by omega
  rw [this] at bv_xor_as_and
  exact bv_xor_as_and

lemma byte_xor_as_or
  {a b : ℕ}
  (ub_a : a < 256)
  (ub_b : b < 256)
:
  a ^^^ b = 2 * (a ||| b) - (a + b)
:= by
  have := @Nat.left_le_or a b
  have := @Nat.or_lt_two_pow a b 8 ub_a ub_b
  have bv_xor_as_or : forall (a b : BitVec 9), a ^^^ b = 2 * (a ||| b) - (a + b) := by bv_decide
  specialize bv_xor_as_or { toFin := ⟨ a, by omega⟩ } { toFin := ⟨ b, by omega⟩ }
  simp [← BitVec.toNat_inj, Fin.add_def] at bv_xor_as_or
  rw [Nat.mod_eq_of_lt (a := a + b) (by omega)] at bv_xor_as_or
  have : (512 - (a + b) + 2 * (a ||| b)) % 512 < 256 := by rw [← bv_xor_as_or]; exact Nat.xor_lt_two_pow (n := 8) ub_a ub_b
  have : (512 - (a + b) + 2 * (a ||| b)) % 512 = 2 * (a ||| b) - (a + b) := by omega
  rw [this] at bv_xor_as_or
  exact bv_xor_as_or

lemma FBB_xor_as_and
  {a b c : FBB}
  (ub_b : b.val < 256)
  (ub_c : c.val < 256)
  (h_eq : (b + c - 2 * a).val = b.val ^^^ c.val)
:
  a.val < 256 ∧ a.val = b.val &&& c.val
:= by
  have := @Nat.and_le_left b c
  have := @Nat.and_le_right b c
  rw [byte_xor_as_and ub_b ub_c] at h_eq
  simp [Fin.add_def, Fin.sub_def, Fin.mul_def] at *
  grind

lemma FBB_xor_as_or
  {a b c : FBB}
  (ub_b : b.val < 256)
  (ub_c : c.val < 256)
  (h_eq : (2 * a - b - c).val = b.val ^^^ c.val)
:
  a.val < 256 ∧ a.val = b.val ||| c.val
:= by
  have := @Nat.or_lt_two_pow b c 8 ub_b ub_c
  have := @Nat.left_le_or b c
  have := @Nat.right_le_or b c
  rw [byte_xor_as_or ub_b ub_c] at h_eq
  grind

end VmAirWrapper_alu.auxiliaries
