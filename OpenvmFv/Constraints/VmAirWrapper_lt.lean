import OpenvmFv.Airs.Alu.VmAirWrapper_lt
import OpenvmFv.Extraction.VmAirWrapper_lt
import OpenvmFv.Util

namespace VmAirWrapper_lt.constraints

  lemma constraint_0' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_0 c row)
  : c.core.opcode_slt_flag row 0 = 0 ∨ c.core.opcode_slt_flag row 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_0 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_1' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_1 c row)
  : c.core.opcode_sltu_flag row 0 = 0 ∨ c.core.opcode_sltu_flag row 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_1 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_2' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_2 c row)
  : c.core.is_valid row 0 = 0 ∨ c.core.is_valid row 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_2 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_3' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_3 c row)
  : c.core.cmp_result row 0 = 0 ∨ c.core.cmp_result row 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_3 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_4' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_4 c row)
  : c.core.b_3 row 0 = c.core.b_msb_f row 0 ∨ 256 = c.core.b_3 row 0 - c.core.b_msb_f row 0 := by
    unfold VmAirWrapper_lt.extraction.constraint_4 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_5' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_5 c row)
  : c.core.c_3 row 0 = c.core.c_msb_f row 0 ∨ 256 = c.core.c_3 row 0 - c.core.c_msb_f row 0 := by
    unfold VmAirWrapper_lt.extraction.constraint_5 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_6' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_6 c row)
  : c.core.diff_marker_3 row 0 = 0 ∨ c.core.diff_marker_3 row 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_6 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_7' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_7 c row)
  : 1 = c.core.diff_marker_3 row 0 ∨ c.core.diff row 0 3 = 0 := by
    unfold VmAirWrapper_lt.extraction.constraint_7 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_8' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_8 c row)
  : c.core.diff_marker_3 row 0 = 0 ∨ c.core.diff_val row 0 = c.core.diff row 0 3 := by
    unfold VmAirWrapper_lt.extraction.constraint_8 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_9' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_9 c row)
  : c.core.diff_marker_2 row 0 = 0 ∨ c.core.diff_marker_2 row 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_9 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_10' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_10 c row)
  : 1 = c.core.prefix_sum row 0 2 ∨ c.core.diff row 0 2 = 0 := by
    unfold VmAirWrapper_lt.extraction.constraint_10 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_11' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_11 c row)
  : c.core.diff_marker_2 row 0 = 0 ∨ c.core.diff_val row 0 = c.core.diff row 0 2 := by
    unfold VmAirWrapper_lt.extraction.constraint_11 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_12' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_12 c row)
  : c.core.diff_marker_1 row 0 = 0 ∨ c.core.diff_marker_1 row 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_12 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_13' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_13 c row)
  : 1 = c.core.prefix_sum row 0 2 + c.core.diff_marker_1 row 0 ∨ c.core.diff row 0 1 = 0 := by
    unfold VmAirWrapper_lt.extraction.constraint_13 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_14' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_14 c row)
  : c.core.diff_marker_1 row 0 = 0 ∨ c.core.diff_val row 0 = c.core.diff row 0 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_14 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_15' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_15 c row)
  : c.core.diff_marker_0 row 0 = 0 ∨ c.core.diff_marker_0 row 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_15 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_16' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_16 c row)
  : 1 = c.core.prefix_sum row 0 0 ∨ c.core.diff row 0 0 = 0 := by
    unfold VmAirWrapper_lt.extraction.constraint_16 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_17' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_17 c row)
  : c.core.diff_marker_0 row 0 = 0 ∨ c.core.diff_val row 0 = c.core.diff row 0 0 := by
    unfold VmAirWrapper_lt.extraction.constraint_17 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_18' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_18 c row)
  : c.core.prefix_sum row 0 0 = 0 ∨ c.core.prefix_sum row 0 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_18 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_19' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_19 c row)
  : 1 = c.core.prefix_sum row 0 0 ∨ c.core.cmp_result row 0 = 0 := by
    unfold VmAirWrapper_lt.extraction.constraint_19 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_20' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_20 c row)
  : c.adapter.rs2_as row 0 = 0 ∨ c.adapter.rs2_as row 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_20 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_21' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_21 c row)
  : 1 = c.adapter.rs2_as row 0 ∨ c.adapter.rs2 row 0 = c.rs2_imm row 0 := by
    unfold VmAirWrapper_lt.extraction.constraint_21 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_22' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_22 c row)
  : 1 = c.adapter.rs2_as row 0 ∨ c.rs2_sign row 0 = c.rs2_limbs row 0 3 := by
    unfold VmAirWrapper_lt.extraction.constraint_22 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_23' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_23 c row)
  : 1 = c.adapter.rs2_as row 0 ∨ c.rs2_sign row 0 = 0 ∨ 255 = c.rs2_sign row 0 := by
    unfold VmAirWrapper_lt.extraction.constraint_23 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_24' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_24 c row)
  : c.core.is_valid row 0 = 0 ∨
  c.adapter.from_state.timestamp row 0 - c.adapter.reads_aux_0.base.prev_timestamp row 0 - 1 =
    c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0 +
      c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072 := by
    unfold VmAirWrapper_lt.extraction.constraint_24 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_25' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_25 c row)
  : c.adapter.rs2_as row 0 = 0 ∨ c.core.is_valid row 0 = 1 := by
    unfold VmAirWrapper_lt.extraction.constraint_25 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_26' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_26 c row)
  : c.adapter.rs2_as row 0 = 0 ∨
  c.adapter.from_state.timestamp row 0 + 1 - c.adapter.reads_aux_1.base.prev_timestamp row 0 - 1 =
    c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0 +
      c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072 := by
    unfold VmAirWrapper_lt.extraction.constraint_26 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constraint_27' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF) (row: ℕ)
    (h: VmAirWrapper_lt.extraction.constraint_27 c row)
  : c.core.is_valid row 0 = 0 ∨
  c.adapter.from_state.timestamp row 0 + 2 - c.adapter.writes_aux.base.prev_timestamp row 0 - 1 =
    c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 +
      c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072 := by
    unfold VmAirWrapper_lt.extraction.constraint_27 at h
    simp [openvm_encapsulation, *] at h
    exact h

  lemma constrain_interactions' [Field F] [Field ExtF]
    (c: Valid_VmAirWrapper_lt F ExtF)
    (h: VmAirWrapper_lt.extraction.constrain_interactions c)
  : c.buses = fun index ↦
  if index = ExecutionBus then
    List.map (fun row ↦ (-c.core.is_valid row 0, [c.adapter.from_state.pc row 0, c.adapter.from_state.timestamp row 0]))
        (List.range (c.last_row + 1)) ++
      List.map
        (fun row ↦
          (c.core.is_valid row 0, [c.adapter.from_state.pc row 0 + 4, c.adapter.from_state.timestamp row 0 + 3]))
        (List.range (c.last_row + 1))
  else
    if index = MemoryBus then
      List.map
          (fun row ↦
            (2013265920 * c.core.is_valid row 0,
              [1, c.adapter.rs1_ptr row 0, c.core.b_0 row 0, c.core.b_1 row 0, c.core.b_2 row 0, c.core.b_3 row 0,
                c.adapter.reads_aux_0.base.prev_timestamp row 0]))
          (List.range (c.last_row + 1)) ++
        (List.map
            (fun row ↦
              (c.core.is_valid row 0,
                [1, c.adapter.rs1_ptr row 0, c.core.b_0 row 0, c.core.b_1 row 0, c.core.b_2 row 0, c.core.b_3 row 0,
                  c.adapter.from_state.timestamp row 0]))
            (List.range (c.last_row + 1)) ++
          (List.map
              (fun row ↦
                (2013265920 * c.adapter.rs2_as row 0,
                  [c.adapter.rs2_as row 0, c.adapter.rs2 row 0, c.core.c_0 row 0, c.core.c_1 row 0, c.core.c_2 row 0,
                    c.core.c_3 row 0, c.adapter.reads_aux_1.base.prev_timestamp row 0]))
              (List.range (c.last_row + 1)) ++
            (List.map
                (fun row ↦
                  (c.adapter.rs2_as row 0,
                    [c.adapter.rs2_as row 0, c.adapter.rs2 row 0, c.core.c_0 row 0, c.core.c_1 row 0, c.core.c_2 row 0,
                      c.core.c_3 row 0, c.adapter.from_state.timestamp row 0 + 1]))
                (List.range (c.last_row + 1)) ++
              (List.map
                  (fun row ↦
                    (2013265920 * c.core.is_valid row 0,
                      [1, c.adapter.rd_ptr row 0, c.adapter.writes_aux.prev_data_0 row 0,
                        c.adapter.writes_aux.prev_data_1 row 0, c.adapter.writes_aux.prev_data_2 row 0,
                        c.adapter.writes_aux.prev_data_3 row 0, c.adapter.writes_aux.base.prev_timestamp row 0]))
                  (List.range (c.last_row + 1)) ++
                List.map
                  (fun row ↦
                    (c.core.is_valid row 0,
                      [1, c.adapter.rd_ptr row 0, c.core.cmp_result row 0, 0, 0, 0,
                        c.adapter.from_state.timestamp row 0 + 2]))
                  (List.range (c.last_row + 1))))))
    else
      if index = RangeCheckerBus then
        List.map
            (fun row ↦ (c.core.is_valid row 0, [c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]))
            (List.range (c.last_row + 1)) ++
          (List.map
              (fun row ↦
                (c.core.is_valid row 0, [c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]))
              (List.range (c.last_row + 1)) ++
            (List.map
                (fun row ↦
                  (c.adapter.rs2_as row 0, [c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]))
                (List.range (c.last_row + 1)) ++
              (List.map
                  (fun row ↦
                    (c.adapter.rs2_as row 0, [c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]))
                  (List.range (c.last_row + 1)) ++
                (List.map
                    (fun row ↦
                      (c.core.is_valid row 0, [c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]))
                    (List.range (c.last_row + 1)) ++
                  List.map
                    (fun row ↦
                      (c.core.is_valid row 0, [c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]))
                    (List.range (c.last_row + 1))))))
      else
        if index = ReadInstructionBus then
          List.map
            (fun row ↦
              (c.core.is_valid row 0,
                [c.adapter.from_state.pc row 0, c.core.opcode_sltu_flag row 0 + 520, c.adapter.rd_ptr row 0,
                  c.adapter.rs1_ptr row 0, c.adapter.rs2 row 0, 1, c.adapter.rs2_as row 0, 0, 0]))
            (List.range (c.last_row + 1))
        else
          if index = BitwiseBus then
            List.map
                (fun row ↦
                  (c.core.is_valid row 0,
                    [c.core.b_msb_f row 0 + 128 * c.core.opcode_slt_flag row 0,
                      c.core.c_msb_f row 0 + 128 * c.core.opcode_slt_flag row 0, 0, 0]))
                (List.range (c.last_row + 1)) ++
              (List.map (fun row ↦ (c.core.prefix_sum row 0 0, [c.core.diff_val row 0 - 1, 0, 0, 0]))
                  (List.range (c.last_row + 1)) ++
                List.map
                  (fun row ↦
                    (c.core.is_valid row 0 - c.adapter.rs2_as row 0, [c.core.c_0 row 0, c.core.c_1 row 0, 0, 0]))
                  (List.range (c.last_row + 1)))
          else [] := by
    unfold VmAirWrapper_lt.extraction.constrain_interactions at h
    simp [openvm_encapsulation] at h
    exact h

end VmAirWrapper_lt.constraints
