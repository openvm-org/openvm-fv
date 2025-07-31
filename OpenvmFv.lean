import OpenvmFv.Basic
import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Extraction.VmAirWrapper_alu

lemma constraint_0' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_0 c row)
: c.core.opcode_add_flag row 0 = 0 ∨ c.core.opcode_add_flag row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_0 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_1' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_1 c row)
: c.core.opcode_sub_flag row 0 = 0 ∨ c.core.opcode_sub_flag row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_1 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_2' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_2 c row)
: c.core.opcode_xor_flag row 0 = 0 ∨ c.core.opcode_xor_flag row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_2 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_3' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_3 c row)
: c.core.opcode_or_flag row 0 = 0 ∨ c.core.opcode_or_flag row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_3 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_4' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_4 c row)
: c.core.opcode_and_flag row 0 = 0 ∨ c.core.opcode_and_flag row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_4 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_5' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_5 c row)
: c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
        c.core.opcode_or_flag row 0 +
      c.core.opcode_and_flag row 0 =
    0 ∨
  c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
          c.core.opcode_or_flag row 0 +
        c.core.opcode_and_flag row 0 -
      1 =
    0 := by
  unfold VmAirWrapper_alu.extraction.constraint_5 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_6' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_6 c row)
: c.core.opcode_add_flag row 0 = 0 ∨
  ((2005401601 : F) = 0 ∨ c.core.b_0 row 0 + c.core.c_0 row 0 - c.core.a_0 row 0 = 0) ∨
    2005401601 * (c.core.b_0 row 0 + c.core.c_0 row 0 - c.core.a_0 row 0) - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_6 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_7' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_7 c row)
: c.core.opcode_sub_flag row 0 = 0 ∨
    ((2005401601 : F) = 0 ∨ c.core.a_0 row 0 + c.core.c_0 row 0 - c.core.b_0 row 0 = 0) ∨
      2005401601 * (c.core.a_0 row 0 + c.core.c_0 row 0 - c.core.b_0 row 0) - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_7 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_8' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_8 c row)
: c.core.opcode_add_flag row 0 = 0 ∨
    ((2005401601 : F) = 0 ∨
        c.core.b_1 row 0 + c.core.c_1 row 0 - c.core.a_1 row 0 +
            2005401601 * (c.core.b_0 row 0 + c.core.c_0 row 0 - c.core.a_0 row 0) =
          0) ∨
      2005401601 *
            (c.core.b_1 row 0 + c.core.c_1 row 0 - c.core.a_1 row 0 +
              2005401601 * (c.core.b_0 row 0 + c.core.c_0 row 0 - c.core.a_0 row 0)) -
          1 =
        0 := by
  unfold VmAirWrapper_alu.extraction.constraint_8 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_9' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_9 c row)
: c.core.opcode_sub_flag row 0 = 0 ∨
    ((2005401601 : F) = 0 ∨
        c.core.a_1 row 0 + c.core.c_1 row 0 - c.core.b_1 row 0 +
            2005401601 * (c.core.a_0 row 0 + c.core.c_0 row 0 - c.core.b_0 row 0) =
          0) ∨
      2005401601 *
            (c.core.a_1 row 0 + c.core.c_1 row 0 - c.core.b_1 row 0 +
              2005401601 * (c.core.a_0 row 0 + c.core.c_0 row 0 - c.core.b_0 row 0)) -
          1 =
        0 := by
  unfold VmAirWrapper_alu.extraction.constraint_9 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_10' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_10 c row)
: c.core.opcode_add_flag row 0 = 0 ∨
    ((2005401601 : F) = 0 ∨
        c.core.b_2 row 0 + c.core.c_2 row 0 - c.core.a_2 row 0 +
            2005401601 *
              (c.core.b_1 row 0 + c.core.c_1 row 0 - c.core.a_1 row 0 +
                2005401601 * (c.core.b_0 row 0 + c.core.c_0 row 0 - c.core.a_0 row 0)) =
          0) ∨
      2005401601 *
            (c.core.b_2 row 0 + c.core.c_2 row 0 - c.core.a_2 row 0 +
              2005401601 *
                (c.core.b_1 row 0 + c.core.c_1 row 0 - c.core.a_1 row 0 +
                  2005401601 * (c.core.b_0 row 0 + c.core.c_0 row 0 - c.core.a_0 row 0))) -
          1 =
        0 := by
  unfold VmAirWrapper_alu.extraction.constraint_10 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_11' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_11 c row)
: c.core.opcode_sub_flag row 0 = 0 ∨
    ((2005401601 : F) = 0 ∨
        c.core.a_2 row 0 + c.core.c_2 row 0 - c.core.b_2 row 0 +
            2005401601 *
              (c.core.a_1 row 0 + c.core.c_1 row 0 - c.core.b_1 row 0 +
                2005401601 * (c.core.a_0 row 0 + c.core.c_0 row 0 - c.core.b_0 row 0)) =
          0) ∨
      2005401601 *
            (c.core.a_2 row 0 + c.core.c_2 row 0 - c.core.b_2 row 0 +
              2005401601 *
                (c.core.a_1 row 0 + c.core.c_1 row 0 - c.core.b_1 row 0 +
                  2005401601 * (c.core.a_0 row 0 + c.core.c_0 row 0 - c.core.b_0 row 0))) -
          1 =
        0 := by
  unfold VmAirWrapper_alu.extraction.constraint_11 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_12' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_12 c row)
: c.core.opcode_add_flag row 0 = 0 ∨
    ((2005401601 : F) = 0 ∨
        c.core.b_3 row 0 + c.core.c_3 row 0 - c.core.a_3 row 0 +
            2005401601 *
              (c.core.b_2 row 0 + c.core.c_2 row 0 - c.core.a_2 row 0 +
                2005401601 *
                  (c.core.b_1 row 0 + c.core.c_1 row 0 - c.core.a_1 row 0 +
                    2005401601 * (c.core.b_0 row 0 + c.core.c_0 row 0 - c.core.a_0 row 0))) =
          0) ∨
      2005401601 *
            (c.core.b_3 row 0 + c.core.c_3 row 0 - c.core.a_3 row 0 +
              2005401601 *
                (c.core.b_2 row 0 + c.core.c_2 row 0 - c.core.a_2 row 0 +
                  2005401601 *
                    (c.core.b_1 row 0 + c.core.c_1 row 0 - c.core.a_1 row 0 +
                      2005401601 * (c.core.b_0 row 0 + c.core.c_0 row 0 - c.core.a_0 row 0)))) -
          1 =
        0 := by
  unfold VmAirWrapper_alu.extraction.constraint_12 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_13' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_13 c row)
: c.core.opcode_sub_flag row 0 = 0 ∨
    ((2005401601 : F) = 0 ∨
        c.core.a_3 row 0 + c.core.c_3 row 0 - c.core.b_3 row 0 +
            2005401601 *
              (c.core.a_2 row 0 + c.core.c_2 row 0 - c.core.b_2 row 0 +
                2005401601 *
                  (c.core.a_1 row 0 + c.core.c_1 row 0 - c.core.b_1 row 0 +
                    2005401601 * (c.core.a_0 row 0 + c.core.c_0 row 0 - c.core.b_0 row 0))) =
          0) ∨
      2005401601 *
            (c.core.a_3 row 0 + c.core.c_3 row 0 - c.core.b_3 row 0 +
              2005401601 *
                (c.core.a_2 row 0 + c.core.c_2 row 0 - c.core.b_2 row 0 +
                  2005401601 *
                    (c.core.a_1 row 0 + c.core.c_1 row 0 - c.core.b_1 row 0 +
                      2005401601 * (c.core.a_0 row 0 + c.core.c_0 row 0 - c.core.b_0 row 0)))) -
          1 =
        0 := by
  unfold VmAirWrapper_alu.extraction.constraint_13 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_14' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_14 c row)
: c.adapter.rs2_as row 0 = 0 ∨ c.adapter.rs2_as row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_14 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_15' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_15 c row)
: 1 - c.adapter.rs2_as row 0 = 0 ∨
    c.adapter.rs2 row 0 - (c.core.c_0 row 0 + c.core.c_1 row 0 * 256 + c.core.c_2 row 0 * 65536) = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_15 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_16' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_16 c row)
: 1 - c.adapter.rs2_as row 0 = 0 ∨ c.core.c_2 row 0 - c.core.c_3 row 0 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_16 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_17' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_17 c row)
: 1 - c.adapter.rs2_as row 0 = 0 ∨ c.core.c_2 row 0 = 0 ∨ 255 - c.core.c_2 row 0 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_17 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_18' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_18 c row)
: c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
        c.core.opcode_or_flag row 0 +
      c.core.opcode_and_flag row 0 =
    0 ∨
  c.adapter.from_state.timestamp row 0 - c.adapter.reads_aux_0.base.prev_timestamp row 0 - 1 -
      (c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072) =
    0 := by
  unfold VmAirWrapper_alu.extraction.constraint_18 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_19' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_19 c row)
: c.adapter.rs2_as row 0 = 0 ∨
    c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
            c.core.opcode_or_flag row 0 +
          c.core.opcode_and_flag row 0 -
        1 =
      0 := by
  unfold VmAirWrapper_alu.extraction.constraint_19 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_20' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_20 c row)
: c.adapter.rs2_as row 0 = 0 ∨
  c.adapter.from_state.timestamp row 0 + 1 - c.adapter.reads_aux_1.base.prev_timestamp row 0 - 1 -
      (c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072) =
    0 := by
  unfold VmAirWrapper_alu.extraction.constraint_20 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constraint_21' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_21 c row)
: c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
        c.core.opcode_or_flag row 0 +
      c.core.opcode_and_flag row 0 =
    0 ∨
  c.adapter.from_state.timestamp row 0 + 2 - c.adapter.writes_aux.base.prev_timestamp row 0 - 1 -
      (c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0 +
        c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0 * 131072) =
    0 := by
  unfold VmAirWrapper_alu.extraction.constraint_21 at h
  simp [openvm_encapsulation, *] at h
  exact h

lemma constrain_interactions' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF)
  (h: VmAirWrapper_alu.extraction.constrain_interactions c)
: c.buses = fun index ↦
  if index = 1 then
    List.map
        (fun row ↦
          (2013265920 *
              (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                  c.core.opcode_or_flag row 0 +
                c.core.opcode_and_flag row 0),
            [1, c.adapter.rs1_ptr row 0, c.core.b_0 row 0, c.core.b_1 row 0, c.core.b_2 row 0, c.core.b_3 row 0,
              c.adapter.reads_aux_0.base.prev_timestamp row 0]))
        (List.range (c.last_row + 1)) ++
      (List.map
          (fun row ↦
            (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                  c.core.opcode_or_flag row 0 +
                c.core.opcode_and_flag row 0,
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
                  (2013265920 *
                      (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                          c.core.opcode_or_flag row 0 +
                        c.core.opcode_and_flag row 0),
                    [1, c.adapter.rd_ptr row 0, c.adapter.writes_aux.prev_data_0 row 0,
                      c.adapter.writes_aux.prev_data_1 row 0, c.adapter.writes_aux.prev_data_2 row 0,
                      c.adapter.writes_aux.prev_data_3 row 0, c.adapter.writes_aux.base.prev_timestamp row 0]))
                (List.range (c.last_row + 1)) ++
              List.map
                (fun row ↦
                  (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                        c.core.opcode_or_flag row 0 +
                      c.core.opcode_and_flag row 0,
                    [1, c.adapter.rd_ptr row 0, c.core.a_0 row 0, c.core.a_1 row 0, c.core.a_2 row 0, c.core.a_3 row 0,
                      c.adapter.from_state.timestamp row 0 + 2]))
                (List.range (c.last_row + 1))))))
  else
    if index = 0 then
      List.map
          (fun row ↦
            (-c.core.opcode_and_flag row 0 +
                (-c.core.opcode_or_flag row 0 +
                  (-c.core.opcode_xor_flag row 0 + (-c.core.opcode_sub_flag row 0 + -c.core.opcode_add_flag row 0))),
              [c.adapter.from_state.pc row 0, c.adapter.from_state.timestamp row 0]))
          (List.range (c.last_row + 1)) ++
        List.map
          (fun row ↦
            (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                  c.core.opcode_or_flag row 0 +
                c.core.opcode_and_flag row 0,
              [c.adapter.from_state.pc row 0 + 4, c.adapter.from_state.timestamp row 0 + 3]))
          (List.range (c.last_row + 1))
    else
      if index = 8 then
        List.map
          (fun row ↦
            (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                  c.core.opcode_or_flag row 0 +
                c.core.opcode_and_flag row 0,
              [c.adapter.from_state.pc row 0,
                512 +
                  (c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 * 2 + c.core.opcode_or_flag row 0 * 3 +
                    c.core.opcode_and_flag row 0 * 4),
                c.adapter.rd_ptr row 0, c.adapter.rs1_ptr row 0, c.adapter.rs2 row 0, 1, c.adapter.rs2_as row 0, 0, 0]))
          (List.range (c.last_row + 1))
      else
        if index = 9 then
          List.map
              (fun row ↦
                (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                      c.core.opcode_or_flag row 0 +
                    c.core.opcode_and_flag row 0,
                  [(1 - (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 + c.core.opcode_and_flag row 0)) *
                        c.core.a_0 row 0 +
                      (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 + c.core.opcode_and_flag row 0) *
                        c.core.b_0 row 0,
                    (1 - (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 + c.core.opcode_and_flag row 0)) *
                        c.core.a_0 row 0 +
                      (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 + c.core.opcode_and_flag row 0) *
                        c.core.c_0 row 0,
                    c.core.opcode_xor_flag row 0 * c.core.a_0 row 0 +
                        c.core.opcode_or_flag row 0 * (2 * c.core.a_0 row 0 - c.core.b_0 row 0 - c.core.c_0 row 0) +
                      c.core.opcode_and_flag row 0 * (c.core.b_0 row 0 + c.core.c_0 row 0 - 2 * c.core.a_0 row 0),
                    1]))
              (List.range (c.last_row + 1)) ++
            (List.map
                (fun row ↦
                  (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                        c.core.opcode_or_flag row 0 +
                      c.core.opcode_and_flag row 0,
                    [(1 - (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 + c.core.opcode_and_flag row 0)) *
                          c.core.a_1 row 0 +
                        (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 + c.core.opcode_and_flag row 0) *
                          c.core.b_1 row 0,
                      (1 -
                            (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 +
                              c.core.opcode_and_flag row 0)) *
                          c.core.a_1 row 0 +
                        (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 + c.core.opcode_and_flag row 0) *
                          c.core.c_1 row 0,
                      c.core.opcode_xor_flag row 0 * c.core.a_1 row 0 +
                          c.core.opcode_or_flag row 0 * (2 * c.core.a_1 row 0 - c.core.b_1 row 0 - c.core.c_1 row 0) +
                        c.core.opcode_and_flag row 0 * (c.core.b_1 row 0 + c.core.c_1 row 0 - 2 * c.core.a_1 row 0),
                      1]))
                (List.range (c.last_row + 1)) ++
              (List.map
                  (fun row ↦
                    (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                          c.core.opcode_or_flag row 0 +
                        c.core.opcode_and_flag row 0,
                      [(1 -
                              (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 +
                                c.core.opcode_and_flag row 0)) *
                            c.core.a_2 row 0 +
                          (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 + c.core.opcode_and_flag row 0) *
                            c.core.b_2 row 0,
                        (1 -
                              (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 +
                                c.core.opcode_and_flag row 0)) *
                            c.core.a_2 row 0 +
                          (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 + c.core.opcode_and_flag row 0) *
                            c.core.c_2 row 0,
                        c.core.opcode_xor_flag row 0 * c.core.a_2 row 0 +
                            c.core.opcode_or_flag row 0 * (2 * c.core.a_2 row 0 - c.core.b_2 row 0 - c.core.c_2 row 0) +
                          c.core.opcode_and_flag row 0 * (c.core.b_2 row 0 + c.core.c_2 row 0 - 2 * c.core.a_2 row 0),
                        1]))
                  (List.range (c.last_row + 1)) ++
                (List.map
                    (fun row ↦
                      (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                            c.core.opcode_or_flag row 0 +
                          c.core.opcode_and_flag row 0,
                        [(1 -
                                (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 +
                                  c.core.opcode_and_flag row 0)) *
                              c.core.a_3 row 0 +
                            (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 +
                                c.core.opcode_and_flag row 0) *
                              c.core.b_3 row 0,
                          (1 -
                                (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 +
                                  c.core.opcode_and_flag row 0)) *
                              c.core.a_3 row 0 +
                            (c.core.opcode_xor_flag row 0 + c.core.opcode_or_flag row 0 +
                                c.core.opcode_and_flag row 0) *
                              c.core.c_3 row 0,
                          c.core.opcode_xor_flag row 0 * c.core.a_3 row 0 +
                              c.core.opcode_or_flag row 0 *
                                (2 * c.core.a_3 row 0 - c.core.b_3 row 0 - c.core.c_3 row 0) +
                            c.core.opcode_and_flag row 0 * (c.core.b_3 row 0 + c.core.c_3 row 0 - 2 * c.core.a_3 row 0),
                          1]))
                    (List.range (c.last_row + 1)) ++
                  List.map
                    (fun row ↦
                      (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                              c.core.opcode_or_flag row 0 +
                            c.core.opcode_and_flag row 0 -
                          c.adapter.rs2_as row 0,
                        [c.core.c_0 row 0, c.core.c_1 row 0, 0, 0]))
                    (List.range (c.last_row + 1)))))
        else
          if index = 4 then
            List.map
                (fun row ↦
                  (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                        c.core.opcode_or_flag row 0 +
                      c.core.opcode_and_flag row 0,
                    [c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]))
                (List.range (c.last_row + 1)) ++
              (List.map
                  (fun row ↦
                    (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                          c.core.opcode_or_flag row 0 +
                        c.core.opcode_and_flag row 0,
                      [c.adapter.reads_aux_0.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]))
                  (List.range (c.last_row + 1)) ++
                (List.map
                    (fun row ↦
                      (c.adapter.rs2_as row 0, [c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]))
                    (List.range (c.last_row + 1)) ++
                  (List.map
                      (fun row ↦
                        (c.adapter.rs2_as row 0,
                          [c.adapter.reads_aux_1.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]))
                      (List.range (c.last_row + 1)) ++
                    (List.map
                        (fun row ↦
                          (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                                c.core.opcode_or_flag row 0 +
                              c.core.opcode_and_flag row 0,
                            [c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]))
                        (List.range (c.last_row + 1)) ++
                      List.map
                        (fun row ↦
                          (c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
                                c.core.opcode_or_flag row 0 +
                              c.core.opcode_and_flag row 0,
                            [c.adapter.writes_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]))
                        (List.range (c.last_row + 1))))))
          else [] := by
  unfold VmAirWrapper_alu.extraction.constrain_interactions at h
  simp [openvm_encapsulation] at h
  exact h
