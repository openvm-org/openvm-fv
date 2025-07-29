import OpenvmFv.Basic
import OpenvmFv.Airs.Alu.VmAirWrapper_alu
import OpenvmFv.Extraction.VmAirWrapper_alu

-- lemma f [Field F] [Field ExtF] (c: VmAirWrapper_alu F ExtF) : @Circuit.main F (by assumption) ExtF (by assumption) VmAirWrapper_alu _ c = c.main := rfl

lemma constraint_0' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_0 c row)
  (h': c.isValid)
: sorry := by
  unfold VmAirWrapper_alu.extraction.constraint_0 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_1' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_1 c row)
  (h': c.isValid)
: c.core.opcode_sub_flag row 0 = 0 ∨ c.core.opcode_sub_flag row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_1 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_2' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_2 c row)
  (h': c.isValid)
: c.core.opcode_xor_flag row 0 = 0 ∨ c.core.opcode_xor_flag row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_2 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_3' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_3 c row)
  (h': c.isValid)
: c.core.opcode_or_flag row 0 = 0 ∨ c.core.opcode_or_flag row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_3 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_4' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_4 c row)
  (h': c.isValid)
: c.core.opcode_and_flag row 0 = 0 ∨ c.core.opcode_and_flag row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_4 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_5' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_5 c row)
  (h': c.isValid)
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
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_6' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_6 c row)
  (h': c.isValid)
: c.core.opcode_add_flag row 0 = 0 ∨
  ((2005401601 : F) = 0 ∨ c.core.b_0 row 0 + c.core.c_0 row 0 - c.core.a_0 row 0 = 0) ∨
    2005401601 * (c.core.b_0 row 0 + c.core.c_0 row 0 - c.core.a_0 row 0) - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_6 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_7' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_7 c row)
  (h': c.isValid)
: c.core.opcode_sub_flag row 0 = 0 ∨
    ((2005401601 : F) = 0 ∨ c.core.a_0 row 0 + c.core.c_0 row 0 - c.core.b_0 row 0 = 0) ∨
      2005401601 * (c.core.a_0 row 0 + c.core.c_0 row 0 - c.core.b_0 row 0) - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_7 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_8' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_8 c row)
  (h': c.isValid)
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
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_9' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_9 c row)
  (h': c.isValid)
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
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_10' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_10 c row)
  (h': c.isValid)
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
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_11' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_11 c row)
  (h': c.isValid)
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
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_12' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_12 c row)
  (h': c.isValid)
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
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_13' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_13 c row)
  (h': c.isValid)
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
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_14' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_14 c row)
  (h': c.isValid)
: c.adapter.rs2_as row 0 = 0 ∨ c.adapter.rs2_as row 0 - 1 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_14 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_15' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_15 c row)
  (h': c.isValid)
: 1 - c.adapter.rs2_as row 0 = 0 ∨
    c.adapter.rs2 row 0 - (c.core.c_0 row 0 + c.core.c_1 row 0 * 256 + c.core.c_2 row 0 * 65536) = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_15 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_16' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_16 c row)
  (h': c.isValid)
: 1 - c.adapter.rs2_as row 0 = 0 ∨ c.core.c_2 row 0 - c.core.c_3 row 0 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_16 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_17' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_17 c row)
  (h': c.isValid)
: 1 - c.adapter.rs2_as row 0 = 0 ∨ c.core.c_2 row 0 = 0 ∨ 255 - c.core.c_2 row 0 = 0 := by
  unfold VmAirWrapper_alu.extraction.constraint_17 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constraint_18' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_18 c row)
  (h': c.isValid)
: sorry := by
  unfold VmAirWrapper_alu.extraction.constraint_18 at h
  simp? [openvm_encapsulation, *] at h
  rewrite [MemoryReadAuxCols.col_0_of_isValid] at h
  exact h

lemma constraint_19' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_19 c row)
  (h': c.isValid)
: c.adapter.rs2_as row 0 = 0 ∨
    c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
            c.core.opcode_or_flag row 0 +
          c.core.opcode_and_flag row 0 -
        1 =
      0 := by
  unfold VmAirWrapper_alu.extraction.constraint_19 at h
  simp? [openvm_encapsulation, *] at h
  exact h

@[openvm_encapsulation]
lemma temp [Field F] [Field ExtF]
  {c: { c : VmAirWrapper_alu F ExtF // c.isValid }} {row rotation : ℕ} :
  c.1.main (id := 0) (column := 1) (row := row) (rotation := rotation) =
  c.1.adapter.main (id := 0) (column := 1) (row := row) (rotation := rotation) := by
    exact (c.2.2 row rotation).2.1

lemma temp' [Field F] [Field ExtF]
  {c: { c : VmAirWrapper_alu F ExtF // c.isValid }} :
  c.1.adapter.isValid := by
    simp [openvm_encapsulation, c.2]

abbrev c' (F ExtF) [Field F] [Field ExtF] := { c: VmAirWrapper_alu F ExtF // c.isValid }
abbrev c'' (F ExtF) [Field F] [Field ExtF] := { c: Rv32BaseAluAdapterAir F ExtF // c.isValid }

-- lemma constraint_20' [Field F] [Field ExtF]
--   (c: Valid_VmAirWrapper_alu F ExtF) (row: ℕ)
--   (h: VmAirWrapper_alu.extraction.constraint_20 c row)
-- : sorry := by
--   unfold VmAirWrapper_alu.extraction.constraint_20 at h
--   -- aesop (add simp openvm_encapsulation)
--   simp only [
--     temp
--   ] at h
--   -- simp? [
--   --   VmAirWrapper_alu.subcircuit_adapter_isValid_of_isValid, *,
--   --   Rv32BaseAluAdapterAir.subcircuit_from_state_isValid_of_isValid,
--   --   ExecutionState.col_1_of_isValid
--   -- ] at h
--   -- have := (Rv32BaseAluAdapterAir.subcircuit_from_state_isValid_of_isValid c.adapter (VmAirWrapper_alu.subcircuit_adapter_isValid_of_isValid c h'))
--   have := (VmAirWrapper_alu.subcircuit_adapter_isValid_of_isValid c h')
--   simp [ExecutionState.col_1_of_isValid, *] at h
--   rewrite [ExecutionState.col_1_of_isValid _ _ _ (Rv32BaseAluAdapterAir.subcircuit_from_state_isValid_of_isValid c.adapter (VmAirWrapper_alu.subcircuit_adapter_isValid_of_isValid c h'))] at h
--   -- have :=
--   -- have :=
--   -- rewrite [@ExecutionState.col_1_of_isValid F ExtF inferInstance inferInstance c.adapter.from_state row 0 this] at h
--   rewrite [
--     ExecutionState.col_1_of_isValid c.adapter.from_state row 0
--     (Rv32BaseAluAdapterAir.subcircuit_from_state_isValid_of_isValid c.adapter
--     (VmAirWrapper_alu.subcircuit_adapter_isValid_of_isValid c h'))
--   ] at h
--   exact h

lemma constraint_21' [Field F] [Field ExtF]
  (c: VmAirWrapper_alu F ExtF) (row: ℕ)
  (h: VmAirWrapper_alu.extraction.constraint_21 c row)
  (h': c.isValid)
: c.core.opcode_add_flag row 0 + c.core.opcode_sub_flag row 0 + c.core.opcode_xor_flag row 0 +
          c.core.opcode_or_flag row 0 +
        c.core.opcode_and_flag row 0 =
      0 ∨
    c.adapter.from_state.main 0 1 row 0 + 2 - c.adapter.writes_aux.main 0 2 row 0 - 1 -
        (c.adapter.writes_aux.main 0 3 row 0 + c.adapter.writes_aux.main 0 4 row 0 * 131072) =
      0 := by
  unfold VmAirWrapper_alu.extraction.constraint_21 at h
  simp? [openvm_encapsulation, *] at h
  exact h

lemma constrain_interactions' [Field F] [Field ExtF]
  (c: Valid_VmAirWrapper_alu F ExtF)
  (h: VmAirWrapper_alu.extraction.constrain_interactions c.1)
: sorry := by
  unfold VmAirWrapper_alu.extraction.constrain_interactions at h
  simp? [openvm_encapsulation] at h
  rewrite [VmAirWrapper_alu.push_cast, Rv32BaseAluAdapterAir.push_cast] at h
  exact h
