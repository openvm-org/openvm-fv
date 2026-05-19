import VmExtensions.Extraction.Sha2MainAir_sha512

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace Sha2MainAir_sha512.constraints

section constraint_simplification

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-! ## Column Abbreviations

Named accessors for the SHA-512 main-chip trace columns.
-/

/-- Column `0`: request id shared with the block hasher on the SHA-2 bus. -/
abbrev request_id (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)

/-- Column `0` on the next row. -/
abbrev next_request_id (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)

/-- Columns `1..128`: input block bytes in ascending memory order. -/
abbrev message_byte (c : C F ExtF) (idx : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 1 + idx) (row := row) (rotation := 0)

/-- Columns `129..192`: previous SHA-512 state bytes, word-wise little-endian. -/
abbrev prev_state_byte (c : C F ExtF) (idx : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 129 + idx) (row := row) (rotation := 0)

/-- Columns `193..256`: post-compression state bytes, word-wise little-endian. -/
abbrev new_state_byte (c : C F ExtF) (idx : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 193 + idx) (row := row) (rotation := 0)

/-- Column `257`: instruction-enable flag for the main chip. -/
abbrev is_enabled (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 257) (row := row) (rotation := 0)

/-- Column `257` on the next row. -/
abbrev next_is_enabled (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 257) (row := row) (rotation := 1)

/-- Column `258`: execution-state program counter. -/
abbrev from_pc (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 258) (row := row) (rotation := 0)

/-- Column `259`: execution-state timestamp. -/
abbrev from_timestamp (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 259) (row := row) (rotation := 0)

/-- Column `260`: destination register pointer. -/
abbrev dst_reg_ptr (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 260) (row := row) (rotation := 0)

/-- Column `261`: previous-state register pointer. -/
abbrev state_reg_ptr (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 261) (row := row) (rotation := 0)

/-- Column `262`: input-block register pointer. -/
abbrev input_reg_ptr (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 262) (row := row) (rotation := 0)

/-- Columns `263..266`: little-endian limbs of the destination memory pointer. -/
abbrev dst_ptr_limb (c : C F ExtF) (limb : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 263 + limb) (row := row) (rotation := 0)

/-- Columns `267..270`: little-endian limbs of the previous-state memory pointer. -/
abbrev state_ptr_limb (c : C F ExtF) (limb : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 267 + limb) (row := row) (rotation := 0)

/-- Columns `271..274`: little-endian limbs of the input-block memory pointer. -/
abbrev input_ptr_limb (c : C F ExtF) (limb : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 271 + limb) (row := row) (rotation := 0)

/-- Register-read auxiliary previous timestamps for `dst`, `state`, and `input`. -/
abbrev register_read_prev_timestamp (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 275 + 3 * slot) (row := row) (rotation := 0)

/-- Lower 17-bit timestamp decomposition limb for a register read. -/
abbrev register_read_timestamp_lt_aux_0 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 276 + 3 * slot) (row := row) (rotation := 0)

/-- Upper 12-bit timestamp decomposition limb for a register read. -/
abbrev register_read_timestamp_lt_aux_1 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 277 + 3 * slot) (row := row) (rotation := 0)

/-- Input-read auxiliary previous timestamps; one per 4-byte chunk. -/
abbrev input_read_prev_timestamp (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 284 + 3 * slot) (row := row) (rotation := 0)

/-- Lower 17-bit timestamp decomposition limb for an input read. -/
abbrev input_read_timestamp_lt_aux_0 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 285 + 3 * slot) (row := row) (rotation := 0)

/-- Upper 12-bit timestamp decomposition limb for an input read. -/
abbrev input_read_timestamp_lt_aux_1 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 286 + 3 * slot) (row := row) (rotation := 0)

/-- Previous-state-read auxiliary previous timestamps; one per 4-byte chunk. -/
abbrev state_read_prev_timestamp (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 380 + 3 * slot) (row := row) (rotation := 0)

/-- Lower 17-bit timestamp decomposition limb for a previous-state read. -/
abbrev state_read_timestamp_lt_aux_0 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 381 + 3 * slot) (row := row) (rotation := 0)

/-- Upper 12-bit timestamp decomposition limb for a previous-state read. -/
abbrev state_read_timestamp_lt_aux_1 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 382 + 3 * slot) (row := row) (rotation := 0)

/-- Write auxiliary previous timestamps; one per 4-byte destination chunk. -/
abbrev write_prev_timestamp (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 428 + 7 * slot) (row := row) (rotation := 0)

/-- Lower 17-bit timestamp decomposition limb for a destination write. -/
abbrev write_timestamp_lt_aux_0 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 429 + 7 * slot) (row := row) (rotation := 0)

/-- Upper 12-bit timestamp decomposition limb for a destination write. -/
abbrev write_timestamp_lt_aux_1 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 430 + 7 * slot) (row := row) (rotation := 0)

/-- Previous byte value at the destination write slot. -/
abbrev write_prev_data (c : C F ExtF) (slot byte : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 431 + 7 * slot + byte) (row := row) (rotation := 0)

/-- Compose four little-endian bytes into one 32-bit pointer word. -/
abbrev compose_u32_le (b0 b1 b2 b3 : F) : F :=
  (((b0 + b1 * 256) + b2 * 65536) + b3 * 16777216)

/-- The destination memory pointer reconstructed from its four 8-bit limbs. -/
abbrev dst_ptr_value (c : C F ExtF) (row : ℕ) : F :=
  compose_u32_le
    (dst_ptr_limb c 0 row)
    (dst_ptr_limb c 1 row)
    (dst_ptr_limb c 2 row)
    (dst_ptr_limb c 3 row)

/-- The previous-state memory pointer reconstructed from its four 8-bit limbs. -/
abbrev state_ptr_value (c : C F ExtF) (row : ℕ) : F :=
  compose_u32_le
    (state_ptr_limb c 0 row)
    (state_ptr_limb c 1 row)
    (state_ptr_limb c 2 row)
    (state_ptr_limb c 3 row)

/-- The input-block memory pointer reconstructed from its four 8-bit limbs. -/
abbrev input_ptr_value (c : C F ExtF) (row : ℕ) : F :=
  compose_u32_le
    (input_ptr_limb c 0 row)
    (input_ptr_limb c 1 row)
    (input_ptr_limb c 2 row)
    (input_ptr_limb c 3 row)

/-- Consecutive little-endian previous-state bytes packed into one u16 limb. -/
abbrev prev_state_u16 (c : C F ExtF) (idx : ℕ) (row : ℕ) : F :=
  prev_state_byte c (2 * idx) row + prev_state_byte c (2 * idx + 1) row * 256

/-- Common 29-bit timestamp-difference encoding used by the memory bridge. -/
abbrev timestamp_delta_expr (current prev lo hi : F) : F :=
  (((current - prev) - 1) - (lo + hi * 131072))

/-! ## Simplified Row Constraints -/

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_0 (c : C F ExtF) (row : ℕ) : Prop :=
  ((Circuit.isFirstRow c row) * ((is_enabled c row) * (request_id c row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_0_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_0 c row ↔ constraint_0 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_1 (c : C F ExtF) (row : ℕ) : Prop :=
  ((Circuit.isTransitionRow c row) *
    ((next_is_enabled c row) * ((next_request_id c row) - ((request_id c row) + 1)))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_1_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_1 c row ↔ constraint_1 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_2 (c : C F ExtF) (row : ℕ) : Prop :=
  (is_enabled c row) * ((is_enabled c row) - 1) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_2_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_2 c row ↔ constraint_2 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_3 (c : C F ExtF) (row : ℕ) : Prop :=
  ((Circuit.isTransitionRow c row) * (((is_enabled c row) - 1) * (next_is_enabled c row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_3_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_3 c row ↔ constraint_3 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_4 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      (from_timestamp c row)
      (register_read_prev_timestamp c 0 row)
      (register_read_timestamp_lt_aux_0 c 0 row)
      (register_read_timestamp_lt_aux_1 c 0 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_4_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_4 c row ↔ constraint_4 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_5 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 1)
      (register_read_prev_timestamp c 1 row)
      (register_read_timestamp_lt_aux_0 c 1 row)
      (register_read_timestamp_lt_aux_1 c 1 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_5_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_5 c row ↔ constraint_5 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_6 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 2)
      (register_read_prev_timestamp c 2 row)
      (register_read_timestamp_lt_aux_0 c 2 row)
      (register_read_timestamp_lt_aux_1 c 2 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_6_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_6 c row ↔ constraint_6 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_7 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 3)
      (input_read_prev_timestamp c 0 row)
      (input_read_timestamp_lt_aux_0 c 0 row)
      (input_read_timestamp_lt_aux_1 c 0 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_7_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_7 c row ↔ constraint_7 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_8 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 4)
      (input_read_prev_timestamp c 1 row)
      (input_read_timestamp_lt_aux_0 c 1 row)
      (input_read_timestamp_lt_aux_1 c 1 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_8_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_8 c row ↔ constraint_8 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_9 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 5)
      (input_read_prev_timestamp c 2 row)
      (input_read_timestamp_lt_aux_0 c 2 row)
      (input_read_timestamp_lt_aux_1 c 2 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_9_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_9 c row ↔ constraint_9 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_10 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 6)
      (input_read_prev_timestamp c 3 row)
      (input_read_timestamp_lt_aux_0 c 3 row)
      (input_read_timestamp_lt_aux_1 c 3 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_10_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_10 c row ↔ constraint_10 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_11 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 7)
      (input_read_prev_timestamp c 4 row)
      (input_read_timestamp_lt_aux_0 c 4 row)
      (input_read_timestamp_lt_aux_1 c 4 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_11_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_11 c row ↔ constraint_11 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_12 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 8)
      (input_read_prev_timestamp c 5 row)
      (input_read_timestamp_lt_aux_0 c 5 row)
      (input_read_timestamp_lt_aux_1 c 5 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_12_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_12 c row ↔ constraint_12 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_13 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 9)
      (input_read_prev_timestamp c 6 row)
      (input_read_timestamp_lt_aux_0 c 6 row)
      (input_read_timestamp_lt_aux_1 c 6 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_13_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_13 c row ↔ constraint_13 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_14 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 10)
      (input_read_prev_timestamp c 7 row)
      (input_read_timestamp_lt_aux_0 c 7 row)
      (input_read_timestamp_lt_aux_1 c 7 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_14_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_14 c row ↔ constraint_14 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_15 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 11)
      (input_read_prev_timestamp c 8 row)
      (input_read_timestamp_lt_aux_0 c 8 row)
      (input_read_timestamp_lt_aux_1 c 8 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_15_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_15 c row ↔ constraint_15 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_16 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 12)
      (input_read_prev_timestamp c 9 row)
      (input_read_timestamp_lt_aux_0 c 9 row)
      (input_read_timestamp_lt_aux_1 c 9 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_16_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_16 c row ↔ constraint_16 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_17 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 13)
      (input_read_prev_timestamp c 10 row)
      (input_read_timestamp_lt_aux_0 c 10 row)
      (input_read_timestamp_lt_aux_1 c 10 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_17_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_17 c row ↔ constraint_17 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_18 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 14)
      (input_read_prev_timestamp c 11 row)
      (input_read_timestamp_lt_aux_0 c 11 row)
      (input_read_timestamp_lt_aux_1 c 11 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_18_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_18 c row ↔ constraint_18 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_19 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 15)
      (input_read_prev_timestamp c 12 row)
      (input_read_timestamp_lt_aux_0 c 12 row)
      (input_read_timestamp_lt_aux_1 c 12 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_19_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_19 c row ↔ constraint_19 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_20 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 16)
      (input_read_prev_timestamp c 13 row)
      (input_read_timestamp_lt_aux_0 c 13 row)
      (input_read_timestamp_lt_aux_1 c 13 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_20_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_20 c row ↔ constraint_20 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_21 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 17)
      (input_read_prev_timestamp c 14 row)
      (input_read_timestamp_lt_aux_0 c 14 row)
      (input_read_timestamp_lt_aux_1 c 14 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_21_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_21 c row ↔ constraint_21 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_22 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 18)
      (input_read_prev_timestamp c 15 row)
      (input_read_timestamp_lt_aux_0 c 15 row)
      (input_read_timestamp_lt_aux_1 c 15 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_22_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_22 c row ↔ constraint_22 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_23 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 19)
      (input_read_prev_timestamp c 16 row)
      (input_read_timestamp_lt_aux_0 c 16 row)
      (input_read_timestamp_lt_aux_1 c 16 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_23_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_23 c row ↔ constraint_23 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_24 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 20)
      (input_read_prev_timestamp c 17 row)
      (input_read_timestamp_lt_aux_0 c 17 row)
      (input_read_timestamp_lt_aux_1 c 17 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_24_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_24 c row ↔ constraint_24 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_25 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 21)
      (input_read_prev_timestamp c 18 row)
      (input_read_timestamp_lt_aux_0 c 18 row)
      (input_read_timestamp_lt_aux_1 c 18 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_25_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_25 c row ↔ constraint_25 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_26 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 22)
      (input_read_prev_timestamp c 19 row)
      (input_read_timestamp_lt_aux_0 c 19 row)
      (input_read_timestamp_lt_aux_1 c 19 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_26_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_26 c row ↔ constraint_26 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_27 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 23)
      (input_read_prev_timestamp c 20 row)
      (input_read_timestamp_lt_aux_0 c 20 row)
      (input_read_timestamp_lt_aux_1 c 20 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_27_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_27 c row ↔ constraint_27 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_28 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 24)
      (input_read_prev_timestamp c 21 row)
      (input_read_timestamp_lt_aux_0 c 21 row)
      (input_read_timestamp_lt_aux_1 c 21 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_28_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_28 c row ↔ constraint_28 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_29 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 25)
      (input_read_prev_timestamp c 22 row)
      (input_read_timestamp_lt_aux_0 c 22 row)
      (input_read_timestamp_lt_aux_1 c 22 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_29_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_29 c row ↔ constraint_29 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_30 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 26)
      (input_read_prev_timestamp c 23 row)
      (input_read_timestamp_lt_aux_0 c 23 row)
      (input_read_timestamp_lt_aux_1 c 23 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_30_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_30 c row ↔ constraint_30 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_31 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 27)
      (input_read_prev_timestamp c 24 row)
      (input_read_timestamp_lt_aux_0 c 24 row)
      (input_read_timestamp_lt_aux_1 c 24 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_31_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_31 c row ↔ constraint_31 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_32 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 28)
      (input_read_prev_timestamp c 25 row)
      (input_read_timestamp_lt_aux_0 c 25 row)
      (input_read_timestamp_lt_aux_1 c 25 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_32_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_32 c row ↔ constraint_32 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_33 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 29)
      (input_read_prev_timestamp c 26 row)
      (input_read_timestamp_lt_aux_0 c 26 row)
      (input_read_timestamp_lt_aux_1 c 26 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_33_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_33 c row ↔ constraint_33 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_34 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 30)
      (input_read_prev_timestamp c 27 row)
      (input_read_timestamp_lt_aux_0 c 27 row)
      (input_read_timestamp_lt_aux_1 c 27 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_34_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_34 c row ↔ constraint_34 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_35 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 31)
      (input_read_prev_timestamp c 28 row)
      (input_read_timestamp_lt_aux_0 c 28 row)
      (input_read_timestamp_lt_aux_1 c 28 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_35_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_35 c row ↔ constraint_35 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_36 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 32)
      (input_read_prev_timestamp c 29 row)
      (input_read_timestamp_lt_aux_0 c 29 row)
      (input_read_timestamp_lt_aux_1 c 29 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_36_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_36 c row ↔ constraint_36 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_37 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 33)
      (input_read_prev_timestamp c 30 row)
      (input_read_timestamp_lt_aux_0 c 30 row)
      (input_read_timestamp_lt_aux_1 c 30 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_37_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_37 c row ↔ constraint_37 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_38 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 34)
      (input_read_prev_timestamp c 31 row)
      (input_read_timestamp_lt_aux_0 c 31 row)
      (input_read_timestamp_lt_aux_1 c 31 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_38_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_38 c row ↔ constraint_38 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_39 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 35)
      (state_read_prev_timestamp c 0 row)
      (state_read_timestamp_lt_aux_0 c 0 row)
      (state_read_timestamp_lt_aux_1 c 0 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_39_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_39 c row ↔ constraint_39 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_40 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 36)
      (state_read_prev_timestamp c 1 row)
      (state_read_timestamp_lt_aux_0 c 1 row)
      (state_read_timestamp_lt_aux_1 c 1 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_40_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_40 c row ↔ constraint_40 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_41 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 37)
      (state_read_prev_timestamp c 2 row)
      (state_read_timestamp_lt_aux_0 c 2 row)
      (state_read_timestamp_lt_aux_1 c 2 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_41_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_41 c row ↔ constraint_41 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_42 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 38)
      (state_read_prev_timestamp c 3 row)
      (state_read_timestamp_lt_aux_0 c 3 row)
      (state_read_timestamp_lt_aux_1 c 3 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_42_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_42 c row ↔ constraint_42 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_43 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 39)
      (state_read_prev_timestamp c 4 row)
      (state_read_timestamp_lt_aux_0 c 4 row)
      (state_read_timestamp_lt_aux_1 c 4 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_43_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_43 c row ↔ constraint_43 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_44 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 40)
      (state_read_prev_timestamp c 5 row)
      (state_read_timestamp_lt_aux_0 c 5 row)
      (state_read_timestamp_lt_aux_1 c 5 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_44_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_44 c row ↔ constraint_44 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_45 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 41)
      (state_read_prev_timestamp c 6 row)
      (state_read_timestamp_lt_aux_0 c 6 row)
      (state_read_timestamp_lt_aux_1 c 6 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_45_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_45 c row ↔ constraint_45 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_46 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 42)
      (state_read_prev_timestamp c 7 row)
      (state_read_timestamp_lt_aux_0 c 7 row)
      (state_read_timestamp_lt_aux_1 c 7 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_46_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_46 c row ↔ constraint_46 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_47 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 43)
      (state_read_prev_timestamp c 8 row)
      (state_read_timestamp_lt_aux_0 c 8 row)
      (state_read_timestamp_lt_aux_1 c 8 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_47_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_47 c row ↔ constraint_47 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_48 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 44)
      (state_read_prev_timestamp c 9 row)
      (state_read_timestamp_lt_aux_0 c 9 row)
      (state_read_timestamp_lt_aux_1 c 9 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_48_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_48 c row ↔ constraint_48 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_49 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 45)
      (state_read_prev_timestamp c 10 row)
      (state_read_timestamp_lt_aux_0 c 10 row)
      (state_read_timestamp_lt_aux_1 c 10 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_49_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_49 c row ↔ constraint_49 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_50 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 46)
      (state_read_prev_timestamp c 11 row)
      (state_read_timestamp_lt_aux_0 c 11 row)
      (state_read_timestamp_lt_aux_1 c 11 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_50_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_50 c row ↔ constraint_50 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_51 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 47)
      (state_read_prev_timestamp c 12 row)
      (state_read_timestamp_lt_aux_0 c 12 row)
      (state_read_timestamp_lt_aux_1 c 12 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_51_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_51 c row ↔ constraint_51 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_52 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 48)
      (state_read_prev_timestamp c 13 row)
      (state_read_timestamp_lt_aux_0 c 13 row)
      (state_read_timestamp_lt_aux_1 c 13 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_52_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_52 c row ↔ constraint_52 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_53 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 49)
      (state_read_prev_timestamp c 14 row)
      (state_read_timestamp_lt_aux_0 c 14 row)
      (state_read_timestamp_lt_aux_1 c 14 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_53_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_53 c row ↔ constraint_53 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_54 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 50)
      (state_read_prev_timestamp c 15 row)
      (state_read_timestamp_lt_aux_0 c 15 row)
      (state_read_timestamp_lt_aux_1 c 15 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_54_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_54 c row ↔ constraint_54 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_55 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 51)
      (write_prev_timestamp c 0 row)
      (write_timestamp_lt_aux_0 c 0 row)
      (write_timestamp_lt_aux_1 c 0 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_55_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_55 c row ↔ constraint_55 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_56 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 52)
      (write_prev_timestamp c 1 row)
      (write_timestamp_lt_aux_0 c 1 row)
      (write_timestamp_lt_aux_1 c 1 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_56_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_56 c row ↔ constraint_56 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_57 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 53)
      (write_prev_timestamp c 2 row)
      (write_timestamp_lt_aux_0 c 2 row)
      (write_timestamp_lt_aux_1 c 2 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_57_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_57 c row ↔ constraint_57 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_58 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 54)
      (write_prev_timestamp c 3 row)
      (write_timestamp_lt_aux_0 c 3 row)
      (write_timestamp_lt_aux_1 c 3 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_58_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_58 c row ↔ constraint_58 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_59 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 55)
      (write_prev_timestamp c 4 row)
      (write_timestamp_lt_aux_0 c 4 row)
      (write_timestamp_lt_aux_1 c 4 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_59_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_59 c row ↔ constraint_59 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_60 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 56)
      (write_prev_timestamp c 5 row)
      (write_timestamp_lt_aux_0 c 5 row)
      (write_timestamp_lt_aux_1 c 5 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_60_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_60 c row ↔ constraint_60 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_61 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 57)
      (write_prev_timestamp c 6 row)
      (write_timestamp_lt_aux_0 c 6 row)
      (write_timestamp_lt_aux_1 c 6 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_61_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_61 c row ↔ constraint_61 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_62 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 58)
      (write_prev_timestamp c 7 row)
      (write_timestamp_lt_aux_0 c 7 row)
      (write_timestamp_lt_aux_1 c 7 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_62_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_62 c row ↔ constraint_62 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_63 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 59)
      (write_prev_timestamp c 8 row)
      (write_timestamp_lt_aux_0 c 8 row)
      (write_timestamp_lt_aux_1 c 8 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_63_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_63 c row ↔ constraint_63 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_64 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 60)
      (write_prev_timestamp c 9 row)
      (write_timestamp_lt_aux_0 c 9 row)
      (write_timestamp_lt_aux_1 c 9 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_64_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_64 c row ↔ constraint_64 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_65 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 61)
      (write_prev_timestamp c 10 row)
      (write_timestamp_lt_aux_0 c 10 row)
      (write_timestamp_lt_aux_1 c 10 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_65_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_65 c row ↔ constraint_65 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_66 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 62)
      (write_prev_timestamp c 11 row)
      (write_timestamp_lt_aux_0 c 11 row)
      (write_timestamp_lt_aux_1 c 11 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_66_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_66 c row ↔ constraint_66 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_67 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 63)
      (write_prev_timestamp c 12 row)
      (write_timestamp_lt_aux_0 c 12 row)
      (write_timestamp_lt_aux_1 c 12 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_67_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_67 c row ↔ constraint_67 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_68 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 64)
      (write_prev_timestamp c 13 row)
      (write_timestamp_lt_aux_0 c 13 row)
      (write_timestamp_lt_aux_1 c 13 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_68_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_68 c row ↔ constraint_68 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_69 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 65)
      (write_prev_timestamp c 14 row)
      (write_timestamp_lt_aux_0 c 14 row)
      (write_timestamp_lt_aux_1 c 14 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_69_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_69 c row ↔ constraint_69 c row := by
  rfl

@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def constraint_70 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 66)
      (write_prev_timestamp c 15 row)
      (write_timestamp_lt_aux_0 c 15 row)
      (write_timestamp_lt_aux_1 c 15 row))) = 0

@[Sha2MainAir_Sha512Config_air_simplification]
lemma constraint_70_of_extraction (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha512Config.extraction.constraint_70 c row ↔ constraint_70 c row := by
  rfl

/-! ## Interaction Views

These views keep the same low-level payload lists as the extraction while
grouping the bus traffic by role.
-/

/-- BabyBear `-1`, kept in extracted numeric form so the lists match the AIR transcript. -/
abbrev negativeMultiplicityCoeff : F := (2013265920 : F)

/-- Address-space tag for register-file reads. -/
abbrev registerAddressSpace : F := (1 : F)

/-- Address-space tag for guest memory reads and writes. -/
abbrev memoryAddressSpace : F := (2 : F)

/-- The transpiled SHA-512 OpenVM opcode at offset `0x321`. -/
abbrev sha512Opcode : F := (801 : F)

/-- The main-chip timestamp delta: 3 register reads, 32 input reads, 16 state reads, 16 writes. -/
abbrev timestampDelta : F := (67 : F)

/-- Negative memory-bus entry for the previous memory contents. -/
abbrev memoryPrevEntry (mul addrSpace ptr x0 x1 x2 x3 prevTs : F) : F × List F :=
  (negativeMultiplicityCoeff * mul, [addrSpace, ptr, x0, x1, x2, x3, prevTs])

/-- Positive memory-bus entry for the current read or write. -/
abbrev memoryCurrEntry (mul addrSpace ptr x0 x1 x2 x3 ts : F) : F × List F :=
  (mul, [addrSpace, ptr, x0, x1, x2, x3, ts])

/-- Execution-bus entries emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def executionBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (-is_enabled c row, [from_pc c row, from_timestamp c row]),
    (is_enabled c row, [from_pc c row + 4, from_timestamp c row + timestampDelta])
  ]

/-- Program-bus entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def programBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (is_enabled c row,
      [ from_pc c row,
        sha512Opcode,
        dst_reg_ptr c row,
        state_reg_ptr c row,
        input_reg_ptr c row,
        1,
        2,
        0,
        0 ])
  ]

/-- Register-file memory-bus entries emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def registerMemoryBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    memoryPrevEntry
      (is_enabled c row) registerAddressSpace (dst_reg_ptr c row)
      (dst_ptr_limb c 0 row) (dst_ptr_limb c 1 row) (dst_ptr_limb c 2 row) (dst_ptr_limb c 3 row)
      (register_read_prev_timestamp c 0 row),
    memoryCurrEntry
      (is_enabled c row) registerAddressSpace (dst_reg_ptr c row)
      (dst_ptr_limb c 0 row) (dst_ptr_limb c 1 row) (dst_ptr_limb c 2 row) (dst_ptr_limb c 3 row)
      (from_timestamp c row),
    memoryPrevEntry
      (is_enabled c row) registerAddressSpace (state_reg_ptr c row)
      (state_ptr_limb c 0 row) (state_ptr_limb c 1 row) (state_ptr_limb c 2 row) (state_ptr_limb c 3 row)
      (register_read_prev_timestamp c 1 row),
    memoryCurrEntry
      (is_enabled c row) registerAddressSpace (state_reg_ptr c row)
      (state_ptr_limb c 0 row) (state_ptr_limb c 1 row) (state_ptr_limb c 2 row) (state_ptr_limb c 3 row)
      ((from_timestamp c row) + 1),
    memoryPrevEntry
      (is_enabled c row) registerAddressSpace (input_reg_ptr c row)
      (input_ptr_limb c 0 row) (input_ptr_limb c 1 row) (input_ptr_limb c 2 row) (input_ptr_limb c 3 row)
      (register_read_prev_timestamp c 2 row),
    memoryCurrEntry
      (is_enabled c row) registerAddressSpace (input_reg_ptr c row)
      (input_ptr_limb c 0 row) (input_ptr_limb c 1 row) (input_ptr_limb c 2 row) (input_ptr_limb c 3 row)
      ((from_timestamp c row) + 2)
  ]

/-- Guest-memory input-block reads emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def inputMemoryBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  (List.range 32).flatMap fun i : ℕ =>
    [
      memoryPrevEntry
        (is_enabled c row) memoryAddressSpace (input_ptr_value c row + (((4 * i : ℕ) : F)))
        (message_byte c (4 * i) row)
        (message_byte c (4 * i + 1) row)
        (message_byte c (4 * i + 2) row)
        (message_byte c (4 * i + 3) row)
        (input_read_prev_timestamp c i row),
      memoryCurrEntry
        (is_enabled c row) memoryAddressSpace (input_ptr_value c row + (((4 * i : ℕ) : F)))
        (message_byte c (4 * i) row)
        (message_byte c (4 * i + 1) row)
        (message_byte c (4 * i + 2) row)
        (message_byte c (4 * i + 3) row)
        (from_timestamp c row + (((3 + i : ℕ) : F)))
    ]

/-- Guest-memory previous-state reads emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def stateMemoryBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  (List.range 16).flatMap fun i : ℕ =>
    [
      memoryPrevEntry
        (is_enabled c row) memoryAddressSpace (state_ptr_value c row + (((4 * i : ℕ) : F)))
        (prev_state_byte c (4 * i) row)
        (prev_state_byte c (4 * i + 1) row)
        (prev_state_byte c (4 * i + 2) row)
        (prev_state_byte c (4 * i + 3) row)
        (state_read_prev_timestamp c i row),
      memoryCurrEntry
        (is_enabled c row) memoryAddressSpace (state_ptr_value c row + (((4 * i : ℕ) : F)))
        (prev_state_byte c (4 * i) row)
        (prev_state_byte c (4 * i + 1) row)
        (prev_state_byte c (4 * i + 2) row)
        (prev_state_byte c (4 * i + 3) row)
        (from_timestamp c row + (((35 + i : ℕ) : F)))
    ]

/-- Guest-memory destination writes emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def writeMemoryBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  (List.range 16).flatMap fun i : ℕ =>
    [
      memoryPrevEntry
        (is_enabled c row) memoryAddressSpace (dst_ptr_value c row + (((4 * i : ℕ) : F)))
        (write_prev_data c i 0 row)
        (write_prev_data c i 1 row)
        (write_prev_data c i 2 row)
        (write_prev_data c i 3 row)
        (write_prev_timestamp c i row),
      memoryCurrEntry
        (is_enabled c row) memoryAddressSpace (dst_ptr_value c row + (((4 * i : ℕ) : F)))
        (new_state_byte c (4 * i) row)
        (new_state_byte c (4 * i + 1) row)
        (new_state_byte c (4 * i + 2) row)
        (new_state_byte c (4 * i + 3) row)
        (from_timestamp c row + (((51 + i : ℕ) : F)))
    ]

/-- All memory-bus entries emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def memoryBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  registerMemoryBus_row c row ++
  inputMemoryBus_row c row ++
  stateMemoryBus_row c row ++
  writeMemoryBus_row c row

/-- Bitwise lookup entries enforcing the 24-bit pointer bound. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def bitwiseLookupBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (is_enabled c row, [dst_ptr_limb c 3 row * 8, state_ptr_limb c 3 row * 8, 0, 0]),
    (is_enabled c row, [input_ptr_limb c 3 row * 8, input_ptr_limb c 3 row * 8, 0, 0])
  ]

/-- The SHA-2 `State` wrapper-bus entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def sha2StateBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (is_enabled c row,
      [0, request_id c row] ++
      (List.range 32).map (fun i => prev_state_u16 c i row) ++
      (List.range 64).map (fun i => new_state_byte c i row))
  ]

/-- The SHA-2 `Message1` wrapper-bus entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def sha2Message1Bus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (is_enabled c row,
      [1, request_id c row] ++
      (List.range 64).map (fun i => message_byte c i row))
  ]

/-- The SHA-2 `Message2` wrapper-bus entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def sha2Message2Bus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (is_enabled c row,
      [2, request_id c row] ++
      (List.range 64).map (fun i => message_byte c (64 + i) row))
  ]

/-- All SHA-2 wrapper-bus entries emitted by one main-chip row. -/
@[Sha2MainAir_Sha512Config_constraint_and_interaction_simplification]
def sha2Bus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  sha2StateBus_row c row ++
  sha2Message1Bus_row c row ++
  sha2Message2Bus_row c row

end constraint_simplification

end Sha2MainAir_sha512.constraints

namespace Sha2MainAir_Sha512Config.extraction

section grouped_constraints

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-- The full extracted SHA-512 main-air row contract: all extracted row
constraints bundled into a single proposition. -/
def constrain_row (c : C F ExtF) (row : ℕ) : Prop :=
  Sha2MainAir_Sha512Config.extraction.constraint_0 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_1 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_2 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_3 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_4 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_5 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_6 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_7 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_8 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_9 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_10 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_11 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_12 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_13 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_14 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_15 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_16 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_17 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_18 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_19 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_20 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_21 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_22 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_23 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_24 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_25 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_26 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_27 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_28 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_29 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_30 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_31 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_32 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_33 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_34 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_35 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_36 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_37 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_38 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_39 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_40 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_41 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_42 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_43 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_44 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_45 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_46 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_47 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_48 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_49 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_50 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_51 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_52 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_53 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_54 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_55 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_56 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_57 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_58 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_59 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_60 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_61 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_62 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_63 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_64 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_65 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_66 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_67 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_68 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_69 c row ∧
  Sha2MainAir_Sha512Config.extraction.constraint_70 c row

end grouped_constraints

end Sha2MainAir_Sha512Config.extraction
