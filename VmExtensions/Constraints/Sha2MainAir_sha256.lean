import VmExtensions.Extraction.Sha2MainAir_sha256

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace Sha2MainAir_sha256.constraints

section constraint_simplification

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-! ## Column Abbreviations

Named accessors for the SHA-256 main-chip trace columns.
-/

/-- Column `0`: request id shared with the block hasher on the SHA-2 bus. -/
abbrev request_id (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 0)

/-- Column `0` on the next row. -/
abbrev next_request_id (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 0) (row := row) (rotation := 1)

/-- Columns `1..64`: input block bytes in ascending memory order. -/
abbrev message_byte (c : C F ExtF) (idx : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 1 + idx) (row := row) (rotation := 0)

/-- Columns `65..96`: previous SHA-256 state bytes, word-wise little-endian. -/
abbrev prev_state_byte (c : C F ExtF) (idx : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 65 + idx) (row := row) (rotation := 0)

/-- Columns `97..128`: post-compression state bytes, word-wise little-endian. -/
abbrev new_state_byte (c : C F ExtF) (idx : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 97 + idx) (row := row) (rotation := 0)

/-- Column `129`: instruction-enable flag for the main chip. -/
abbrev is_enabled (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 129) (row := row) (rotation := 0)

/-- Column `129` on the next row. -/
abbrev next_is_enabled (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 129) (row := row) (rotation := 1)

/-- Column `130`: execution-state program counter. -/
abbrev from_pc (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 130) (row := row) (rotation := 0)

/-- Column `131`: execution-state timestamp. -/
abbrev from_timestamp (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 131) (row := row) (rotation := 0)

/-- Column `132`: destination register pointer. -/
abbrev dst_reg_ptr (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 132) (row := row) (rotation := 0)

/-- Column `133`: previous-state register pointer. -/
abbrev state_reg_ptr (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 133) (row := row) (rotation := 0)

/-- Column `134`: input-block register pointer. -/
abbrev input_reg_ptr (c : C F ExtF) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 134) (row := row) (rotation := 0)

/-- Columns `135..138`: little-endian limbs of the destination memory pointer. -/
abbrev dst_ptr_limb (c : C F ExtF) (limb : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 135 + limb) (row := row) (rotation := 0)

/-- Columns `139..142`: little-endian limbs of the previous-state memory pointer. -/
abbrev state_ptr_limb (c : C F ExtF) (limb : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 139 + limb) (row := row) (rotation := 0)

/-- Columns `143..146`: little-endian limbs of the input-block memory pointer. -/
abbrev input_ptr_limb (c : C F ExtF) (limb : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 143 + limb) (row := row) (rotation := 0)

/-- Register-read auxiliary previous timestamps for `dst`, `state`, and `input`. -/
abbrev register_read_prev_timestamp (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 147 + 3 * slot) (row := row) (rotation := 0)

/-- Lower 17-bit timestamp decomposition limb for a register read. -/
abbrev register_read_timestamp_lt_aux_0 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 148 + 3 * slot) (row := row) (rotation := 0)

/-- Upper 12-bit timestamp decomposition limb for a register read. -/
abbrev register_read_timestamp_lt_aux_1 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 149 + 3 * slot) (row := row) (rotation := 0)

/-- Input-read auxiliary previous timestamps; one per 4-byte chunk. -/
abbrev input_read_prev_timestamp (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 156 + 3 * slot) (row := row) (rotation := 0)

/-- Lower 17-bit timestamp decomposition limb for an input read. -/
abbrev input_read_timestamp_lt_aux_0 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 157 + 3 * slot) (row := row) (rotation := 0)

/-- Upper 12-bit timestamp decomposition limb for an input read. -/
abbrev input_read_timestamp_lt_aux_1 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 158 + 3 * slot) (row := row) (rotation := 0)

/-- Previous-state-read auxiliary previous timestamps; one per 4-byte chunk. -/
abbrev state_read_prev_timestamp (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 204 + 3 * slot) (row := row) (rotation := 0)

/-- Lower 17-bit timestamp decomposition limb for a previous-state read. -/
abbrev state_read_timestamp_lt_aux_0 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 205 + 3 * slot) (row := row) (rotation := 0)

/-- Upper 12-bit timestamp decomposition limb for a previous-state read. -/
abbrev state_read_timestamp_lt_aux_1 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 206 + 3 * slot) (row := row) (rotation := 0)

/-- Write auxiliary previous timestamps; one per 4-byte destination word. -/
abbrev write_prev_timestamp (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 228 + 7 * slot) (row := row) (rotation := 0)

/-- Lower 17-bit timestamp decomposition limb for a destination write. -/
abbrev write_timestamp_lt_aux_0 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 229 + 7 * slot) (row := row) (rotation := 0)

/-- Upper 12-bit timestamp decomposition limb for a destination write. -/
abbrev write_timestamp_lt_aux_1 (c : C F ExtF) (slot : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 230 + 7 * slot) (row := row) (rotation := 0)

/-- Previous byte value at the destination write slot. -/
abbrev write_prev_data (c : C F ExtF) (slot byte : ℕ) (row : ℕ) : F :=
  Circuit.main c (id := 0) (column := 231 + 7 * slot + byte) (row := row) (rotation := 0)

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

/-- First enabled row starts the shared SHA-2 request id at `0`. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_0 (c : C F ExtF) (row : ℕ) : Prop :=
  ((Circuit.isFirstRow c row) * ((is_enabled c row) * (request_id c row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_0_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_2 c row ↔ constraint_0 c row := by
  rfl

/-- Enabled rows advance the shared SHA-2 request id by one across transitions. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_1 (c : C F ExtF) (row : ℕ) : Prop :=
  ((Circuit.isTransitionRow c row) *
    ((next_is_enabled c row) * ((next_request_id c row) - ((request_id c row) + 1)))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_1_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_3 c row ↔ constraint_1 c row := by
  rfl

/-- The main-chip enable flag is boolean on every row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_2 (c : C F ExtF) (row : ℕ) : Prop :=
  (is_enabled c row) * ((is_enabled c row) - 1) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_2_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_0 c row ↔ constraint_2 c row := by
  rfl

/-- Once a transition row is disabled, the next row stays disabled. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_3 (c : C F ExtF) (row : ℕ) : Prop :=
  ((Circuit.isTransitionRow c row) * (((is_enabled c row) - 1) * (next_is_enabled c row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_3_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_1 c row ↔ constraint_3 c row := by
  rfl

/-- Register read `dst`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_4 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      (from_timestamp c row)
      (register_read_prev_timestamp c 0 row)
      (register_read_timestamp_lt_aux_0 c 0 row)
      (register_read_timestamp_lt_aux_1 c 0 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_4_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_4 c row ↔ constraint_4 c row := by
  rfl

/-- Register read `state`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_5 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 1)
      (register_read_prev_timestamp c 1 row)
      (register_read_timestamp_lt_aux_0 c 1 row)
      (register_read_timestamp_lt_aux_1 c 1 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_5_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_5 c row ↔ constraint_5 c row := by
  rfl

/-- Register read `input`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_6 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 2)
      (register_read_prev_timestamp c 2 row)
      (register_read_timestamp_lt_aux_0 c 2 row)
      (register_read_timestamp_lt_aux_1 c 2 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_6_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_6 c row ↔ constraint_6 c row := by
  rfl

/-- Input-block read `0`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_7 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 3)
      (input_read_prev_timestamp c 0 row)
      (input_read_timestamp_lt_aux_0 c 0 row)
      (input_read_timestamp_lt_aux_1 c 0 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_7_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_7 c row ↔ constraint_7 c row := by
  rfl

/-- Input-block read `1`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_8 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 4)
      (input_read_prev_timestamp c 1 row)
      (input_read_timestamp_lt_aux_0 c 1 row)
      (input_read_timestamp_lt_aux_1 c 1 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_8_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_8 c row ↔ constraint_8 c row := by
  rfl

/-- Input-block read `2`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_9 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 5)
      (input_read_prev_timestamp c 2 row)
      (input_read_timestamp_lt_aux_0 c 2 row)
      (input_read_timestamp_lt_aux_1 c 2 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_9_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_9 c row ↔ constraint_9 c row := by
  rfl

/-- Input-block read `3`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_10 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 6)
      (input_read_prev_timestamp c 3 row)
      (input_read_timestamp_lt_aux_0 c 3 row)
      (input_read_timestamp_lt_aux_1 c 3 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_10_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_10 c row ↔ constraint_10 c row := by
  rfl

/-- Input-block read `4`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_11 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 7)
      (input_read_prev_timestamp c 4 row)
      (input_read_timestamp_lt_aux_0 c 4 row)
      (input_read_timestamp_lt_aux_1 c 4 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_11_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_11 c row ↔ constraint_11 c row := by
  rfl

/-- Input-block read `5`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_12 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 8)
      (input_read_prev_timestamp c 5 row)
      (input_read_timestamp_lt_aux_0 c 5 row)
      (input_read_timestamp_lt_aux_1 c 5 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_12_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_12 c row ↔ constraint_12 c row := by
  rfl

/-- Input-block read `6`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_13 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 9)
      (input_read_prev_timestamp c 6 row)
      (input_read_timestamp_lt_aux_0 c 6 row)
      (input_read_timestamp_lt_aux_1 c 6 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_13_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_13 c row ↔ constraint_13 c row := by
  rfl

/-- Input-block read `7`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_14 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 10)
      (input_read_prev_timestamp c 7 row)
      (input_read_timestamp_lt_aux_0 c 7 row)
      (input_read_timestamp_lt_aux_1 c 7 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_14_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_14 c row ↔ constraint_14 c row := by
  rfl

/-- Input-block read `8`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_15 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 11)
      (input_read_prev_timestamp c 8 row)
      (input_read_timestamp_lt_aux_0 c 8 row)
      (input_read_timestamp_lt_aux_1 c 8 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_15_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_15 c row ↔ constraint_15 c row := by
  rfl

/-- Input-block read `9`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_16 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 12)
      (input_read_prev_timestamp c 9 row)
      (input_read_timestamp_lt_aux_0 c 9 row)
      (input_read_timestamp_lt_aux_1 c 9 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_16_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_16 c row ↔ constraint_16 c row := by
  rfl

/-- Input-block read `10`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_17 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 13)
      (input_read_prev_timestamp c 10 row)
      (input_read_timestamp_lt_aux_0 c 10 row)
      (input_read_timestamp_lt_aux_1 c 10 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_17_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_17 c row ↔ constraint_17 c row := by
  rfl

/-- Input-block read `11`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_18 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 14)
      (input_read_prev_timestamp c 11 row)
      (input_read_timestamp_lt_aux_0 c 11 row)
      (input_read_timestamp_lt_aux_1 c 11 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_18_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_18 c row ↔ constraint_18 c row := by
  rfl

/-- Input-block read `12`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_19 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 15)
      (input_read_prev_timestamp c 12 row)
      (input_read_timestamp_lt_aux_0 c 12 row)
      (input_read_timestamp_lt_aux_1 c 12 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_19_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_19 c row ↔ constraint_19 c row := by
  rfl

/-- Input-block read `13`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_20 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 16)
      (input_read_prev_timestamp c 13 row)
      (input_read_timestamp_lt_aux_0 c 13 row)
      (input_read_timestamp_lt_aux_1 c 13 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_20_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_20 c row ↔ constraint_20 c row := by
  rfl

/-- Input-block read `14`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_21 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 17)
      (input_read_prev_timestamp c 14 row)
      (input_read_timestamp_lt_aux_0 c 14 row)
      (input_read_timestamp_lt_aux_1 c 14 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_21_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_21 c row ↔ constraint_21 c row := by
  rfl

/-- Input-block read `15`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_22 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 18)
      (input_read_prev_timestamp c 15 row)
      (input_read_timestamp_lt_aux_0 c 15 row)
      (input_read_timestamp_lt_aux_1 c 15 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_22_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_22 c row ↔ constraint_22 c row := by
  rfl

/-- Previous-state read `0`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_23 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 19)
      (state_read_prev_timestamp c 0 row)
      (state_read_timestamp_lt_aux_0 c 0 row)
      (state_read_timestamp_lt_aux_1 c 0 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_23_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_23 c row ↔ constraint_23 c row := by
  rfl

/-- Previous-state read `1`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_24 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 20)
      (state_read_prev_timestamp c 1 row)
      (state_read_timestamp_lt_aux_0 c 1 row)
      (state_read_timestamp_lt_aux_1 c 1 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_24_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_24 c row ↔ constraint_24 c row := by
  rfl

/-- Previous-state read `2`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_25 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 21)
      (state_read_prev_timestamp c 2 row)
      (state_read_timestamp_lt_aux_0 c 2 row)
      (state_read_timestamp_lt_aux_1 c 2 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_25_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_25 c row ↔ constraint_25 c row := by
  rfl

/-- Previous-state read `3`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_26 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 22)
      (state_read_prev_timestamp c 3 row)
      (state_read_timestamp_lt_aux_0 c 3 row)
      (state_read_timestamp_lt_aux_1 c 3 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_26_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_26 c row ↔ constraint_26 c row := by
  rfl

/-- Previous-state read `4`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_27 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 23)
      (state_read_prev_timestamp c 4 row)
      (state_read_timestamp_lt_aux_0 c 4 row)
      (state_read_timestamp_lt_aux_1 c 4 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_27_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_27 c row ↔ constraint_27 c row := by
  rfl

/-- Previous-state read `5`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_28 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 24)
      (state_read_prev_timestamp c 5 row)
      (state_read_timestamp_lt_aux_0 c 5 row)
      (state_read_timestamp_lt_aux_1 c 5 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_28_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_28 c row ↔ constraint_28 c row := by
  rfl

/-- Previous-state read `6`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_29 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 25)
      (state_read_prev_timestamp c 6 row)
      (state_read_timestamp_lt_aux_0 c 6 row)
      (state_read_timestamp_lt_aux_1 c 6 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_29_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_29 c row ↔ constraint_29 c row := by
  rfl

/-- Previous-state read `7`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_30 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 26)
      (state_read_prev_timestamp c 7 row)
      (state_read_timestamp_lt_aux_0 c 7 row)
      (state_read_timestamp_lt_aux_1 c 7 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_30_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_30 c row ↔ constraint_30 c row := by
  rfl

/-- Destination write `0`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_31 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 27)
      (write_prev_timestamp c 0 row)
      (write_timestamp_lt_aux_0 c 0 row)
      (write_timestamp_lt_aux_1 c 0 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_31_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_31 c row ↔ constraint_31 c row := by
  rfl

/-- Destination write `1`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_32 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 28)
      (write_prev_timestamp c 1 row)
      (write_timestamp_lt_aux_0 c 1 row)
      (write_timestamp_lt_aux_1 c 1 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_32_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_32 c row ↔ constraint_32 c row := by
  rfl

/-- Destination write `2`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_33 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 29)
      (write_prev_timestamp c 2 row)
      (write_timestamp_lt_aux_0 c 2 row)
      (write_timestamp_lt_aux_1 c 2 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_33_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_33 c row ↔ constraint_33 c row := by
  rfl

/-- Destination write `3`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_34 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 30)
      (write_prev_timestamp c 3 row)
      (write_timestamp_lt_aux_0 c 3 row)
      (write_timestamp_lt_aux_1 c 3 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_34_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_34 c row ↔ constraint_34 c row := by
  rfl

/-- Destination write `4`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_35 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 31)
      (write_prev_timestamp c 4 row)
      (write_timestamp_lt_aux_0 c 4 row)
      (write_timestamp_lt_aux_1 c 4 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_35_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_35 c row ↔ constraint_35 c row := by
  rfl

/-- Destination write `5`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_36 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 32)
      (write_prev_timestamp c 5 row)
      (write_timestamp_lt_aux_0 c 5 row)
      (write_timestamp_lt_aux_1 c 5 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_36_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_36 c row ↔ constraint_36 c row := by
  rfl

/-- Destination write `6`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_37 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 33)
      (write_prev_timestamp c 6 row)
      (write_timestamp_lt_aux_0 c 6 row)
      (write_timestamp_lt_aux_1 c 6 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_37_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_37 c row ↔ constraint_37 c row := by
  rfl

/-- Destination write `7`: timestamp delta matches the memory-bridge range witness. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def constraint_38 (c : C F ExtF) (row : ℕ) : Prop :=
  ((is_enabled c row) *
    (timestamp_delta_expr
      ((from_timestamp c row) + 34)
      (write_prev_timestamp c 7 row)
      (write_timestamp_lt_aux_0 c 7 row)
      (write_timestamp_lt_aux_1 c 7 row))) = 0

@[Sha2MainAir_Sha256Config_air_simplification]
lemma constraint_38_of_extraction
    (c : C F ExtF) (row : ℕ) :
    Sha2MainAir_Sha256Config.extraction.constraint_38 c row ↔ constraint_38 c row := by
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

/-- The transpiled SHA-256 OpenVM opcode at offset `0x320`. -/
abbrev sha256Opcode : F := (800 : F)

/-- The main-chip timestamp delta: 3 register reads, 16 input reads, 8 state reads, 8 writes. -/
abbrev timestampDelta : F := (35 : F)

/-- Negative memory-bus entry for the previous memory contents. -/
abbrev memoryPrevEntry (mul addrSpace ptr x0 x1 x2 x3 prevTs : F) : F × List F :=
  (negativeMultiplicityCoeff * mul, [addrSpace, ptr, x0, x1, x2, x3, prevTs])

/-- Positive memory-bus entry for the current read or write. -/
abbrev memoryCurrEntry (mul addrSpace ptr x0 x1 x2 x3 ts : F) : F × List F :=
  (mul, [addrSpace, ptr, x0, x1, x2, x3, ts])

/-- Execution-bus entries emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def executionBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (-is_enabled c row, [from_pc c row, from_timestamp c row]),
    (is_enabled c row, [from_pc c row + 4, from_timestamp c row + timestampDelta])
  ]

/-- Program-bus entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def programBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (is_enabled c row,
      [ from_pc c row,
        sha256Opcode,
        dst_reg_ptr c row,
        state_reg_ptr c row,
        input_reg_ptr c row,
        1,
        2,
        0,
        0 ])
  ]

/-- Register-file memory-bus entries emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
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
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def inputMemoryBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  (List.range 16).flatMap fun i : ℕ =>
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
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def stateMemoryBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  (List.range 8).flatMap fun i : ℕ =>
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
        (from_timestamp c row + (((19 + i : ℕ) : F)))
    ]

/-- Guest-memory destination writes emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def writeMemoryBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  (List.range 8).flatMap fun i : ℕ =>
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
        (from_timestamp c row + (((27 + i : ℕ) : F)))
    ]

/-- All memory-bus entries emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def memoryBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  registerMemoryBus_row c row ++
  inputMemoryBus_row c row ++
  stateMemoryBus_row c row ++
  writeMemoryBus_row c row

/-- Bitwise lookup entries enforcing the 24-bit pointer bound. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def bitwiseLookupBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (is_enabled c row, [dst_ptr_limb c 3 row * 8, state_ptr_limb c 3 row * 8, 0, 0]),
    (is_enabled c row, [input_ptr_limb c 3 row * 8, input_ptr_limb c 3 row * 8, 0, 0])
  ]

/-- The SHA-2 `State` wrapper-bus entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def sha2StateBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (is_enabled c row,
      [0, request_id c row] ++
      (List.range 16).map (fun i => prev_state_u16 c i row) ++
      (List.range 32).map (fun i => new_state_byte c i row))
  ]

/-- The SHA-2 `Message1` wrapper-bus entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def sha2Message1Bus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (is_enabled c row,
      [1, request_id c row] ++
      (List.range 32).map (fun i => message_byte c i row))
  ]

/-- The SHA-2 `Message2` wrapper-bus entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def sha2Message2Bus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (is_enabled c row,
      [2, request_id c row] ++
      (List.range 32).map (fun i => message_byte c (32 + i) row))
  ]

/-- All SHA-2 wrapper-bus entries emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def sha2Bus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  sha2StateBus_row c row ++
  sha2Message1Bus_row c row ++
  sha2Message2Bus_row c row

end constraint_simplification

end Sha2MainAir_sha256.constraints

namespace Sha2MainAir_Sha256Config.extraction

section grouped_constraints

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-- The full extracted SHA-256 main-air row contract: all extracted row
constraints bundled into a single proposition. -/
def constrain_row (c : C F ExtF) (row : ℕ) : Prop :=
  constraint_0 c row ∧
  constraint_1 c row ∧
  constraint_2 c row ∧
  constraint_3 c row ∧
  constraint_4 c row ∧
  constraint_5 c row ∧
  constraint_6 c row ∧
  constraint_7 c row ∧
  constraint_8 c row ∧
  constraint_9 c row ∧
  constraint_10 c row ∧
  constraint_11 c row ∧
  constraint_12 c row ∧
  constraint_13 c row ∧
  constraint_14 c row ∧
  constraint_15 c row ∧
  constraint_16 c row ∧
  constraint_17 c row ∧
  constraint_18 c row ∧
  constraint_19 c row ∧
  constraint_20 c row ∧
  constraint_21 c row ∧
  constraint_22 c row ∧
  constraint_23 c row ∧
  constraint_24 c row ∧
  constraint_25 c row ∧
  constraint_26 c row ∧
  constraint_27 c row ∧
  constraint_28 c row ∧
  constraint_29 c row ∧
  constraint_30 c row ∧
  constraint_31 c row ∧
  constraint_32 c row ∧
  constraint_33 c row ∧
  constraint_34 c row ∧
  constraint_35 c row ∧
  constraint_36 c row ∧
  constraint_37 c row ∧
  constraint_38 c row

end grouped_constraints

end Sha2MainAir_Sha256Config.extraction
