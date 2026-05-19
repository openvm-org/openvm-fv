import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.TraceSpec

set_option autoImplicit false

/-!
Proof lemmas extracted from `TraceSpec.lean`.

This is the SHA-512 analogue of the SHA-256 `Core/SpecFacts` layer, adapted to
the 64-bit block-hasher column map and the 6-cell ternary selector.
-/

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

lemma next_main_eq_main_succ
    (air : C FBB ExtF) (hrot : rotation_consistent air) (column row : ℕ)
    (hrow : row < Circuit.last_row air) :
    Circuit.main air (id := 0) (column := column) (row := row) (rotation := 1) =
      Circuit.main air (id := 0) (column := column) (row := row + 1) (rotation := 0) :=
  hrot.1 column row hrow

lemma last_row_main_eq_first
    (air : C FBB ExtF) (hrot : rotation_consistent air) (column : ℕ) :
    Circuit.main air (id := 0) (column := column) (row := Circuit.last_row air) (rotation := 1) =
      Circuit.main air (id := 0) (column := column) (row := 0) (rotation := 0) :=
  hrot.2 column

lemma next_request_id_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_request_id air row = request_id air (row + 1) := by
  simpa [next_request_id, request_id] using next_main_eq_main_succ air hrot 0 row hrow

lemma next_request_id_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_request_id air row = request_id air (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_request_id_eq air hrot row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_request_id, request_id, last_row_main_eq_first air hrot 0]

lemma next_is_round_row_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_is_round_row air row = is_round_row air (row + 1) := by
  simpa [next_is_round_row, is_round_row] using next_main_eq_main_succ air hrot 1 row hrow

lemma next_is_first_4_rows_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_is_first_4_rows air row = is_first_4_rows air (row + 1) := by
  simpa [next_is_first_4_rows, is_first_4_rows] using next_main_eq_main_succ air hrot 2 row hrow

lemma next_is_digest_row_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_is_digest_row air row = is_digest_row air (row + 1) := by
  simpa [next_is_digest_row, is_digest_row] using next_main_eq_main_succ air hrot 3 row hrow

lemma next_is_round_row_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_is_round_row air row = is_round_row air (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_is_round_row_eq air hrot row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_is_round_row, is_round_row, last_row_main_eq_first air hrot 1]

lemma next_is_first_4_rows_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_is_first_4_rows air row = is_first_4_rows air (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_is_first_4_rows_eq air hrot row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_is_first_4_rows, is_first_4_rows,
      last_row_main_eq_first air hrot 2]

lemma next_is_digest_row_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_is_digest_row air row = is_digest_row air (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_is_digest_row_eq air hrot row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_is_digest_row, is_digest_row,
      last_row_main_eq_first air hrot 3]

lemma next_padding_flag_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_padding_flag air row = padding_flag air (nextRow air row) := by
  simp [next_padding_flag, padding_flag,
    next_is_round_row_eq_nextRow air hrot row hvalid,
    next_is_digest_row_eq_nextRow air hrot row hvalid]

lemma encoder_idx_next_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (i row : ℕ)
    (hrow : row < Circuit.last_row air) :
    encoder_idx_next air i row = encoder_idx air i (row + 1) := by
  simpa [encoder_idx_next, encoder_idx] using next_main_eq_main_succ air hrot (4 + i) row hrow

lemma encoder_idx_next_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (i row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    encoder_idx_next air i row = encoder_idx air i (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, encoder_idx_next_eq air hrot i row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, encoder_idx_next, encoder_idx,
      last_row_main_eq_first air hrot (4 + i)]

lemma next_encoder_selector_idx_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_encoder_selector_idx air row = encoder_selector_idx air (nextRow air row) := by
  simp [next_encoder_selector_idx, encoder_selector_idx, encoder_selector_from,
    encoder_digit_sum_from, encoder_idx_next_eq_nextRow air hrot 0 row hvalid,
    encoder_idx_next_eq_nextRow air hrot 1 row hvalid,
    encoder_idx_next_eq_nextRow air hrot 2 row hvalid,
    encoder_idx_next_eq_nextRow air hrot 3 row hvalid,
    encoder_idx_next_eq_nextRow air hrot 4 row hvalid,
    encoder_idx_next_eq_nextRow air hrot 5 row hvalid]

lemma next_global_block_idx_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_global_block_idx air row = global_block_idx air (row + 1) := by
  simpa [next_global_block_idx, global_block_idx] using next_main_eq_main_succ air hrot 10 row hrow

lemma next_global_block_idx_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_global_block_idx air row = global_block_idx air (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_global_block_idx_eq air hrot row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_global_block_idx, global_block_idx,
      last_row_main_eq_first air hrot 10]

lemma next_work_vars_a_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot bit row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_work_vars_a air slot bit row = work_vars_a air slot bit (row + 1) := by
  simpa [next_work_vars_a, work_vars_a] using
    next_main_eq_main_succ air hrot (11 + 64 * slot + bit) row hrow

lemma next_work_vars_a_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot bit row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_work_vars_a air slot bit row = work_vars_a air slot bit (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_work_vars_a_eq air hrot slot bit row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_work_vars_a, work_vars_a,
      last_row_main_eq_first air hrot (11 + 64 * slot + bit)]

lemma next_work_vars_e_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot bit row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_work_vars_e air slot bit row = work_vars_e air slot bit (row + 1) := by
  simpa [next_work_vars_e, work_vars_e] using
    next_main_eq_main_succ air hrot (267 + 64 * slot + bit) row hrow

lemma next_work_vars_e_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot bit row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_work_vars_e air slot bit row = work_vars_e air slot bit (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_work_vars_e_eq air hrot slot bit row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_work_vars_e, work_vars_e,
      last_row_main_eq_first air hrot (267 + 64 * slot + bit)]

lemma next_carry_a_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_carry_a air slot limb row = carry_a air slot limb (row + 1) := by
  simpa [next_carry_a, carry_a] using
    next_main_eq_main_succ air hrot (523 + 4 * slot + limb) row hrow

lemma next_carry_a_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_carry_a air slot limb row = carry_a air slot limb (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_carry_a_eq air hrot slot limb row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_carry_a, carry_a,
      last_row_main_eq_first air hrot (523 + 4 * slot + limb)]

lemma next_carry_e_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_carry_e air slot limb row = carry_e air slot limb (row + 1) := by
  simpa [next_carry_e, carry_e] using
    next_main_eq_main_succ air hrot (539 + 4 * slot + limb) row hrow

lemma next_carry_e_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_carry_e air slot limb row = carry_e air slot limb (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_carry_e_eq air hrot slot limb row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_carry_e, carry_e,
      last_row_main_eq_first air hrot (539 + 4 * slot + limb)]

lemma next_schedule_helper_w_3_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_schedule_helper_w_3 air slot limb row = schedule_helper_w_3 air slot limb (row + 1) := by
  simpa [next_schedule_helper_w_3, schedule_helper_w_3] using
    next_main_eq_main_succ air hrot (555 + 4 * slot + limb) row hrow

lemma next_schedule_helper_w_3_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_schedule_helper_w_3 air slot limb row = schedule_helper_w_3 air slot limb (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_schedule_helper_w_3_eq air hrot slot limb row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_schedule_helper_w_3, schedule_helper_w_3,
      last_row_main_eq_first air hrot (555 + 4 * slot + limb)]

lemma next_intermed_4_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_intermed_4 air slot limb row = intermed_4 air slot limb (row + 1) := by
  simpa [next_intermed_4, intermed_4] using
    next_main_eq_main_succ air hrot (567 + 4 * slot + limb) row hrow

lemma next_intermed_4_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_intermed_4 air slot limb row = intermed_4 air slot limb (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_intermed_4_eq air hrot slot limb row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_intermed_4, intermed_4,
      last_row_main_eq_first air hrot (567 + 4 * slot + limb)]

lemma next_intermed_8_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_intermed_8 air slot limb row = intermed_8 air slot limb (row + 1) := by
  simpa [next_intermed_8, intermed_8] using
    next_main_eq_main_succ air hrot (583 + 4 * slot + limb) row hrow

lemma next_intermed_8_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_intermed_8 air slot limb row = intermed_8 air slot limb (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_intermed_8_eq air hrot slot limb row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_intermed_8, intermed_8,
      last_row_main_eq_first air hrot (583 + 4 * slot + limb)]

lemma next_intermed_12_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_intermed_12 air slot limb row = intermed_12 air slot limb (row + 1) := by
  simpa [next_intermed_12, intermed_12] using
    next_main_eq_main_succ air hrot (599 + 4 * slot + limb) row hrow

lemma next_intermed_12_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot limb row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_intermed_12 air slot limb row = intermed_12 air slot limb (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_intermed_12_eq air hrot slot limb row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_intermed_12, intermed_12,
      last_row_main_eq_first air hrot (599 + 4 * slot + limb)]

lemma next_msg_schedule_w_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot bit row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_msg_schedule_w air slot bit row = msg_schedule_w air slot bit (row + 1) := by
  simpa [next_msg_schedule_w, msg_schedule_w] using
    next_main_eq_main_succ air hrot (615 + 64 * slot + bit) row hrow

lemma next_msg_schedule_w_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot bit row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_msg_schedule_w air slot bit row = msg_schedule_w air slot bit (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_msg_schedule_w_eq air hrot slot bit row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_msg_schedule_w, msg_schedule_w,
      last_row_main_eq_first air hrot (615 + 64 * slot + bit)]

lemma next_msg_schedule_carry_or_buffer_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot byte row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_msg_schedule_carry_or_buffer air slot byte row =
      msg_schedule_carry_or_buffer air slot byte (row + 1) := by
  simpa [next_msg_schedule_carry_or_buffer, msg_schedule_carry_or_buffer] using
    next_main_eq_main_succ air hrot (871 + 8 * slot + byte) row hrow

lemma next_msg_schedule_carry_or_buffer_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (slot byte row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_msg_schedule_carry_or_buffer air slot byte row =
      msg_schedule_carry_or_buffer air slot byte (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne,
      next_msg_schedule_carry_or_buffer_eq air hrot slot byte row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_msg_schedule_carry_or_buffer, msg_schedule_carry_or_buffer,
      last_row_main_eq_first air hrot (871 + 8 * slot + byte)]

lemma next_final_hash_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (word byte row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_final_hash air word byte row = final_hash air word byte (row + 1) := by
  simpa [next_final_hash, final_hash] using
    next_main_eq_main_succ air hrot (615 + 8 * word + byte) row hrow

lemma next_final_hash_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (word byte row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_final_hash air word byte row = final_hash air word byte (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_final_hash_eq air hrot word byte row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_final_hash, final_hash,
      last_row_main_eq_first air hrot (615 + 8 * word + byte)]

lemma next_prev_hash_eq
    (air : C FBB ExtF) (hrot : rotation_consistent air) (word limb row : ℕ)
    (hrow : row < Circuit.last_row air) :
    next_prev_hash air word limb row = prev_hash air word limb (row + 1) := by
  simpa [next_prev_hash, prev_hash] using
    next_main_eq_main_succ air hrot (679 + 4 * word + limb) row hrow

lemma next_prev_hash_eq_nextRow
    (air : C FBB ExtF) (hrot : rotation_consistent air) (word limb row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_prev_hash air word limb row = prev_hash air word limb (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_prev_hash_eq air hrot word limb row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_prev_hash, prev_hash,
      last_row_main_eq_first air hrot (679 + 4 * word + limb)]

lemma scheduleWordAtRow_eq_bitsWordToUInt64
    (air : C FBB ExtF) (row slot : ℕ) :
    scheduleWordAtRow air row slot = bitsWordToUInt64 (scheduleBitsWord air row slot) := by
  rfl

lemma blockStateRow_zero (air : C FBB ExtF) (start : ℕ) :
    blockStateRow air start 0 = prevRow air start := by
  by_cases hstart : start = 0
  · simp [blockStateRow, prevRow, hstart]
  · simp [blockStateRow, prevRow, hstart]

lemma blockStateRow_succ (air : C FBB ExtF) (start offset : ℕ) :
    blockStateRow air start (offset + 1) = start + offset := by
  by_cases hstart : start = 0
  · simp [blockStateRow, hstart]
  · simpa [blockStateRow, hstart] using Nat.succ_sub_one (start + offset)

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
