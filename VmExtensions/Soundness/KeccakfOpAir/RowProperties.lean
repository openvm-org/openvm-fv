import VmExtensions.Constraints.KeccakfOpAir
import VmExtensions.Soundness.KeccakfOpAir.FieldLemmas

set_option linter.all false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace KeccakfOpAir.Soundness

open KeccakfOpAir.constraints

/-!
# Row Properties for KeccakfOpAir

Structural facts derived from row constraints.
-/

variable {F ExtF : Type} [Field F] [Field ExtF]

lemma extractedInteractions_of_allHold_simplified
    {air : Valid_KeccakfOpAir F ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row) :
    KeccakfOpAir.extraction.constrain_interactions air :=
  h.1

lemma rows_of_allHold_simplified
    {air : Valid_KeccakfOpAir F ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row) :
    List.Forall (·) (row_constraint_list air row) :=
  h.2

-- List.Forall (·) on a concrete list implies each element, by index.
lemma forall_list_get {l : List Prop} (h : List.Forall (·) l)
    {i : ℕ} (hi : i < l.length) : l[i] := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons a t ih =>
    rw [List.forall_cons] at h
    cases i with
    | zero => exact h.1
    | succ n => exact ih h.2 (Nat.lt_of_succ_lt_succ hi)

-- The row constraint list always has 52 elements.
lemma rcl_length (air : Valid_KeccakfOpAir F ExtF) (row : ℕ) :
    (row_constraint_list air row).length = 52 := by
  rfl

-- is_valid is binary
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma is_valid_binary (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    : is_valid air row = 0 ∨ is_valid air row = 1 := by
  have hlen := rcl_length air row
  have h0 := forall_list_get hc (show (0 : ℕ) < _ by omega)
  change constraint_0 air row at h0
  exact binary_of_mul_sub_one_eq_zero h0

-- When is_valid = 1, rd_aux timestamp decomposition holds
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma rd_aux_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row - rd_aux_prev_ts air row - 1 -
        (rd_aux_lower_decomp_0 air row + rd_aux_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h1 := forall_list_get hc (show (1 : ℕ) < _ by omega)
  change constraint_1 air row at h1
  unfold constraint_1 at h1
  exact eq_zero_of_enabled_mul h1 hen

/-! ## buf_aux timestamp decomposition lemmas (constraints 2-51)

Each buf_aux_k (k=0..49) has a timestamp decomposition constraint:
  is_valid * ((timestamp + (k+1) - buf_aux_k_prev_ts) - 1 -
    (buf_aux_k_lower_decomp_0 + buf_aux_k_lower_decomp_1 * 131072)) = 0

When is_valid = 1, the inner expression equals 0.
-/

-- buf_aux_0 timestamp decomposition (constraint 2)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_0_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 1 - buf_aux_0_prev_ts air row - 1 -
        (buf_aux_0_lower_decomp_0 air row + buf_aux_0_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h2 := forall_list_get hc (show (2 : ℕ) < _ by omega)
  change constraint_2 air row at h2
  unfold constraint_2 at h2
  exact eq_zero_of_enabled_mul h2 hen

-- buf_aux_1 timestamp decomposition (constraint 3)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_1_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 2 - buf_aux_1_prev_ts air row - 1 -
        (buf_aux_1_lower_decomp_0 air row + buf_aux_1_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h3 := forall_list_get hc (show (3 : ℕ) < _ by omega)
  change constraint_3 air row at h3
  unfold constraint_3 at h3
  exact eq_zero_of_enabled_mul h3 hen

-- buf_aux_2 timestamp decomposition (constraint 4)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_2_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 3 - buf_aux_2_prev_ts air row - 1 -
        (buf_aux_2_lower_decomp_0 air row + buf_aux_2_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h4 := forall_list_get hc (show (4 : ℕ) < _ by omega)
  change constraint_4 air row at h4
  unfold constraint_4 at h4
  exact eq_zero_of_enabled_mul h4 hen

-- buf_aux_3 timestamp decomposition (constraint 5)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_3_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 4 - buf_aux_3_prev_ts air row - 1 -
        (buf_aux_3_lower_decomp_0 air row + buf_aux_3_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h5 := forall_list_get hc (show (5 : ℕ) < _ by omega)
  change constraint_5 air row at h5
  unfold constraint_5 at h5
  exact eq_zero_of_enabled_mul h5 hen

-- buf_aux_4 timestamp decomposition (constraint 6)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_4_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 5 - buf_aux_4_prev_ts air row - 1 -
        (buf_aux_4_lower_decomp_0 air row + buf_aux_4_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h6 := forall_list_get hc (show (6 : ℕ) < _ by omega)
  change constraint_6 air row at h6
  unfold constraint_6 at h6
  exact eq_zero_of_enabled_mul h6 hen

-- buf_aux_5 timestamp decomposition (constraint 7)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_5_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 6 - buf_aux_5_prev_ts air row - 1 -
        (buf_aux_5_lower_decomp_0 air row + buf_aux_5_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h7 := forall_list_get hc (show (7 : ℕ) < _ by omega)
  change constraint_7 air row at h7
  unfold constraint_7 at h7
  exact eq_zero_of_enabled_mul h7 hen

-- buf_aux_6 timestamp decomposition (constraint 8)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_6_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 7 - buf_aux_6_prev_ts air row - 1 -
        (buf_aux_6_lower_decomp_0 air row + buf_aux_6_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h8 := forall_list_get hc (show (8 : ℕ) < _ by omega)
  change constraint_8 air row at h8
  unfold constraint_8 at h8
  exact eq_zero_of_enabled_mul h8 hen

-- buf_aux_7 timestamp decomposition (constraint 9)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_7_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 8 - buf_aux_7_prev_ts air row - 1 -
        (buf_aux_7_lower_decomp_0 air row + buf_aux_7_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h9 := forall_list_get hc (show (9 : ℕ) < _ by omega)
  change constraint_9 air row at h9
  unfold constraint_9 at h9
  exact eq_zero_of_enabled_mul h9 hen

-- buf_aux_8 timestamp decomposition (constraint 10)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_8_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 9 - buf_aux_8_prev_ts air row - 1 -
        (buf_aux_8_lower_decomp_0 air row + buf_aux_8_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h10 := forall_list_get hc (show (10 : ℕ) < _ by omega)
  change constraint_10 air row at h10
  unfold constraint_10 at h10
  exact eq_zero_of_enabled_mul h10 hen

-- buf_aux_9 timestamp decomposition (constraint 11)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_9_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 10 - buf_aux_9_prev_ts air row - 1 -
        (buf_aux_9_lower_decomp_0 air row + buf_aux_9_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h11 := forall_list_get hc (show (11 : ℕ) < _ by omega)
  change constraint_11 air row at h11
  unfold constraint_11 at h11
  exact eq_zero_of_enabled_mul h11 hen

-- buf_aux_10 timestamp decomposition (constraint 12)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_10_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 11 - buf_aux_10_prev_ts air row - 1 -
        (buf_aux_10_lower_decomp_0 air row + buf_aux_10_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h12 := forall_list_get hc (show (12 : ℕ) < _ by omega)
  change constraint_12 air row at h12
  unfold constraint_12 at h12
  exact eq_zero_of_enabled_mul h12 hen

-- buf_aux_11 timestamp decomposition (constraint 13)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_11_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 12 - buf_aux_11_prev_ts air row - 1 -
        (buf_aux_11_lower_decomp_0 air row + buf_aux_11_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h13 := forall_list_get hc (show (13 : ℕ) < _ by omega)
  change constraint_13 air row at h13
  unfold constraint_13 at h13
  exact eq_zero_of_enabled_mul h13 hen

-- buf_aux_12 timestamp decomposition (constraint 14)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_12_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 13 - buf_aux_12_prev_ts air row - 1 -
        (buf_aux_12_lower_decomp_0 air row + buf_aux_12_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h14 := forall_list_get hc (show (14 : ℕ) < _ by omega)
  change constraint_14 air row at h14
  unfold constraint_14 at h14
  exact eq_zero_of_enabled_mul h14 hen

-- buf_aux_13 timestamp decomposition (constraint 15)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_13_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 14 - buf_aux_13_prev_ts air row - 1 -
        (buf_aux_13_lower_decomp_0 air row + buf_aux_13_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h15 := forall_list_get hc (show (15 : ℕ) < _ by omega)
  change constraint_15 air row at h15
  unfold constraint_15 at h15
  exact eq_zero_of_enabled_mul h15 hen

-- buf_aux_14 timestamp decomposition (constraint 16)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_14_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 15 - buf_aux_14_prev_ts air row - 1 -
        (buf_aux_14_lower_decomp_0 air row + buf_aux_14_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h16 := forall_list_get hc (show (16 : ℕ) < _ by omega)
  change constraint_16 air row at h16
  unfold constraint_16 at h16
  exact eq_zero_of_enabled_mul h16 hen

-- buf_aux_15 timestamp decomposition (constraint 17)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_15_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 16 - buf_aux_15_prev_ts air row - 1 -
        (buf_aux_15_lower_decomp_0 air row + buf_aux_15_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h17 := forall_list_get hc (show (17 : ℕ) < _ by omega)
  change constraint_17 air row at h17
  unfold constraint_17 at h17
  exact eq_zero_of_enabled_mul h17 hen

-- buf_aux_16 timestamp decomposition (constraint 18)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_16_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 17 - buf_aux_16_prev_ts air row - 1 -
        (buf_aux_16_lower_decomp_0 air row + buf_aux_16_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h18 := forall_list_get hc (show (18 : ℕ) < _ by omega)
  change constraint_18 air row at h18
  unfold constraint_18 at h18
  exact eq_zero_of_enabled_mul h18 hen

-- buf_aux_17 timestamp decomposition (constraint 19)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_17_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 18 - buf_aux_17_prev_ts air row - 1 -
        (buf_aux_17_lower_decomp_0 air row + buf_aux_17_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h19 := forall_list_get hc (show (19 : ℕ) < _ by omega)
  change constraint_19 air row at h19
  unfold constraint_19 at h19
  exact eq_zero_of_enabled_mul h19 hen

-- buf_aux_18 timestamp decomposition (constraint 20)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_18_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 19 - buf_aux_18_prev_ts air row - 1 -
        (buf_aux_18_lower_decomp_0 air row + buf_aux_18_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h20 := forall_list_get hc (show (20 : ℕ) < _ by omega)
  change constraint_20 air row at h20
  unfold constraint_20 at h20
  exact eq_zero_of_enabled_mul h20 hen

-- buf_aux_19 timestamp decomposition (constraint 21)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_19_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 20 - buf_aux_19_prev_ts air row - 1 -
        (buf_aux_19_lower_decomp_0 air row + buf_aux_19_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h21 := forall_list_get hc (show (21 : ℕ) < _ by omega)
  change constraint_21 air row at h21
  unfold constraint_21 at h21
  exact eq_zero_of_enabled_mul h21 hen

-- buf_aux_20 timestamp decomposition (constraint 22)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_20_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 21 - buf_aux_20_prev_ts air row - 1 -
        (buf_aux_20_lower_decomp_0 air row + buf_aux_20_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h22 := forall_list_get hc (show (22 : ℕ) < _ by omega)
  change constraint_22 air row at h22
  unfold constraint_22 at h22
  exact eq_zero_of_enabled_mul h22 hen

-- buf_aux_21 timestamp decomposition (constraint 23)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_21_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 22 - buf_aux_21_prev_ts air row - 1 -
        (buf_aux_21_lower_decomp_0 air row + buf_aux_21_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h23 := forall_list_get hc (show (23 : ℕ) < _ by omega)
  change constraint_23 air row at h23
  unfold constraint_23 at h23
  exact eq_zero_of_enabled_mul h23 hen

-- buf_aux_22 timestamp decomposition (constraint 24)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_22_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 23 - buf_aux_22_prev_ts air row - 1 -
        (buf_aux_22_lower_decomp_0 air row + buf_aux_22_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h24 := forall_list_get hc (show (24 : ℕ) < _ by omega)
  change constraint_24 air row at h24
  unfold constraint_24 at h24
  exact eq_zero_of_enabled_mul h24 hen

-- buf_aux_23 timestamp decomposition (constraint 25)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_23_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 24 - buf_aux_23_prev_ts air row - 1 -
        (buf_aux_23_lower_decomp_0 air row + buf_aux_23_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h25 := forall_list_get hc (show (25 : ℕ) < _ by omega)
  change constraint_25 air row at h25
  unfold constraint_25 at h25
  exact eq_zero_of_enabled_mul h25 hen

-- buf_aux_24 timestamp decomposition (constraint 26)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_24_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 25 - buf_aux_24_prev_ts air row - 1 -
        (buf_aux_24_lower_decomp_0 air row + buf_aux_24_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h26 := forall_list_get hc (show (26 : ℕ) < _ by omega)
  change constraint_26 air row at h26
  unfold constraint_26 at h26
  exact eq_zero_of_enabled_mul h26 hen

-- buf_aux_25 timestamp decomposition (constraint 27)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_25_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 26 - buf_aux_25_prev_ts air row - 1 -
        (buf_aux_25_lower_decomp_0 air row + buf_aux_25_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h27 := forall_list_get hc (show (27 : ℕ) < _ by omega)
  change constraint_27 air row at h27
  unfold constraint_27 at h27
  exact eq_zero_of_enabled_mul h27 hen

-- buf_aux_26 timestamp decomposition (constraint 28)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_26_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 27 - buf_aux_26_prev_ts air row - 1 -
        (buf_aux_26_lower_decomp_0 air row + buf_aux_26_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h28 := forall_list_get hc (show (28 : ℕ) < _ by omega)
  change constraint_28 air row at h28
  unfold constraint_28 at h28
  exact eq_zero_of_enabled_mul h28 hen

-- buf_aux_27 timestamp decomposition (constraint 29)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_27_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 28 - buf_aux_27_prev_ts air row - 1 -
        (buf_aux_27_lower_decomp_0 air row + buf_aux_27_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h29 := forall_list_get hc (show (29 : ℕ) < _ by omega)
  change constraint_29 air row at h29
  unfold constraint_29 at h29
  exact eq_zero_of_enabled_mul h29 hen

-- buf_aux_28 timestamp decomposition (constraint 30)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_28_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 29 - buf_aux_28_prev_ts air row - 1 -
        (buf_aux_28_lower_decomp_0 air row + buf_aux_28_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h30 := forall_list_get hc (show (30 : ℕ) < _ by omega)
  change constraint_30 air row at h30
  unfold constraint_30 at h30
  exact eq_zero_of_enabled_mul h30 hen

-- buf_aux_29 timestamp decomposition (constraint 31)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_29_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 30 - buf_aux_29_prev_ts air row - 1 -
        (buf_aux_29_lower_decomp_0 air row + buf_aux_29_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h31 := forall_list_get hc (show (31 : ℕ) < _ by omega)
  change constraint_31 air row at h31
  unfold constraint_31 at h31
  exact eq_zero_of_enabled_mul h31 hen

-- buf_aux_30 timestamp decomposition (constraint 32)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_30_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 31 - buf_aux_30_prev_ts air row - 1 -
        (buf_aux_30_lower_decomp_0 air row + buf_aux_30_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h32 := forall_list_get hc (show (32 : ℕ) < _ by omega)
  change constraint_32 air row at h32
  unfold constraint_32 at h32
  exact eq_zero_of_enabled_mul h32 hen

-- buf_aux_31 timestamp decomposition (constraint 33)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_31_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 32 - buf_aux_31_prev_ts air row - 1 -
        (buf_aux_31_lower_decomp_0 air row + buf_aux_31_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h33 := forall_list_get hc (show (33 : ℕ) < _ by omega)
  change constraint_33 air row at h33
  unfold constraint_33 at h33
  exact eq_zero_of_enabled_mul h33 hen

-- buf_aux_32 timestamp decomposition (constraint 34)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_32_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 33 - buf_aux_32_prev_ts air row - 1 -
        (buf_aux_32_lower_decomp_0 air row + buf_aux_32_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h34 := forall_list_get hc (show (34 : ℕ) < _ by omega)
  change constraint_34 air row at h34
  unfold constraint_34 at h34
  exact eq_zero_of_enabled_mul h34 hen

-- buf_aux_33 timestamp decomposition (constraint 35)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_33_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 34 - buf_aux_33_prev_ts air row - 1 -
        (buf_aux_33_lower_decomp_0 air row + buf_aux_33_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h35 := forall_list_get hc (show (35 : ℕ) < _ by omega)
  change constraint_35 air row at h35
  unfold constraint_35 at h35
  exact eq_zero_of_enabled_mul h35 hen

-- buf_aux_34 timestamp decomposition (constraint 36)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_34_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 35 - buf_aux_34_prev_ts air row - 1 -
        (buf_aux_34_lower_decomp_0 air row + buf_aux_34_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h36 := forall_list_get hc (show (36 : ℕ) < _ by omega)
  change constraint_36 air row at h36
  unfold constraint_36 at h36
  exact eq_zero_of_enabled_mul h36 hen

-- buf_aux_35 timestamp decomposition (constraint 37)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_35_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 36 - buf_aux_35_prev_ts air row - 1 -
        (buf_aux_35_lower_decomp_0 air row + buf_aux_35_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h37 := forall_list_get hc (show (37 : ℕ) < _ by omega)
  change constraint_37 air row at h37
  unfold constraint_37 at h37
  exact eq_zero_of_enabled_mul h37 hen

-- buf_aux_36 timestamp decomposition (constraint 38)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_36_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 37 - buf_aux_36_prev_ts air row - 1 -
        (buf_aux_36_lower_decomp_0 air row + buf_aux_36_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h38 := forall_list_get hc (show (38 : ℕ) < _ by omega)
  change constraint_38 air row at h38
  unfold constraint_38 at h38
  exact eq_zero_of_enabled_mul h38 hen

-- buf_aux_37 timestamp decomposition (constraint 39)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_37_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 38 - buf_aux_37_prev_ts air row - 1 -
        (buf_aux_37_lower_decomp_0 air row + buf_aux_37_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h39 := forall_list_get hc (show (39 : ℕ) < _ by omega)
  change constraint_39 air row at h39
  unfold constraint_39 at h39
  exact eq_zero_of_enabled_mul h39 hen

-- buf_aux_38 timestamp decomposition (constraint 40)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_38_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 39 - buf_aux_38_prev_ts air row - 1 -
        (buf_aux_38_lower_decomp_0 air row + buf_aux_38_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h40 := forall_list_get hc (show (40 : ℕ) < _ by omega)
  change constraint_40 air row at h40
  unfold constraint_40 at h40
  exact eq_zero_of_enabled_mul h40 hen

-- buf_aux_39 timestamp decomposition (constraint 41)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_39_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 40 - buf_aux_39_prev_ts air row - 1 -
        (buf_aux_39_lower_decomp_0 air row + buf_aux_39_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h41 := forall_list_get hc (show (41 : ℕ) < _ by omega)
  change constraint_41 air row at h41
  unfold constraint_41 at h41
  exact eq_zero_of_enabled_mul h41 hen

-- buf_aux_40 timestamp decomposition (constraint 42)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_40_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 41 - buf_aux_40_prev_ts air row - 1 -
        (buf_aux_40_lower_decomp_0 air row + buf_aux_40_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h42 := forall_list_get hc (show (42 : ℕ) < _ by omega)
  change constraint_42 air row at h42
  unfold constraint_42 at h42
  exact eq_zero_of_enabled_mul h42 hen

-- buf_aux_41 timestamp decomposition (constraint 43)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_41_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 42 - buf_aux_41_prev_ts air row - 1 -
        (buf_aux_41_lower_decomp_0 air row + buf_aux_41_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h43 := forall_list_get hc (show (43 : ℕ) < _ by omega)
  change constraint_43 air row at h43
  unfold constraint_43 at h43
  exact eq_zero_of_enabled_mul h43 hen

-- buf_aux_42 timestamp decomposition (constraint 44)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_42_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 43 - buf_aux_42_prev_ts air row - 1 -
        (buf_aux_42_lower_decomp_0 air row + buf_aux_42_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h44 := forall_list_get hc (show (44 : ℕ) < _ by omega)
  change constraint_44 air row at h44
  unfold constraint_44 at h44
  exact eq_zero_of_enabled_mul h44 hen

-- buf_aux_43 timestamp decomposition (constraint 45)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_43_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 44 - buf_aux_43_prev_ts air row - 1 -
        (buf_aux_43_lower_decomp_0 air row + buf_aux_43_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h45 := forall_list_get hc (show (45 : ℕ) < _ by omega)
  change constraint_45 air row at h45
  unfold constraint_45 at h45
  exact eq_zero_of_enabled_mul h45 hen

-- buf_aux_44 timestamp decomposition (constraint 46)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_44_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 45 - buf_aux_44_prev_ts air row - 1 -
        (buf_aux_44_lower_decomp_0 air row + buf_aux_44_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h46 := forall_list_get hc (show (46 : ℕ) < _ by omega)
  change constraint_46 air row at h46
  unfold constraint_46 at h46
  exact eq_zero_of_enabled_mul h46 hen

-- buf_aux_45 timestamp decomposition (constraint 47)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_45_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 46 - buf_aux_45_prev_ts air row - 1 -
        (buf_aux_45_lower_decomp_0 air row + buf_aux_45_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h47 := forall_list_get hc (show (47 : ℕ) < _ by omega)
  change constraint_47 air row at h47
  unfold constraint_47 at h47
  exact eq_zero_of_enabled_mul h47 hen

-- buf_aux_46 timestamp decomposition (constraint 48)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_46_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 47 - buf_aux_46_prev_ts air row - 1 -
        (buf_aux_46_lower_decomp_0 air row + buf_aux_46_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h48 := forall_list_get hc (show (48 : ℕ) < _ by omega)
  change constraint_48 air row at h48
  unfold constraint_48 at h48
  exact eq_zero_of_enabled_mul h48 hen

-- buf_aux_47 timestamp decomposition (constraint 49)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_47_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 48 - buf_aux_47_prev_ts air row - 1 -
        (buf_aux_47_lower_decomp_0 air row + buf_aux_47_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h49 := forall_list_get hc (show (49 : ℕ) < _ by omega)
  change constraint_49 air row at h49
  unfold constraint_49 at h49
  exact eq_zero_of_enabled_mul h49 hen

-- buf_aux_48 timestamp decomposition (constraint 50)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_48_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 49 - buf_aux_48_prev_ts air row - 1 -
        (buf_aux_48_lower_decomp_0 air row + buf_aux_48_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h50 := forall_list_get hc (show (50 : ℕ) < _ by omega)
  change constraint_50 air row at h50
  unfold constraint_50 at h50
  exact eq_zero_of_enabled_mul h50 hen

-- buf_aux_49 timestamp decomposition (constraint 51)
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buf_aux_49_timestamp_lt (air : Valid_KeccakfOpAir F ExtF) (row : ℕ)
    (hc : List.Forall (·) (row_constraint_list air row))
    (hen : is_valid air row = 1)
    : timestamp air row + 50 - buf_aux_49_prev_ts air row - 1 -
        (buf_aux_49_lower_decomp_0 air row + buf_aux_49_lower_decomp_1 air row * 131072) = 0 := by
  have hlen := rcl_length air row
  have h51 := forall_list_get hc (show (51 : ℕ) < _ by omega)
  change constraint_51 air row at h51
  unfold constraint_51 at h51
  exact eq_zero_of_enabled_mul h51 hen


end KeccakfOpAir.Soundness
