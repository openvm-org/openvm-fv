/-
  Structural lemmas proved from XorinVmAir row constraints (FBB-specialized).

  Extracts binary flags, pointer decomposition, and the length-padding
  relationship from the 177 row constraints.
-/
import VmExtensions.Soundness.XorinVmAir.FieldLemmas
import VmExtensions.Constraints.XorinVmAir
import VmExtensions.Spec.Xorin
import OpenvmFv.Fundamentals.BabyBear

set_option autoImplicit false
set_option linter.unusedVariables false

namespace XorinVmAir.Soundness

open XorinVmAir.constraints
open Xorin.Spec

variable {ExtF : Type} [Field ExtF]

/-! ## FBB value arithmetic helpers -/

open BabyBear in
lemma fbb_val_add {a b : FBB} (h : a.val + b.val < 2013265921) :
    (a + b).val = a.val + b.val := by
  simp [Fin.val_add, Nat.mod_eq_of_lt h]

open BabyBear in
lemma fbb_val_mul {a b : FBB} (h : a.val * b.val < 2013265921) :
    (a * b).val = a.val * b.val := by
  simp [Fin.val_mul, Nat.mod_eq_of_lt h]

open BabyBear in
lemma fbb_val_natCast {n : ℕ} (h : n < 2013265921) :
    (n : FBB).val = n := by
  simp [Nat.mod_eq_of_lt h]

/-! ## Cumulative Pad Sum and Active Words -/

-- Cumulative sum of (1 - is_padding_byte[k]) for k = 0..n-1.
-- This is the timestamp offset structure used by memoryBus_row.
noncomputable def cumulativePadSum
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (air : C F ExtF) (row : ℕ) : ℕ → F
  | 0 => 0
  | n + 1 => cumulativePadSum air row n + (1 - is_padding_byte air n row)

-- Number of active (non-padding) words, at ℕ level via spec.
noncomputable def activeWords
    (air : Valid_XorinVmAir FBB ExtF) (row : ℕ) : ℕ :=
  num_active_words (xorin_len air row).val

/-! ## Constraint Extraction Helpers -/

-- Extract the row-constraint conjunction from allHold_simplified.
lemma rows_of_allHold_simplified
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row) :
    List.Forall (·) (row_constraint_list air row) :=
  h.2

-- List.Forall (·) on a concrete list implies each element, by index.
private lemma forall_list_get {l : List Prop} (h : List.Forall (·) l)
    {i : ℕ} (hi : i < l.length) : l[i] := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons a t ih =>
    rw [List.forall_cons] at h
    cases i with
    | zero => exact h.1
    | succ n => exact ih h.2 (Nat.lt_of_succ_lt_succ hi)

-- The row constraint list always has 177 elements.
set_option maxHeartbeats 400000 in
private lemma rcl_length (air : Valid_XorinVmAir FBB ExtF) (row : ℕ) :
    (row_constraint_list air row).length = 177 := by
  rfl

/-! ## Constraint 0: is_enabled is binary -/

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- The `is_enabled` flag is binary: either 0 (disabled) or 1 (enabled). -/
lemma is_enabled_binary
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row) :
    is_enabled air row = 0 ∨ is_enabled air row = 1 := by
  have h_rows := rows_of_allHold_simplified h
  have hlen := rcl_length air row
  have hc := forall_list_get h_rows (show (0 : ℕ) < _ by omega)
  change constraint_0 air row at hc
  unfold constraint_0 at hc
  exact binary_of_mul_sub_one_eq_zero hc

/-! ## Constraints 72–74: Pointer/length limb decomposition (unconditional) -/

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma buffer_ptr_eq_limbs
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row) :
    buffer_ptr air row =
      buffer_ptr_limb air 0 row + buffer_ptr_limb air 1 row * 256 +
      buffer_ptr_limb air 2 row * 65536 + buffer_ptr_limb air 3 row * 16777216 := by
  have h_rows := rows_of_allHold_simplified h
  have hlen := rcl_length air row
  have hc := forall_list_get h_rows (show (72 : ℕ) < _ by omega)
  change constraint_72 air row at hc
  unfold constraint_72 at hc
  exact sub_eq_zero.mp hc

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma input_ptr_eq_limbs
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row) :
    input_ptr air row =
      input_ptr_limb air 0 row + input_ptr_limb air 1 row * 256 +
      input_ptr_limb air 2 row * 65536 + input_ptr_limb air 3 row * 16777216 := by
  have h_rows := rows_of_allHold_simplified h
  have hlen := rcl_length air row
  have hc := forall_list_get h_rows (show (73 : ℕ) < _ by omega)
  change constraint_73 air row at hc
  unfold constraint_73 at hc
  exact sub_eq_zero.mp hc

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma xorin_len_eq_limbs
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row) :
    xorin_len air row =
      len_limb air 0 row + len_limb air 1 row * 256 +
      len_limb air 2 row * 65536 + len_limb air 3 row * 16777216 := by
  have h_rows := rows_of_allHold_simplified h
  have hlen := rcl_length air row
  have hc := forall_list_get h_rows (show (74 : ℕ) < _ by omega)
  change constraint_74 air row at hc
  unfold constraint_74 at hc
  exact sub_eq_zero.mp hc

/-! ## Constraints 1–34: Padding byte flags are binary (unconditional) -/

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 4096 in
/-- Each padding flag is binary: `is_padding_byte j` is 0 or 1. -/
lemma padding_byte_binary
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (j : ℕ) (hj : j < 34) :
    is_padding_byte air j row = 0 ∨ is_padding_byte air j row = 1 := by
  have h_rows := rows_of_allHold_simplified h
  have hlen := rcl_length air row
  have hidx : j + 1 < (row_constraint_list air row).length := by rw [hlen]; omega
  have hc := forall_list_get h_rows hidx
  revert hc
  interval_cases j <;> (intro hc; exact binary_of_mul_sub_one_eq_zero hc)

/-! ## Constraint 35: xorin_len = 4 * count of non-padding words -/

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
lemma xorin_len_eq_four_mul_active_count
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1) :
    xorin_len air row = (((((((((((((((((((((((((((((((((
      (1 - is_padding_byte air 0 row) +
      (1 - is_padding_byte air 1 row)) +
      (1 - is_padding_byte air 2 row)) +
      (1 - is_padding_byte air 3 row)) +
      (1 - is_padding_byte air 4 row)) +
      (1 - is_padding_byte air 5 row)) +
      (1 - is_padding_byte air 6 row)) +
      (1 - is_padding_byte air 7 row)) +
      (1 - is_padding_byte air 8 row)) +
      (1 - is_padding_byte air 9 row)) +
      (1 - is_padding_byte air 10 row)) +
      (1 - is_padding_byte air 11 row)) +
      (1 - is_padding_byte air 12 row)) +
      (1 - is_padding_byte air 13 row)) +
      (1 - is_padding_byte air 14 row)) +
      (1 - is_padding_byte air 15 row)) +
      (1 - is_padding_byte air 16 row)) +
      (1 - is_padding_byte air 17 row)) +
      (1 - is_padding_byte air 18 row)) +
      (1 - is_padding_byte air 19 row)) +
      (1 - is_padding_byte air 20 row)) +
      (1 - is_padding_byte air 21 row)) +
      (1 - is_padding_byte air 22 row)) +
      (1 - is_padding_byte air 23 row)) +
      (1 - is_padding_byte air 24 row)) +
      (1 - is_padding_byte air 25 row)) +
      (1 - is_padding_byte air 26 row)) +
      (1 - is_padding_byte air 27 row)) +
      (1 - is_padding_byte air 28 row)) +
      (1 - is_padding_byte air 29 row)) +
      (1 - is_padding_byte air 30 row)) +
      (1 - is_padding_byte air 31 row)) +
      (1 - is_padding_byte air 32 row)) +
      (1 - is_padding_byte air 33 row)) * 4 := by
  have h_rows := rows_of_allHold_simplified h
  have hlen := rcl_length air row
  have hc := forall_list_get h_rows (show (35 : ℕ) < _ by rw [hlen]; omega)
  change constraint_35 air row at hc
  unfold constraint_35 at hc
  exact (eq_of_enabled_mul_sub hc h_en).symm

/-! ## Constraints 36–71: Padding monotonicity (enabled-gated) -/

-- (pad[j+1] - pad[j]) * (pad[j+1] - pad[j] - 1) = 0 when enabled
set_option maxHeartbeats 6400000 in
set_option maxRecDepth 4096 in
lemma padding_monotone_step
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1)
    (j : ℕ) (hj : j < 33) :
    (is_padding_byte air (j + 1) row - is_padding_byte air j row) *
    ((is_padding_byte air (j + 1) row - is_padding_byte air j row) - 1) = 0 := by
  have h_rows := rows_of_allHold_simplified h
  have hlen := rcl_length air row
  have hidx : j + 36 < (row_constraint_list air row).length := by rw [hlen]; omega
  have hc := forall_list_get h_rows hidx
  revert hc
  interval_cases j <;> (intro hc; exact eq_zero_of_enabled_mul hc h_en)

/-! ## Derived: padding contiguity and active prefix -/

/-- Padding flags are contiguous: once padding starts, all subsequent words are padded. -/
lemma padding_contiguous
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1)
    (j k : ℕ) (hjk : j ≤ k) (hk : k < 34)
    (h_pad : is_padding_byte air j row = 1) :
    is_padding_byte air k row = 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  induction d with
  | zero => simpa using h_pad
  | succ d ih =>
    have h_prev : is_padding_byte air (j + d) row = 1 := ih (by omega) (by omega)
    have h_step := padding_monotone_step h h_en (j + d) (by omega)
    rw [h_prev] at h_step
    -- h_step : (pad[j+d+1] - 1) * ((pad[j+d+1] - 1) - 1) = 0
    have h_bin := padding_byte_binary h (j + d + 1) (by omega)
    rcases h_bin with h0 | h1
    · -- pad[j+d+1] = 0 → contradiction
      rw [h0] at h_step
      -- h_step : ((0:FBB) - 1) * (((0:FBB) - 1) - 1) = 0, false in FBB
      exact absurd h_step (by decide)
    · exact h1

-- Active region is a prefix
lemma active_prefix
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1)
    (j k : ℕ) (hkj : k ≤ j) (hj : j < 34)
    (h_active : is_padding_byte air j row = 0) :
    is_padding_byte air k row = 0 := by
  by_contra h_ne
  have h_bin := padding_byte_binary h k (by omega)
  rcases h_bin with h0 | h1
  · exact h_ne h0
  · -- pad[k] = 1 → by contiguity, pad[j] = 1, contradicting pad[j] = 0
    have := padding_contiguous h h_en k j hkj hj h1
    rw [h_active] at this
    exact absurd this (by decide : (0 : FBB) ≠ 1)

/-! ## Cumulative pad sum for active prefix -/

-- For an active prefix of length j, cumulativePadSum(j) = (j : FBB)
lemma cumulative_pad_sum_for_active_prefix
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ}
    (j : ℕ) (hj : j ≤ 34)
    (h_active : ∀ k, k < j → is_padding_byte air k row = 0) :
    cumulativePadSum air row j = (j : FBB) := by
  induction j with
  | zero => simp [cumulativePadSum]
  | succ n ih =>
    rw [cumulativePadSum]
    have h_pn := h_active n (by omega)
    rw [h_pn, sub_zero]
    rw [ih (by omega) (fun k hk => h_active k (by omega))]
    push_cast
    ring

/-! ## cumulativePadSum ↔ activeWords bridge -/

-- cumulativePadSum(34) unrolls to the same 34-fold sum as constraint 35.
-- This is purely definitional (unfold the recursive definition 34 times).
lemma cumulativePadSum_34_eq_unrolled_sum
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} :
    cumulativePadSum air row 34 =
      ((((((((((((((((((((((((((((((((
      (1 - is_padding_byte air 0 row) +
      (1 - is_padding_byte air 1 row)) +
      (1 - is_padding_byte air 2 row)) +
      (1 - is_padding_byte air 3 row)) +
      (1 - is_padding_byte air 4 row)) +
      (1 - is_padding_byte air 5 row)) +
      (1 - is_padding_byte air 6 row)) +
      (1 - is_padding_byte air 7 row)) +
      (1 - is_padding_byte air 8 row)) +
      (1 - is_padding_byte air 9 row)) +
      (1 - is_padding_byte air 10 row)) +
      (1 - is_padding_byte air 11 row)) +
      (1 - is_padding_byte air 12 row)) +
      (1 - is_padding_byte air 13 row)) +
      (1 - is_padding_byte air 14 row)) +
      (1 - is_padding_byte air 15 row)) +
      (1 - is_padding_byte air 16 row)) +
      (1 - is_padding_byte air 17 row)) +
      (1 - is_padding_byte air 18 row)) +
      (1 - is_padding_byte air 19 row)) +
      (1 - is_padding_byte air 20 row)) +
      (1 - is_padding_byte air 21 row)) +
      (1 - is_padding_byte air 22 row)) +
      (1 - is_padding_byte air 23 row)) +
      (1 - is_padding_byte air 24 row)) +
      (1 - is_padding_byte air 25 row)) +
      (1 - is_padding_byte air 26 row)) +
      (1 - is_padding_byte air 27 row)) +
      (1 - is_padding_byte air 28 row)) +
      (1 - is_padding_byte air 29 row)) +
      (1 - is_padding_byte air 30 row)) +
      (1 - is_padding_byte air 31 row)) +
      (1 - is_padding_byte air 32 row)) +
      (1 - is_padding_byte air 33 row) := by
  simp only [cumulativePadSum, zero_add]

-- The key bridge: xorin_len = cumulativePadSum(34) * 4 at FBB level.
-- Combines constraint 35 with the unrolled sum identity.
lemma xorin_len_eq_cumulativePadSum_mul_four
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1) :
    xorin_len air row = cumulativePadSum air row 34 * 4 := by
  rw [cumulativePadSum_34_eq_unrolled_sum]
  exact xorin_len_eq_four_mul_active_count h h_en

/-! ## FBB overflow bounds -/

-- Helper: (1 - pad[n]).val is 0 or 1
lemma one_sub_pad_val_le
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (n : ℕ) (hn : n < 34) :
    (1 - is_padding_byte air n row).val ≤ 1 := by
  have h_bin := padding_byte_binary h n hn
  rcases h_bin with h0 | h1
  · rw [h0, sub_zero]; norm_num
  · rw [h1, sub_self]; simp

-- Helper: cumulativePadSum(n).val ≤ n
lemma cPS_val_le
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (n : ℕ) (hn : n ≤ 34) :
    (cumulativePadSum air row n).val ≤ n := by
  induction n with
  | zero => simp [cumulativePadSum]
  | succ m ih =>
    have h_ih := ih (by omega)
    have h_term := one_sub_pad_val_le h m (by omega)
    show (cumulativePadSum air row m + (1 - is_padding_byte air m row)).val ≤ m + 1
    have h_small : (cumulativePadSum air row m).val +
        (1 - is_padding_byte air m row).val < 2013265921 := by omega
    rw [fbb_val_add h_small]
    omega

-- Helper: cPS is monotone at .val level
lemma cPS_val_monotone
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (m n : ℕ) (hmn : m ≤ n) (hn : n ≤ 34) :
    (cumulativePadSum air row m).val ≤ (cumulativePadSum air row n).val := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    show _ ≤ (cumulativePadSum air row (m + d) +
        (1 - is_padding_byte air (m + d) row)).val
    have h_le := cPS_val_le h (m + d) (by omega)
    have h_term := one_sub_pad_val_le h (m + d) (by omega)
    have h_small : (cumulativePadSum air row (m + d)).val +
        (1 - is_padding_byte air (m + d) row).val < 2013265921 := by omega
    rw [fbb_val_add h_small]
    omega

-- xorin_len ≤ 136 when enabled
lemma xorin_len_le_max
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1) :
    (xorin_len air row).val ≤ 136 := by
  have h_eq := xorin_len_eq_cumulativePadSum_mul_four h h_en
  have h_le := cPS_val_le h 34 (le_refl _)
  -- xorin_len = cPS(34) * 4 at FBB level
  -- cPS(34).val ≤ 34, so cPS(34).val * 4 ≤ 136 < p
  have h_small : (cumulativePadSum air row 34).val * (4 : FBB).val < 2013265921 := by
    have : (4 : FBB).val = 4 := by decide
    rw [this]; omega
  rw [h_eq, fbb_val_mul h_small]
  have : (4 : FBB).val = 4 := by decide
  rw [this]; omega

/-- The number of active (non-padding) words is at most 34. -/
lemma activeWords_le_34
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1) :
    activeWords air row ≤ 34 :=
  num_active_words_le _ (xorin_len_le_max h h_en)

-- The master bridge: cumulativePadSum(34).val = activeWords at ℕ level.
lemma cumulativePadSum_34_val_eq_activeWords
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1) :
    (cumulativePadSum air row 34).val = activeWords air row := by
  have h_eq := xorin_len_eq_cumulativePadSum_mul_four h h_en
  have h_le := cPS_val_le h 34 (le_refl _)
  -- xorin_len.val = cPS(34).val * 4 (no overflow since cPS(34).val ≤ 34)
  have h4 : (4 : FBB).val = 4 := by decide
  have h_mul_small : (cumulativePadSum air row 34).val * (4 : FBB).val < 2013265921 := by
    rw [h4]; omega
  have h_val : (xorin_len air row).val = (cumulativePadSum air row 34).val * 4 := by
    conv_lhs => rw [h_eq]
    rw [fbb_val_mul h_mul_small, h4]
  -- activeWords = xorin_len.val / 4 = (cPS(34).val * 4) / 4 = cPS(34).val
  unfold activeWords num_active_words
  rw [h_val]
  omega

/-- The XORIN length is divisible by 4 (aligned to word boundaries). -/
lemma xorin_len_mod_four
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1) :
    (xorin_len air row).val % 4 = 0 := by
  have h_eq := xorin_len_eq_cumulativePadSum_mul_four h h_en
  have h_cps_val := cumulativePadSum_34_val_eq_activeWords h h_en
  have h_aw_le := activeWords_le_34 h h_en
  have h4 : (4 : FBB).val = 4 := by decide
  have h_le := cPS_val_le h 34 (le_refl _)
  have h_mul_small : (cumulativePadSum air row 34).val * (4 : FBB).val < 2013265921 := by
    rw [h4]; omega
  have h_val : (xorin_len air row).val = (cumulativePadSum air row 34).val * 4 := by
    conv_lhs => rw [h_eq]
    rw [fbb_val_mul h_mul_small, h4]
  rw [h_val, Nat.mul_comm]
  exact Nat.mul_mod_right _ _

/-! ## Active-word / padding relationships -/

-- Padding byte is 0 iff the word index is active
lemma active_word_iff_not_padding
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1)
    (j : ℕ) (hj : j < 34) :
    is_padding_byte air j row = 0 ↔ j < activeWords air row := by
  constructor
  · -- Forward: pad[j]=0 → j < activeWords
    intro h_active
    -- All k ≤ j have pad[k] = 0
    have h_prefix : ∀ k, k < j + 1 → is_padding_byte air k row = 0 := by
      intro k hk
      exact active_prefix h h_en j k (by omega) hj h_active
    -- cPS(j+1) = ((j+1) : FBB)
    have h_cps := cumulative_pad_sum_for_active_prefix (j + 1) (by omega) h_prefix
    -- cPS(j+1).val = j + 1
    have h_cast : ((j + 1 : ℕ) : FBB).val = j + 1 := fbb_val_natCast (by omega)
    have h_cps_val : (cumulativePadSum air row (j + 1)).val = j + 1 := by
      rw [h_cps, h_cast]
    -- cPS(j+1).val ≤ cPS(34).val (monotonicity)
    have h_mono := cPS_val_monotone h (j + 1) 34 (by omega) (le_refl _)
    -- cPS(34).val = activeWords
    have h_aw := cumulativePadSum_34_val_eq_activeWords h h_en
    omega
  · -- Backward: j < activeWords → pad[j]=0
    intro hj_lt
    by_contra h_ne
    have h_bin := padding_byte_binary h j hj
    rcases h_bin with h0 | h1
    · exact absurd h0 h_ne
    · -- pad[j] = 1. By contiguity, all k ≥ j with k < 34 have pad[k] = 1.
      -- So cPS(34) = cPS(j) (terms j..33 contribute 0 each).
      -- cPS(j).val ≤ j (from cPS_val_le).
      -- So activeWords = cPS(34).val ≤ j, contradicting j < activeWords.
      have h_all_pad : ∀ k, j ≤ k → k < 34 → is_padding_byte air k row = 1 :=
        fun k hjk hk => padding_contiguous h h_en j k hjk hk h1
      -- cPS(34) = cPS(j) + sum of (1-pad[k]) for k=j..33
      -- Each term is 0 since pad[k] = 1
      -- So cPS(34).val = cPS(j).val
      have h_cps_tail : ∀ d, j + d ≤ 34 →
          cumulativePadSum air row (j + d) = cumulativePadSum air row j := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
          intro hd
          show cumulativePadSum air row (j + d) +
              (1 - is_padding_byte air (j + d) row) = _
          have h_pad_jd := h_all_pad (j + d) (by omega) (by omega)
          rw [h_pad_jd, sub_self, add_zero]
          exact ih (by omega)
      have h_cps_eq : cumulativePadSum air row 34 = cumulativePadSum air row j := by
        have := h_cps_tail (34 - j) (by omega)
        rwa [show j + (34 - j) = 34 from by omega] at this
      have h_aw := cumulativePadSum_34_val_eq_activeWords h h_en
      have h_le := cPS_val_le h j (by omega)
      rw [h_cps_eq] at h_aw
      omega

-- Padding byte is 1 iff the word index is inactive
lemma inactive_word_iff_padding
    {air : Valid_XorinVmAir FBB ExtF} {row : ℕ} {h_row : row ≤ air.last_row}
    (h : allHold_simplified air row h_row)
    (h_en : is_enabled air row = 1)
    (j : ℕ) (hj : j < 34) :
    is_padding_byte air j row = 1 ↔ j ≥ activeWords air row := by
  have h_iff := active_word_iff_not_padding h h_en j hj
  have h_bin := padding_byte_binary h j hj
  constructor
  · intro h1
    by_contra h_lt
    push_neg at h_lt
    have h0 := h_iff.mpr h_lt
    rw [h0] at h1
    exact absurd h1 (by decide : (0 : FBB) ≠ 1)
  · intro h_ge
    rcases h_bin with h0 | h1
    · have := h_iff.mp h0
      omega
    · exact h1

end XorinVmAir.Soundness
