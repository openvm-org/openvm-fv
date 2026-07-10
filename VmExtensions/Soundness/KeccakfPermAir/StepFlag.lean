/-
  Global step-flag alignment for KeccakfPermAir.

  Proves that for every row in the trace, exactly one of the 24 step flags
  is active (equals 1) and it matches `row % 24`. This is the single global
  induction that covers all rows, including block starts beyond block 0.

  Dependencies: control_step_init_constraint (seg_A) and
  transition_step_rotation_constraint (seg_B) from RowProperties.lean,
  plus rotation_consistent from KeccakfPermAir.lean (isValid).
-/
import VmExtensions.Soundness.KeccakfPermAir.RowProperties

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfPermAir.Soundness

open KeccakfPermAir.constraints
open BabyBear

variable {ExtF : Type} [Field ExtF]

/-! ## Bridge Lemmas -/

-- Rotation consistency bridge: step_flag_next at row r equals step_flag at row r+1.
-- Uses the rotation_consistent clause added to Valid_KeccakfPermAir.isValid.
private lemma step_flag_next_eq
    {air : Valid_KeccakfPermAir FBB ExtF}
    {i row : ℕ} (h : row < air.last_row) :
    step_flag_next air i row = step_flag air i (row + 1) :=
  air.rotation_consistent h

-- isFirstRow returns 1 at row 0.
omit [Field ExtF] in
private lemma isFirstRow_zero (air : Valid_KeccakfPermAir FBB ExtF) :
    Circuit.isFirstRow air (0 : ℕ) = (1 : FBB) := by
  show (if (0 : ℕ) = 0 then (1 : FBB) else 0) = 1
  exact if_pos rfl

-- isTransitionRow returns 1 when row < last_row.
private lemma isTransitionRow_of_lt
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : row < air.last_row) :
    Circuit.isTransitionRow air row = (1 : FBB) := by
  show (if row = air.last_row then (0 : FBB) else 1) = 1
  exact if_neg (by omega)

/-! ## Main Theorem -/

-- Global step-flag alignment: at every row, exactly one step flag is active
-- and it matches `row % 24`.
--
-- Proof by simple induction on row. Base case uses control_step_init_constraint
-- (seg_A, isFirstRow = 1 at row 0). Inductive step uses
-- transition_step_rotation_constraint (seg_B, isTransitionRow = 1 at row < last_row)
-- plus the rotation consistency bridge.
theorem step_flag_globally_aligned
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row) :
    ∀ row, row ≤ air.last_row →
      step_flag air (row % 24) row = 1 ∧
      ∀ j, j < 24 → j ≠ row % 24 → step_flag air j row = 0 := by
  intro row
  induction row with
  | zero =>
    intro h_row
    simp only [Nat.zero_mod]
    have h0 := h_allHold 0 h_row
    constructor
    · -- step_flag 0 0 = 1: control_step_init at j=0, isFirstRow=1
      have hc := control_step_init_constraint h0 0 (by omega)
      simp only [ite_true] at hc
      rw [isFirstRow_zero, one_mul] at hc
      exact sub_eq_zero.mp hc
    · -- step_flag j 0 = 0 for j ≠ 0: control_step_init at j>0, isFirstRow=1
      intro j hj hne
      have hc := control_step_init_constraint h0 j hj
      rw [if_neg hne, isFirstRow_zero, one_mul] at hc
      exact hc
  | succ n ih =>
    intro h_row
    have hn_lt : n < air.last_row := by omega
    have ih_n := ih (by omega : n ≤ air.last_row)
    have hn := h_allHold n (by omega : n ≤ air.last_row)
    have h_trans := isTransitionRow_of_lt hn_lt
    -- Transition constraint at row n gives:
    -- step_flag((j+1)%24, n+1) = step_flag(j, n) for all j < 24
    have h_shift : ∀ j, j < 24 →
        step_flag air ((j + 1) % 24) (n + 1) = step_flag air j n := by
      intro j hj
      have hc := transition_step_rotation_constraint hn j hj
      rw [h_trans, one_mul] at hc
      rw [← step_flag_next_eq hn_lt]
      exact (sub_eq_zero.mp hc).symm
    constructor
    · -- step_flag ((n+1)%24) (n+1) = 1
      -- Key: (n%24+1)%24 = (n+1)%24, so h_shift at j=n%24 gives the result
      have h1 := h_shift (n % 24) (Nat.mod_lt n (by omega))
      have h_mod : (n % 24 + 1) % 24 = (n + 1) % 24 := by omega
      rw [h_mod] at h1
      rw [h1]
      exact ih_n.1
    · -- step_flag k (n+1) = 0 for k ≠ (n+1)%24
      -- For each k, use j=(k+23)%24 so (j+1)%24=k, then IH gives the zero
      intro k hk hne
      have hj_lt : (k + 23) % 24 < 24 := Nat.mod_lt _ (by omega)
      have hj_succ : ((k + 23) % 24 + 1) % 24 = k := by omega
      have hj_ne : (k + 23) % 24 ≠ n % 24 := by
        intro heq
        apply hne
        have : ((k + 23) % 24 + 1) % 24 = (n % 24 + 1) % 24 := by omega
        rw [hj_succ] at this
        omega
      have h1 := h_shift ((k + 23) % 24) hj_lt
      rw [hj_succ] at h1
      rw [h1]
      exact ih_n.2 _ hj_lt hj_ne

/-! ## Row-Indexed Step-Flag One-Hotness -/

-- Row-indexed step-flag one-hotness: within a 24-aligned block starting at
-- startRow, offset k is the unique active step flag at startRow + k.
-- Generalizes step_flag_one_hot from block-indexed to row-indexed.
theorem step_flag_one_hot_row
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    {startRow exportRow : ℕ}
    (h_layout : BlockLayoutFacts startRow exportRow air.last_row)
    (k : ℕ) (hk : k < 24) :
    step_flag air k (startRow + k) = 1 ∧
    ∀ j, j < 24 → j ≠ k →
      step_flag air j (startRow + k) = 0 := by
  have h_bound : startRow + k ≤ air.last_row := by
    have := h_layout.export_row_eq
    have := h_layout.export_row_le_last
    simp only [EXPORT_ROW_OFFSET, BLOCK_ROWS] at *
    omega
  have h_mod : (startRow + k) % 24 = k := by
    have h_aligned := h_layout.start_row_aligned
    simp only [BLOCK_ROWS] at h_aligned
    omega
  have h_global := step_flag_globally_aligned h_allHold _ h_bound
  rw [h_mod] at h_global
  exact h_global

theorem step_flag_one_hot
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    {block : ℕ}
    (h_layout : BlockLayoutFacts (air.blockStartRow block)
        (air.blockExportRow block) air.last_row)
    (k : ℕ) (hk : k < 24) :
    step_flag air k (air.blockStartRow block + k) = 1 ∧
    ∀ j, j < 24 → j ≠ k →
      step_flag air j (air.blockStartRow block + k) = 0 :=
  step_flag_one_hot_row h_allHold h_layout k hk

-- From constraint_249: (1 - step_flag 23) * export_flag = 0.
-- With export_flag = 1: step_flag 23 = 1.
lemma ef_implies_step_flag_23
    {air : Valid_KeccakfPermAir FBB ExtF}
    {row : ℕ}
    (h : allHold_simplified air row)
    (h_ef : export_flag air row = 1) :
    step_flag air 23 row = 1 := by
  -- Extract constraint_249 from allHold_simplified
  have h_rot0 := forall_rot0_of_forall_row air row h.2
  simp only [rot0_constraint_list, List.forall_append] at h_rot0
  -- constraint_249 is the second element of seg_E
  have h249 : constraint_249 air row := h_rot0.1.2.2.1
  -- constraint_249: (1 - step_flag 23 row) * export_flag row = 0
  simp only [constraint_249] at h249
  rw [h_ef, mul_one] at h249
  exact (sub_eq_zero.mp h249).symm

-- From step_flag_globally_aligned: if step_flag 23 row = 1 and row ≤ last_row,
-- then row % 24 = 23.
lemma step_flag_23_implies_alignment
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    {row : ℕ} (h_row : row ≤ air.last_row)
    (h_sf23 : step_flag air 23 row = 1) :
    row % 24 = 23 := by
  by_contra h_ne
  have h_aligned := step_flag_globally_aligned h_allHold row h_row
  have h_zero := h_aligned.2 23 (by omega) (Ne.symm h_ne)
  rw [h_zero] at h_sf23
  exact zero_ne_one h_sf23

-- From ef=1, derive BlockLayoutFacts for the block ending at this row.
lemma ef_implies_layout
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    {row : ℕ} (h_row : row ≤ air.last_row)
    (h_ef : export_flag air row = 1) :
    BlockLayoutFacts (row - 23) row air.last_row := by
  have h_sf23 := ef_implies_step_flag_23 (h_allHold row h_row) h_ef
  have h_mod := step_flag_23_implies_alignment h_allHold h_row h_sf23
  exact {
    start_row_aligned := by simp only [BLOCK_ROWS]; omega
    export_row_eq := by simp only [EXPORT_ROW_OFFSET, BLOCK_ROWS]; omega
    export_row_le_last := h_row
  }

end KeccakfPermAir.Soundness
