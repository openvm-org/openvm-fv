/-
  Preimage persistence across a 24-row block.

  Proves that preimage columns are constant across all 24 rows of a block,
  equaling the `a` columns at the block start. Uses preimage_init_constraint
  (seg_C) for the base case and preimage_consistency_constraint (seg_D) for
  the inductive step, gated by step_flag_one_hot from StepFlag.lean.

  Dependencies: StepFlag.lean (step_flag_one_hot), RowProperties.lean
  (preimage_init_constraint, preimage_consistency_constraint),
  KeccakfPermAir.lean (rotation_consistent, BlockLayoutFacts).
-/
import VmExtensions.Soundness.KeccakfPermAir.StepFlag

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfPermAir.Soundness

open KeccakfPermAir.constraints
open BabyBear

variable {ExtF : Type} [Field ExtF]

/-! ## Bridge Lemmas -/

-- Rotation consistency bridge: preimage_next at row r equals preimage at row r+1.
private lemma preimage_next_eq
    {air : Valid_KeccakfPermAir FBB ExtF}
    {i row : ℕ} (h : row < air.last_row) :
    preimage_next air i row = preimage air i (row + 1) :=
  air.rotation_consistent h

-- isTransitionRow returns 1 when row < last_row.
private lemma isTransitionRow_of_lt'
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : row < air.last_row) :
    Circuit.isTransitionRow air row = (1 : FBB) := by
  show (if row = air.last_row then (0 : FBB) else 1) = 1
  exact if_neg (by omega)

/-! ## Row-Indexed Preimage Persistence -/

-- Row-indexed preimage persistence: within a 24-aligned block starting at startRow,
-- preimage(i, r) = a(i, startRow) for all rows r in the block.
-- Generalizes preimage_persists from block-indexed to row-indexed.
theorem preimage_persists_row
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    {startRow exportRow : ℕ}
    (h_layout : BlockLayoutFacts startRow exportRow air.last_row)
    {i : ℕ} (hi : i < 100) :
    ∀ r, startRow ≤ r → r ≤ startRow + 23 →
      preimage air i r = a air i startRow := by
  suffices h : ∀ d, d ≤ 23 →
      preimage air i (startRow + d) = a air i startRow by
    intro r hr_lo hr_hi
    have ⟨d, hd_eq⟩ : ∃ d, r = startRow + d := ⟨r - startRow, by omega⟩
    rw [hd_eq]
    exact h d (by omega)
  intro d
  induction d with
  | zero =>
    intro _
    simp only [Nat.add_zero]
    have h_row_le : startRow ≤ air.last_row := by
      have := h_layout.export_row_eq
      have := h_layout.export_row_le_last
      simp only [EXPORT_ROW_OFFSET, BLOCK_ROWS] at *
      omega
    have h_ah := h_allHold _ h_row_le
    have h_sf := step_flag_one_hot_row h_allHold h_layout 0 (by omega)
    have h_init := preimage_init_constraint h_ah i hi
    simp only [Nat.add_zero] at h_sf
    rw [h_sf.1, one_mul] at h_init
    exact sub_eq_zero.mp h_init
  | succ n ih =>
    intro hd
    have hn_le : n ≤ 23 := by omega
    have ih_n := ih hn_le
    have h_row_bound : startRow + n ≤ air.last_row := by
      have := h_layout.export_row_eq
      have := h_layout.export_row_le_last
      simp only [EXPORT_ROW_OFFSET, BLOCK_ROWS] at *
      omega
    have h_row_lt : startRow + n < air.last_row := by
      have := h_layout.export_row_eq
      have := h_layout.export_row_le_last
      simp only [EXPORT_ROW_OFFSET, BLOCK_ROWS] at *
      omega
    have h_ah := h_allHold _ h_row_bound
    have h_sf23 : step_flag air 23 (startRow + n) = 0 := by
      have h_sf := step_flag_one_hot_row h_allHold h_layout n (by omega)
      exact h_sf.2 23 (by omega) (by omega)
    have h_cons := preimage_consistency_constraint h_ah i hi
    rw [h_sf23, sub_zero, one_mul] at h_cons
    rw [isTransitionRow_of_lt' h_row_lt, one_mul] at h_cons
    have h_eq : preimage air i (startRow + n) =
        preimage_next air i (startRow + n) :=
      sub_eq_zero.mp h_cons
    rw [preimage_next_eq h_row_lt] at h_eq
    show preimage air i (startRow + (n + 1)) = a air i startRow
    rw [show startRow + (n + 1) = startRow + n + 1 from by omega]
    rw [← h_eq, ih_n]

/-! ## Block-Indexed Wrapper -/

-- Block-indexed preimage persistence: thin wrapper over preimage_persists_row.
theorem preimage_persists
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    {block : ℕ}
    (h_layout : BlockLayoutFacts (air.blockStartRow block)
        (air.blockExportRow block) air.last_row)
    {i : ℕ} (hi : i < 100) :
    ∀ r, air.blockStartRow block ≤ r → r ≤ air.blockStartRow block + 23 →
      preimage air i r = a air i (air.blockStartRow block) :=
  preimage_persists_row h_allHold h_layout hi

end KeccakfPermAir.Soundness
