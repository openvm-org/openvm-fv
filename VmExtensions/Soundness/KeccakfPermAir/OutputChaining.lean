/-
  Output-to-input chaining.

  Proves that on transition rows where step_flag 23 = 0, the next row's input
  state equals the current row's output state. This is the row-local glue
  between successive rounds in the 24-round block composition.

  Dependencies: RowProperties.lean (output_chaining_constraint, output_col),
  Round/Surface.lean (rowInputState, rowOutputState, laneOfLimbs),
  KeccakfPermAir.lean (rotation_consistent).
-/
import VmExtensions.Soundness.KeccakfPermAir.RowProperties
import VmExtensions.Soundness.KeccakfPermAir.Round.Surface

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfPermAir.Soundness

open KeccakfPermAir.constraints
open BabyBear

variable {ExtF : Type} [Field ExtF]

/-! ## Bridge Lemmas -/

-- Rotation bridge: a_next at row r equals a at row r+1.
private lemma a_next_eq
    {air : Valid_KeccakfPermAir FBB ExtF}
    {i row : ℕ} (h : row < air.last_row) :
    a_next air i row = a air i (row + 1) :=
  air.rotation_consistent h

-- isTransitionRow returns 1 when row < last_row.
private lemma isTransitionRow_of_lt
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : row < air.last_row) :
    Circuit.isTransitionRow air row = (1 : FBB) := by
  show (if row = air.last_row then (0 : FBB) else 1) = 1
  exact if_neg (by omega)

/-! ## Per-Limb Bridge -/

-- When row < last_row and step_flag 23 = 0, the output column at each limb
-- index equals the `a` column at the next row. This is the core extraction
-- from the output-chaining constraint family (seg_F, 100 constraints).
private lemma output_col_eq_a_succ
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_allHold : allHold_simplified air row)
    (h_row_lt : row < air.last_row)
    (h_sf23 : step_flag air 23 row = 0)
    {i : ℕ} (hi : i < 100) :
    output_col air i row = a air i (row + 1) := by
  have h_cc := output_chaining_constraint h_allHold i hi
  rw [isTransitionRow_of_lt h_row_lt, one_mul, h_sf23, sub_zero, one_mul,
      sub_eq_zero] at h_cc
  rw [h_cc, a_next_eq h_row_lt]

/-! ## Main Theorem -/

-- Output-to-input chaining: on transition rows where step_flag 23 = 0, the next
-- row's input state equals the current row's output state. This is the per-row
-- glue in the 24-round block composition chain.
--
-- Proof: extract 100 per-limb equalities from the output-chaining constraint family,
-- split into a_ppp_00_limb (limbs 0-3, lane [0][0]) and a_prime_prime (limbs 4-99),
-- then assemble into State equality via Subtype.ext + Array.ext.
theorem output_chains_to_input
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_allHold : allHold_simplified air row)
    (h_row_lt : row < air.last_row)
    (h_not_last_step : step_flag air 23 row = 0) :
    rowInputState air (row + 1) = rowOutputState air row := by
  -- Per-limb bridge: output_col air i row = a air i (row + 1) for all i < 100
  have h_limb : ∀ i, i < 100 → output_col air i row = a air i (row + 1) :=
    fun i hi => output_col_eq_a_succ h_allHold h_row_lt h_not_last_step hi
  -- Specialize to a_ppp_00_limb (limbs 0-3, lane [0][0])
  have h_ppp : ∀ j, j < 4 → a_ppp_00_limb air j row = a air j (row + 1) := by
    intro j hj
    have := h_limb j (by omega)
    simp only [output_col, if_pos hj] at this
    exact this
  -- Specialize to a_prime_prime (limbs 4-99, lanes 1-24)
  have h_app : ∀ j, 4 ≤ j → j < 100 → a_prime_prime air j row = a air j (row + 1) := by
    intro j hlo hhi
    have := h_limb j hhi
    simp only [output_col, if_neg (by omega : ¬(j < 4))] at this
    exact this
  -- State equality via Subtype.ext + Array.ext on the 25 lanes
  apply Subtype.ext
  apply Array.ext
  · simp [rowInputState, rowOutputState]
  · intro i hi₁ hi₂
    simp only [rowInputState, rowOutputState, Array.getElem_ofFn] at *
    by_cases hi : i = 0
    · -- Lane [0][0]: from a_ppp_00_limb columns
      subst hi
      simp only [↓reduceIte]
      rw [h_ppp 0 (by omega), h_ppp 1 (by omega), h_ppp 2 (by omega), h_ppp 3 (by omega)]
    · -- Lanes 1-24: from a_prime_prime columns
      rw [if_neg hi]
      have hi25 : i < 25 := by simp [rowInputState] at hi₁; exact hi₁
      rw [h_app (4 * i) (by omega) (by omega),
          h_app (4 * i + 1) (by omega) (by omega),
          h_app (4 * i + 2) (by omega) (by omega),
          h_app (4 * i + 3) (by omega) (by omega)]

end KeccakfPermAir.Soundness
