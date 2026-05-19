/-
  24-round block composition.

  Proves that composing 24 applications of single_round_correctness with
  output-to-input chaining yields rowOutputState(start+23) = keccakP(rowInputState(start)).

  Dependencies: StepFlag.lean (step_flag_one_hot), OutputChaining.lean
  (output_chains_to_input), RowProperties.lean (roundLocalConstraints_of_allHold_simplified),
  Round/SingleRound.lean (single_round_correctness), Keccak/Spec/Basic.lean (keccakP).
-/
import VmExtensions.Soundness.KeccakfPermAir.StepFlag
import VmExtensions.Soundness.KeccakfPermAir.OutputChaining
import VmExtensions.Soundness.KeccakfPermAir.Round.SingleRound

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints
open Keccak

variable {ExtF : Type} [Field ExtF]

/-! ## keccakP Loop Unfolding -/

-- roundConstants.size = 24
private lemma rc_size : roundConstants.size = 24 := by rfl

-- Partial Keccak permutation: applies rounds 0..n-1 in order.
noncomputable def keccakRounds : (n : Nat) → (hn : n ≤ 24) → State → State
  | 0, _, A => A
  | n + 1, hn, A =>
    keccakRounds n (by omega) A |> θ |> ρπ |> χ |> (ι · n (by rw [rc_size]; omega))

-- keccakP equals keccakRounds 24.
-- Proof: expand the for-loop via cons/nil, then unfold keccakP.match_1
-- (the And.casesOn from membership proof destructuring) and reduce via
-- And.rec_val + proof irrelevance so that rfl closes the goal.
@[simp] private lemma id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl
@[simp] private lemma id_bind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

-- And.rec on an opaque proof reduces to applying the continuation to projections.
@[simp] private theorem and_rec_val {P Q : Prop} {α : Sort _} (f : P → Q → α) (p : P ∧ Q) :
    And.rec f p = f p.1 p.2 := by cases p; rfl

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 65536 in
private theorem keccakP_eq_keccakRounds (A : State) :
    keccakP A = keccakRounds 24 (by omega) A := by
  simp only [keccakP, keccakRounds, Id.run, roundConstants,
    Std.Range.forIn'_eq_forIn'_range', Std.Range.size]
  norm_num
  simp only [List.range'_succ, List.range'_zero,
    List.forIn'_cons, List.forIn'_nil, id_pure, id_bind]
  unfold keccakP.match_1
  simp only [and_rec_val]

/-! ## Row-Indexed Composition Chain -/

-- Row-indexed core inductive lemma: after k+1 rounds starting at startRow,
-- the output state matches keccakRounds (k+1) applied to the initial input state.
-- Generalizes block_chain from block-indexed to row-indexed.
private theorem row_chain
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    {startRow exportRow : ℕ}
    (h_layout : BlockLayoutFacts startRow exportRow air.last_row)
    (k : Nat) (hk : k < 24) :
    rowOutputState air (startRow + k) =
      keccakRounds (k + 1) (by omega) (rowInputState air startRow) := by
  induction k with
  | zero =>
    simp only [keccakRounds]
    have h_bound : startRow + 0 ≤ air.last_row := by
      have := h_layout.export_row_eq; have := h_layout.export_row_le_last
      simp only [EXPORT_ROW_OFFSET, BLOCK_ROWS] at *; omega
    have h_ah := h_allHold _ h_bound
    have h_step := step_flag_one_hot_row h_allHold h_layout 0 (by omega)
    have h_rlc := roundLocalConstraints_of_allHold_simplified h_ah
    exact single_round_correctness (round := ⟨0, by omega⟩) h_rlc h_step
  | succ k ih =>
    have h_bound_k : startRow + k ≤ air.last_row := by
      have := h_layout.export_row_eq; have := h_layout.export_row_le_last
      simp only [EXPORT_ROW_OFFSET, BLOCK_ROWS] at *; omega
    have h_bound_sk : startRow + (k + 1) ≤ air.last_row := by
      have := h_layout.export_row_eq; have := h_layout.export_row_le_last
      simp only [EXPORT_ROW_OFFSET, BLOCK_ROWS] at *; omega
    have h_row_lt : startRow + k < air.last_row := by omega
    have h_step_k := step_flag_one_hot_row h_allHold h_layout k (by omega)
    have h_sf23_zero : step_flag air 23 (startRow + k) = 0 :=
      h_step_k.2 23 (by omega) (by omega)
    have h_chain := output_chains_to_input
      (h_allHold _ h_bound_k) h_row_lt h_sf23_zero
    have h_ah_sk := h_allHold _ h_bound_sk
    have h_step_sk := step_flag_one_hot_row h_allHold h_layout (k + 1) hk
    have h_rlc_sk := roundLocalConstraints_of_allHold_simplified h_ah_sk
    have h_ih := ih (by omega)
    rw [show startRow + (k + 1) = startRow + k + 1 from by omega]
      at h_ah_sk h_step_sk h_rlc_sk ⊢
    rw [single_round_correctness (round := ⟨k + 1, by omega⟩) h_rlc_sk h_step_sk]
    rw [h_chain, h_ih]
    rfl

-- Row-indexed 24-round composition: the output state at startRow + 23 equals
-- keccakP applied to the input state at startRow.
theorem rounds_24_row
    {air : Valid_KeccakfPermAir FBB ExtF}
    {startRow exportRow : ℕ}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    (h_layout : BlockLayoutFacts startRow exportRow air.last_row) :
    rowOutputState air (startRow + 23) =
      keccakP (rowInputState air startRow) := by
  rw [keccakP_eq_keccakRounds]
  exact row_chain h_allHold h_layout 23 (by omega)

/-! ## Block-Indexed Wrappers -/

-- Block-indexed block_chain: thin wrapper over row_chain.
private theorem block_chain
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    {block : ℕ}
    (h_layout : BlockLayoutFacts (air.blockStartRow block)
        (air.blockExportRow block) air.last_row)
    (k : Nat) (hk : k < 24) :
    rowOutputState air (air.blockStartRow block + k) =
      keccakRounds (k + 1) (by omega) (rowInputState air (air.blockStartRow block)) :=
  row_chain h_allHold h_layout k hk

-- Block-indexed 24-round composition: thin wrapper over rounds_24_row.
theorem block_24_rounds
    {air : Valid_KeccakfPermAir FBB ExtF}
    {block : ℕ}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    (h_layout : BlockLayoutFacts (air.blockStartRow block)
        (air.blockExportRow block) air.last_row) :
    rowOutputState air (air.blockStartRow block + 23) =
      keccakP (rowInputState air (air.blockStartRow block)) :=
  rounds_24_row h_allHold h_layout

end KeccakfPermAir.Soundness
