import VmExtensions.Soundness.KeccakfOpAir.Soundness
import OpenvmFv.Fundamentals.MemoryConsistency

set_option linter.all false
set_option maxHeartbeats 1600000

namespace KeccakfOpAir.WFC

open KeccakfOpAir.constraints
open KeccakfOpAir.Soundness
open BabyBear
open Consistency

variable {ExtF : Type} [Field ExtF]

/-! ## List helpers -/

private lemma forall_get' {α : Type} {p : α → Prop} {l : List α}
    (h : List.Forall p l) {n : ℕ} (hn : n < l.length) :
    p (l[n]) := by
  induction l generalizing n with
  | nil => exact absurd hn (Nat.not_lt_zero _)
  | cons a t ih =>
      rw [List.forall_cons] at h
      cases n with
      | zero => exact h.1
      | succ n => exact ih h.2 (Nat.lt_of_succ_lt_succ hn)

private lemma forall_flatMap_range50_pair_even'
    {P Q : ℕ → Prop}
    (h : List.Forall id ((List.range 50).flatMap (fun a => [P a, Q a])))
    (j : ℕ) (hj : j < 50) :
    P j := by
  have hidx : 2 * j < ((List.range 50).flatMap (fun a => [P a, Q a])).length := by
    have hlen : ((List.range 50).flatMap (fun a => [P a, Q a])).length = 100 := by simp
    omega
  have hjth := forall_get' h hidx
  revert hjth
  interval_cases j <;> intro hjth <;> simpa using hjth

/-! ## μ reduction helpers -/

private lemma μ_2 (x y : FBB) : μ [x, y] = y.val := rfl
private lemma μ_7 (a b c d e f g : FBB) : μ [a, b, c, d, e, f, g] = g.val := rfl

/-! ## Prev_ts bounds from memory bus axioms -/

private lemma rd_prev_ts_bound
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h_axioms : axiomsPerRow air row)
    (h_en : is_valid air row = 1) :
    (rd_aux_prev_ts air row).val < 2 ^ 29 := by
  have pa_mem := h_axioms.2.1
  simp [axioms, _memoryBus_row, _memoryBus_rd_pair, _memoryBus_buf_pair, h_en] at pa_mem
  exact pa_mem.1

set_option maxHeartbeats 3200000 in
private lemma buf_prev_ts_bound
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h_axioms : axiomsPerRow air row)
    (h_en : is_valid air row = 1)
    (k : ℕ) (hk : k < 50) :
    (buf_aux_prev_ts air row k).val < 2 ^ 29 := by
  have pa_mem := h_axioms.2.1
  simp [axioms, _memoryBus_row, _memoryBus_rd_pair, _memoryBus_buf_pair, h_en] at pa_mem
  exact forall_flatMap_range50_pair_even' pa_mem.2.2 k hk

/-! ## RowContract builder -/

private lemma mk_row_contract
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_allHold : allHold_simplified air row h_row)
    (h_axioms : axiomsPerRow air row)
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_valid air row = 1) :
    RowContract air row := by
  have hc := rows_of_allHold_simplified h_allHold
  have h_sound := row_soundness air row h_row hc h_axioms h_wf
  rcases h_sound.2 with ⟨h0, _⟩ | ⟨_, rc⟩
  · simp [h0] at h_en
  · exact rc

/-! ## WFConstraints instance -/

set_option maxHeartbeats 3200000 in
noncomputable def WFC_KeccakfOpAir
    {air : Valid_KeccakfOpAir FBB ExtF}
    (h_allHold : ∀ row (h_row : row ≤ air.last_row),
      allHold_simplified air row h_row)
    (h_axioms : ∀ row, row ≤ air.last_row → axiomsPerRow air row)
    (h_wfAssume : ∀ row, row ≤ air.last_row →
      wf_propertiesToAssumePerRow air row)
    : WFConstraints (Valid_KeccakfOpAir FBB ExtF) air μ :=
{
  execution_bus_entries :=
    (List.range (air.last_row + 1)).filterMap
    (fun row ↦
      if is_valid air row = 1 then
        .some ([pc air row, timestamp air row],
               [pc air row + 4, timestamp air row + 51])
      else
        .none)

  rising_pairs_on_execution_bus := by
    intro a b h_in; simp at h_in
    obtain ⟨row, h_row, h_valid, rfl, rfl⟩ := h_in
    rw [μ_2, μ_2]
    have h_ts := (execution_bus_bounds air row (h_axioms row (by omega)) h_valid).2.2
    have h51 : (51 : FBB).val = 51 := by rfl
    rw [fbb_val_add (by rw [h51]; omega)]
    omega

  memory_bus_entries :=
    ((List.range (air.last_row + 1)).filterMap
    (fun row ↦
      if is_valid air row = 1 then
        .some (
          [( [1, rd_ptr air row,
              buffer_ptr_limb_0 air row, buffer_ptr_limb_1 air row,
              buffer_ptr_limb_2 air row, buffer_ptr_limb_3 air row,
              rd_aux_prev_ts air row],
             [1, rd_ptr air row,
              buffer_ptr_limb_0 air row, buffer_ptr_limb_1 air row,
              buffer_ptr_limb_2 air row, buffer_ptr_limb_3 air row,
              timestamp air row] )] ++
          (List.range 50).map (fun k ↦
            ( [2, buffer_ptr air row + ((4 * k : ℕ) : FBB),
               preimage air row (4 * k), preimage air row (4 * k + 1),
               preimage air row (4 * k + 2), preimage air row (4 * k + 3),
               buf_aux_prev_ts air row k],
              [2, buffer_ptr air row + ((4 * k : ℕ) : FBB),
               postimage air row (4 * k), postimage air row (4 * k + 1),
               postimage air row (4 * k + 2), postimage air row (4 * k + 3),
               timestamp air row + ((k + 1 : ℕ) : FBB)] )))
      else
        .none)).flatten

  memory_bus_entries_wf := by
    intro a b h_in; simp at h_in
    obtain ⟨row, ⟨h_row, h_valid⟩, (⟨rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩)⟩ := h_in
    · rfl
    · rfl

  rising_pairs_on_memory_bus := by
    intro a b h_in; simp at h_in
    obtain ⟨row, ⟨h_row, h_valid⟩, (⟨rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩)⟩ := h_in
    · -- rd pair: rd_aux_prev_ts.val < timestamp.val
      rw [μ_7, μ_7]
      exact rd_timestamp_ordered
        (mk_row_contract air row (by omega) (h_allHold row (by omega))
          (h_axioms row (by omega)) (h_wfAssume row (by omega)) h_valid)
        (rd_prev_ts_bound air row (h_axioms row (by omega)) h_valid)
    · -- buf pair k: (buf_aux_prev_ts k).val < (timestamp + (k+1)).val
      rw [μ_7, μ_7]
      have h := buf_timestamp_ordered
        (mk_row_contract air row (by omega) (h_allHold row (by omega))
          (h_axioms row (by omega)) (h_wfAssume row (by omega)) h_valid)
        k (by omega)
        (buf_prev_ts_bound air row (h_axioms row (by omega)) h_valid k (by omega))
      simp only [Nat.cast_add, Nat.cast_one] at h; exact h
}

/-! ## WFChip wrapper -/

noncomputable def wfc_opAir
    {air : Valid_KeccakfOpAir FBB ExtF}
    (h_allHold : ∀ row (h_row : row ≤ air.last_row),
      allHold_simplified air row h_row)
    (h_axioms : ∀ row, row ≤ air.last_row → axiomsPerRow air row)
    (h_wfAssume : ∀ row, row ≤ air.last_row →
      wf_propertiesToAssumePerRow air row)
    : WFChip μ where
  ChipType := Valid_KeccakfOpAir FBB ExtF
  chip := air
  inst_wf := WFC_KeccakfOpAir h_allHold h_axioms h_wfAssume

end KeccakfOpAir.WFC
