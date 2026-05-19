/-
  Derives OpTimestampUnique from execution bus consistency.

  Proves that distinct enabled KeccakfOpAir rows have distinct timestamps,
  using the framework's `execution_bus_consistency` theorem applied to a chip
  list containing KeccakfOpAir.
-/
import VmExtensions.Soundness.KeccakfOpAir.WFConstraints
import OpenvmFv.Fundamentals.MemoryConsistency

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Keccakf.Soundness

open BabyBear
open Consistency
open KeccakfOpAir
open KeccakfOpAir.constraints
open KeccakfOpAir.WFC

variable {ExtF : Type} [Field ExtF]

/-! ## Definition -/

/-- Distinct enabled KeccakfOpAir rows have distinct timestamps. -/
def OpTimestampUnique (opAir : Valid_KeccakfOpAir FBB ExtF) : Prop :=
  ∀ r₁ r₂, r₁ ≤ opAir.last_row → r₂ ≤ opAir.last_row →
    is_valid opAir r₁ = 1 → is_valid opAir r₂ = 1 →
    (timestamp opAir r₁).val = (timestamp opAir r₂).val → r₁ = r₂

/-! ## List helper lemmas -/

section ListHelpers

variable {α : Type*} {β : Type*} {γ : Type*}

-- In a pairwise strictly increasing list (by μ), members with the same μ are equal.
private lemma pairwise_lt_mem_unique
    {l : List (List FBB)} (h : l.Pairwise (fun x y => μ x < μ y))
    {a b : List FBB} (ha : a ∈ l) (hb : b ∈ l) (heq : μ a = μ b) :
    a = b := by
  induction l with
  | nil => simp at ha
  | cons hd tl ih =>
    rw [List.pairwise_cons] at h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha'
    · rcases hb with rfl | hb'
      · rfl
      · exact absurd heq (Nat.ne_of_lt (h.1 b hb'))
    · rcases hb with rfl | hb'
      · exact absurd heq.symm (Nat.ne_of_lt (h.1 a ha'))
      · exact ih h.2 ha' hb'

-- Pairwise strictly increasing → Nodup.
private lemma chain_nodup_of_pairwise
    {l : List (List FBB)} (h : l.Pairwise (fun x y => μ x < μ y)) :
    l.Nodup :=
  h.imp (fun hab heq => absurd (heq ▸ hab) (Nat.lt_irrefl _))

-- Pairwise on a concatenation → pairwise on the left part.
private lemma pairwise_of_append_left {R : α → α → Prop}
    {l₁ l₂ : List α} (h : (l₁ ++ l₂).Pairwise R) :
    l₁.Pairwise R :=
  (List.pairwise_append.mp h).1

-- Membership in zip → first component is in the first list.
private lemma fst_mem_of_mem_zip
    {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : (a, b) ∈ List.zip l₁ l₂) : a ∈ l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩ | h'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h')

-- If the first list has Nodup, then zip has Nodup.
private lemma zip_nodup_of_left_nodup
    {l₁ : List α} {l₂ : List β} (h : l₁.Nodup) :
    (List.zip l₁ l₂).Nodup := by
  induction l₁ generalizing l₂ with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    cases l₂ with
    | nil => exact List.nodup_nil
    | cons y ys =>
      rw [List.zip_cons_cons, List.nodup_cons]
      rw [List.nodup_cons] at h
      exact ⟨fun hmem => h.1 (fst_mem_of_mem_zip hmem), ih h.2⟩

-- An element's entries in a flatMap form a sublist.
private lemma sublist_flatMap_of_mem
    {f : α → List β} {a : α} {l : List α} (h : a ∈ l) :
    List.Sublist (f a) (l.flatMap f) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.mem_cons] at h ⊢
    rcases h with rfl | h'
    · exact List.sublist_append_left _ _
    · exact (ih h').trans (List.sublist_append_right _ _)

-- Two distinct inputs mapping to the same filterMap output → not Nodup.
private lemma filterMap_not_nodup_of_dup [DecidableEq β]
    {l : List α} {f : α → Option β} {a₁ a₂ : α} {b : β}
    (h₁ : a₁ ∈ l) (h₂ : a₂ ∈ l) (hne : a₁ ≠ a₂)
    (hnd : l.Nodup) (hf₁ : f a₁ = some b) (hf₂ : f a₂ = some b) :
    ¬ (l.filterMap f).Nodup := by
  induction l with
  | nil => simp at h₁
  | cons hd tl ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons] at h₁ h₂
    rcases h₁ with h₁_eq | h₁'
    · -- a₁ = hd
      subst h₁_eq
      rcases h₂ with h₂_eq | h₂'
      · -- a₂ = a₁, contradicts hne
        exact absurd h₂_eq.symm hne
      · -- a₂ ∈ tl: filterMap (a₁ :: tl) f = b :: tl.filterMap f, and b ∈ tl.filterMap f
        have : (a₁ :: tl).filterMap f = b :: tl.filterMap f := by
          show (match f a₁ with | none => _ | some b => b :: _) = _; rw [hf₁]
        rw [this]; intro hnd'
        exact (List.nodup_cons.mp hnd').1 (List.mem_filterMap.mpr ⟨a₂, h₂', hf₂⟩)
    · rcases h₂ with h₂_eq | h₂'
      · -- a₂ = hd, a₁ ∈ tl
        subst h₂_eq
        have : (a₂ :: tl).filterMap f = b :: tl.filterMap f := by
          show (match f a₂ with | none => _ | some b => b :: _) = _; rw [hf₂]
        rw [this]; intro hnd'
        exact (List.nodup_cons.mp hnd').1 (List.mem_filterMap.mpr ⟨a₁, h₁', hf₁⟩)
      · -- both in tl: recurse
        have ih' : ¬ (tl.filterMap f).Nodup := ih h₁' h₂' hnd.2
        intro hnd'
        apply ih'
        have hfm : (hd :: tl).filterMap f =
            match f hd with | none => tl.filterMap f | some c => c :: tl.filterMap f := rfl
        rw [hfm] at hnd'
        split at hnd'
        · exact hnd'
        · exact (List.nodup_cons.mp hnd').2

end ListHelpers

/-! ## Entry membership -/

-- An enabled row's execution bus entry is in execution_bus chips.
private lemma enabled_row_entry_mem_exec_bus
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (h_allHold : ∀ row (h_row : row ≤ opAir.last_row), allHold_simplified opAir row h_row)
    (h_axioms : ∀ row, row ≤ opAir.last_row → axiomsPerRow opAir row)
    (h_wfAssume : ∀ row, row ≤ opAir.last_row → wf_propertiesToAssumePerRow opAir row)
    {chips : List (WFChip μ)}
    (h_opAir_chip : wfc_opAir h_allHold h_axioms h_wfAssume ∈ chips)
    {row : ℕ} (h_row : row ≤ opAir.last_row) (h_valid : is_valid opAir row = 1) :
    ([pc opAir row, timestamp opAir row],
     [pc opAir row + 4, timestamp opAir row + 51]) ∈ execution_bus chips := by
  apply List.mem_flatMap.mpr
  exact ⟨wfc_opAir h_allHold h_axioms h_wfAssume, h_opAir_chip, by
    show _ ∈ (WFC_KeccakfOpAir h_allHold h_axioms h_wfAssume).execution_bus_entries
    simp only [WFC_KeccakfOpAir, List.mem_filterMap, List.mem_range]
    exact ⟨row, by omega, by simp [h_valid]⟩⟩

-- μ of a two-element list is the last element's val.
private lemma μ_two (x y : FBB) : μ [x, y] = y.val := rfl

/-! ## Main theorem -/

/-- OpTimestampUnique is derived from execution bus consistency.
    Given that KeccakfOpAir participates in a chip list with a balanced execution bus,
    distinct enabled rows must have distinct timestamps. -/
theorem op_timestamp_unique
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (h_allHold : ∀ row (h_row : row ≤ opAir.last_row),
      allHold_simplified opAir row h_row)
    (h_axioms : ∀ row, row ≤ opAir.last_row → axiomsPerRow opAir row)
    (h_wfAssume : ∀ row, row ≤ opAir.last_row →
      wf_propertiesToAssumePerRow opAir row)
    {chips : List (WFChip μ)} {lb rb : List FBB}
    (h_opAir_chip : wfc_opAir h_allHold h_axioms h_wfAssume ∈ chips)
    (h_bus_length : 2 * (execution_bus chips).length +
                    2 * (memory_bus chips).length + 2 < BB_prime)
    (h_exec_balanced : InteractionList.is_balanced
      ([((1 : FBB), lb)] ++
       InteractionList.rising_bus μ (execution_bus chips)
         (execution_bus_is_rising_bus chips) ++
       [((-1 : FBB), rb)])) :
    OpTimestampUnique opAir := by
  intro r₁ r₂ hr₁ hr₂ hv₁ hv₂ hts
  by_contra h_ne
  -- Step 1: execution bus is non-empty (row r₁ contributes)
  have h_e₁ := enabled_row_entry_mem_exec_bus opAir h_allHold h_axioms h_wfAssume
    h_opAir_chip hr₁ hv₁
  have h_nonempty : 0 < (execution_bus chips).length := by
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem h_e₁)
  -- Step 2: get the chain from execution_bus_consistency
  obtain ⟨xs, h_perm, h_pw⟩ := execution_bus_consistency chips h_bus_length h_nonempty
    h_exec_balanced
  -- Step 3: entry for r₂ is also in execution_bus
  have h_e₂ := enabled_row_entry_mem_exec_bus opAir h_allHold h_axioms h_wfAssume
    h_opAir_chip hr₂ hv₂
  -- Step 4: through Perm, entries are in zip → first components in lb :: xs
  have h_fst₁ : [pc opAir r₁, timestamp opAir r₁] ∈ lb :: xs :=
    fst_mem_of_mem_zip (h_perm.mem_iff.mp h_e₁)
  have h_fst₂ : [pc opAir r₂, timestamp opAir r₂] ∈ lb :: xs :=
    fst_mem_of_mem_zip (h_perm.mem_iff.mp h_e₂)
  -- Step 5: pairwise on prefix lb :: xs
  have h_pw_prefix : (lb :: xs).Pairwise (fun x y => μ x < μ y) :=
    pairwise_of_append_left (l₂ := [rb]) (by rwa [List.cons_append] at h_pw)
  -- Step 6: same timestamp.val → same μ → same first component
  have h_mu_eq : μ [pc opAir r₁, timestamp opAir r₁] =
      μ [pc opAir r₂, timestamp opAir r₂] := by
    simp only [μ_two]; exact hts
  have h_fst_eq := pairwise_lt_mem_unique h_pw_prefix h_fst₁ h_fst₂ h_mu_eq
  -- Step 7: first component equality → pc and timestamp equality as FBB values
  have h_pc_eq : pc opAir r₁ = pc opAir r₂ := (List.cons.inj h_fst_eq).1
  have h_ts_eq : timestamp opAir r₁ = timestamp opAir r₂ :=
    (List.cons.inj (List.cons.inj h_fst_eq).2).1
  -- Step 8: execution_bus is Nodup (chain → zip Nodup → Perm)
  have h_chain_nd := chain_nodup_of_pairwise h_pw
  have h_prefix_nd : (lb :: xs).Nodup := by
    have hsub : List.Sublist (lb :: xs) (lb :: xs ++ [rb]) := by
      rw [List.cons_append]; exact List.sublist_append_left _ _
    exact List.Nodup.sublist hsub h_chain_nd
  have h_zip_nd := zip_nodup_of_left_nodup (l₂ := xs ++ [rb]) h_prefix_nd
  have h_exec_nd := h_perm.nodup_iff.mpr h_zip_nd
  -- Step 9: chip entries are a sublist of execution_bus, hence Nodup
  have h_chip_sub : List.Sublist
      (wfc_opAir h_allHold h_axioms h_wfAssume).inst_wf.execution_bus_entries
      (execution_bus chips) := by
    unfold execution_bus
    -- Prove for a general list to avoid induction generalizing irrelevant hypotheses
    suffices ∀ (l : List (WFChip μ)),
        wfc_opAir h_allHold h_axioms h_wfAssume ∈ l →
        List.Sublist (wfc_opAir h_allHold h_axioms h_wfAssume).inst_wf.execution_bus_entries
          (List.flatMap (fun chip => chip.inst_wf.execution_bus_entries) l)
      from this chips h_opAir_chip
    intro l hmem
    induction l with
    | nil => simp at hmem
    | cons c cs ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | h'
      · exact List.sublist_append_left _ _
      · exact (ih h').trans (List.sublist_append_right _ _)
  have h_chip_nd := List.Nodup.sublist h_chip_sub h_exec_nd
  -- Step 10: the filterMap for our chip is not Nodup (r₁ ≠ r₂ produce same entry)
  let f : ℕ → Option (List FBB × List FBB) := fun row =>
    if is_valid opAir row = 1 then
      .some ([pc opAir row, timestamp opAir row],
             [pc opAir row + 4, timestamp opAir row + 51])
    else .none
  have h_chip_eq :
      (wfc_opAir h_allHold h_axioms h_wfAssume).inst_wf.execution_bus_entries =
      (List.range (opAir.last_row + 1)).filterMap f := by
    show (WFC_KeccakfOpAir h_allHold h_axioms h_wfAssume).execution_bus_entries = _
    rfl
  have h_f₁ : f r₁ = some ([pc opAir r₁, timestamp opAir r₁],
      [pc opAir r₁ + 4, timestamp opAir r₁ + 51]) := by
    simp only [f, hv₁, ↓reduceIte]
  have h_f₂ : f r₂ = some ([pc opAir r₁, timestamp opAir r₁],
      [pc opAir r₁ + 4, timestamp opAir r₁ + 51]) := by
    simp only [f, hv₂, ↓reduceIte, h_pc_eq, h_ts_eq]
  have h_not_nd := filterMap_not_nodup_of_dup
    (List.mem_range.mpr (by omega : r₁ < opAir.last_row + 1))
    (List.mem_range.mpr (by omega : r₂ < opAir.last_row + 1))
    h_ne (List.nodup_range) h_f₁ h_f₂
  -- Step 11: contradiction
  rw [h_chip_eq] at h_chip_nd
  exact h_not_nd h_chip_nd

end Keccakf.Soundness
