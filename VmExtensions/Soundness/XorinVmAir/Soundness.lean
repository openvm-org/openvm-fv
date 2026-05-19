/-
  Circuit soundness theorem for XorinVmAir (FBB-specialized).

  Uses the NonValidRows → ValidRows proof structure:
    NonValidRows → ValidRows (wf_propertiesToAssert → essentials → spec → row_contract)

  Uses structures for `Essentials` and `XorinRowContract` for named field access.
  XorinRowContract is bus-effect-centric and self-contained: execution send,
  per-word memory facts, inactive word absence, spec-level postimage equality,
  and all bounds callers need.
-/
import VmExtensions.Soundness.XorinVmAir.BusFacts
import VmExtensions.Constraints.XorinVmAirBus
import OpenvmFv.Fundamentals.BabyBear
import OpenvmFv.Fundamentals.Interaction

set_option autoImplicit false
set_option linter.all false

namespace XorinVmAir.Soundness

open XorinVmAir.constraints
open XorinVmAir.Soundness.BusFacts
open Xorin.Spec

variable {ExtF : Type} [Field ExtF]

/-! ## Circuit-to-Spec Interpretation (FBB-specialized) -/

-- Interpret circuit columns as XorinInput
noncomputable def xorinInputOfRow
    (air : Valid_XorinVmAir FBB ExtF) (row : ℕ) : XorinInput where
  pc := (pc air row).val
  start_timestamp := (start_timestamp air row).val
  buffer_ptr := (buffer_ptr air row).val
  input_ptr := (input_ptr air row).val
  xorin_len := (xorin_len air row).val
  preimage := fun i => (preimage_buffer_byte air i row).val
  input := fun i => (input_byte air i row).val

private lemma propsAssert_append
    {α : Type} [Interaction.BusEntry FBB α] (xs ys : List α) :
    propertiesToAssert (xs ++ ys) ↔
      propertiesToAssert xs ∧ propertiesToAssert ys := by
  unfold propertiesToAssert
  rw [List.map_append, List.forall_append]

private lemma propsAssert_flatMap_of_each
    {β α : Type} [Interaction.BusEntry FBB α]
    (xs : List β) (f : β → List α)
    (h_each : ∀ x, x ∈ xs → propertiesToAssert (f x)) :
    propertiesToAssert (xs.flatMap f) := by
  induction xs with
  | nil =>
      simp [propertiesToAssert]
  | cons x xs ih =>
      rw [List.flatMap_cons, propsAssert_append]
      refine ⟨h_each x (by simp), ih ?_⟩
      intro y hy
      exact h_each y (by simp [hy])

/-! ===== NON-VALID ROWS ===== -/

namespace NonValidRows

variable (air : Valid_XorinVmAir FBB ExtF) (row : ℕ)
variable (h_row : row ≤ air.last_row)
variable (h_constraints : allHold_simplified air row h_row)
variable (h_disabled : is_enabled air row = 0)

-- wf_propertiesToAssertPerRow is vacuously true when disabled:
-- every bus multiplicity has is_enabled as a factor, so when is_enabled = 0,
-- no multiplicity equals 1 (or -1), making all wf_assert_cond implications vacuous.
theorem wf_propertiesToAssert :
    (h_disabled : is_enabled air row = 0) →
    wf_propertiesToAssertPerRow air row
    := by
  intro h_disabled
  have h_exec : propertiesToAssert (_executionBus_row air row) := by
    unfold propertiesToAssert _executionBus_row
    simp [executionBus_row, Interaction.BusEntry.assert, h_disabled]
  have h_mem_reg : propertiesToAssert (_memoryBus_reg_pairs air row) := by
    unfold propertiesToAssert _memoryBus_reg_pairs _memoryBus_buffer_reg_pair
      _memoryBus_input_reg_pair _memoryBus_len_reg_pair
    simp [Interaction.BusEntry.assert, h_disabled]
  have h_mem_pre : propertiesToAssert (_memoryBus_preimage_pairs air row) := by
    apply propsAssert_flatMap_of_each
    intro j hj
    unfold propertiesToAssert
    simp [_memoryBus_preimage_pair, memoryBus_word_factor, Interaction.BusEntry.assert, h_disabled]
  have h_mem_input : propertiesToAssert (_memoryBus_input_pairs air row) := by
    apply propsAssert_flatMap_of_each
    intro j hj
    unfold propertiesToAssert
    simp [_memoryBus_input_pair, memoryBus_word_factor, Interaction.BusEntry.assert, h_disabled]
  have h_mem_post : propertiesToAssert (_memoryBus_postimage_pairs air row) := by
    apply propsAssert_flatMap_of_each
    intro j hj
    unfold propertiesToAssert
    simp [_memoryBus_postimage_pair, memoryBus_word_factor, Interaction.BusEntry.assert, h_disabled]
  have h_mem_input_post : propertiesToAssert
      (_memoryBus_input_pairs air row ++ _memoryBus_postimage_pairs air row) := by
    exact (propsAssert_append (_memoryBus_input_pairs air row) (_memoryBus_postimage_pairs air row)).2
      ⟨h_mem_input, h_mem_post⟩
  have h_mem_tail : propertiesToAssert
      (_memoryBus_preimage_pairs air row ++
        (_memoryBus_input_pairs air row ++ _memoryBus_postimage_pairs air row)) := by
    exact (propsAssert_append (_memoryBus_preimage_pairs air row)
      (_memoryBus_input_pairs air row ++ _memoryBus_postimage_pairs air row)).2
      ⟨h_mem_pre, h_mem_input_post⟩
  have h_mem : propertiesToAssert (_memoryBus_row air row) := by
    simpa [_memoryBus_row, List.append_assoc] using
      (propsAssert_append (_memoryBus_reg_pairs air row)
        (_memoryBus_preimage_pairs air row ++
          (_memoryBus_input_pairs air row ++ _memoryBus_postimage_pairs air row))).2
        ⟨h_mem_reg, h_mem_tail⟩
  have h_range_prefix : propertiesToAssert (_rangeCheckerBus_prefix air row) := by
    simp [propertiesToAssert, Interaction.BusEntry.assert, _rangeCheckerBus_prefix, h_disabled]
  have h_range_pre : propertiesToAssert (_rangeCheckerBus_preimage_aux air row) := by
    apply propsAssert_flatMap_of_each
    intro j hj
    unfold propertiesToAssert
    simp [_rangeCheckerBus_preimage_aux_pair, Interaction.BusEntry.assert, h_disabled]
  have h_range_input : propertiesToAssert (_rangeCheckerBus_input_aux air row) := by
    apply propsAssert_flatMap_of_each
    intro j hj
    unfold propertiesToAssert
    simp [_rangeCheckerBus_input_aux_pair, Interaction.BusEntry.assert, h_disabled]
  have h_range_post : propertiesToAssert (_rangeCheckerBus_postimage_aux air row) := by
    apply propsAssert_flatMap_of_each
    intro j hj
    unfold propertiesToAssert
    simp [_rangeCheckerBus_postimage_aux_pair, Interaction.BusEntry.assert, h_disabled]
  have h_range_input_post : propertiesToAssert
      (_rangeCheckerBus_input_aux air row ++ _rangeCheckerBus_postimage_aux air row) := by
    exact (propsAssert_append (_rangeCheckerBus_input_aux air row)
      (_rangeCheckerBus_postimage_aux air row)).2 ⟨h_range_input, h_range_post⟩
  have h_range : propertiesToAssert (_rangeCheckerBus_row air row) := by
    simpa [_rangeCheckerBus_row, List.append_assoc] using
      (propsAssert_append (_rangeCheckerBus_prefix air row)
        (_rangeCheckerBus_preimage_aux air row ++
          (_rangeCheckerBus_input_aux air row ++ _rangeCheckerBus_postimage_aux air row))).2
        ⟨h_range_prefix,
          (propsAssert_append (_rangeCheckerBus_preimage_aux air row)
            (_rangeCheckerBus_input_aux air row ++ _rangeCheckerBus_postimage_aux air row)).2
            ⟨h_range_pre, h_range_input_post⟩⟩
  have h_program : propertiesToAssert (_programBus_row air row) := by
    unfold propertiesToAssert _programBus_row
    simp [programBus_row, Interaction.BusEntry.assert, h_disabled]
  have h_bitwise : propertiesToAssert (_bitwiseBus_row air row) := by
    unfold propertiesToAssert _bitwiseBus_row _bitwiseBus_prefix _bitwiseBus_active_bytes
    rw [List.map_append, List.forall_append]
    refine ⟨?_, ?_⟩
    · simp [Interaction.BusEntry.assert, h_disabled]
    · rw [List.forall_map_iff, List.forall_map_iff, List.forall_iff_forall_mem]
      intro i hi
      change Interaction.BusEntry.assert FBB (_bitwiseBus_active_byte air row i)
      simp [_bitwiseBus_active_byte, Interaction.BusEntry.assert, h_disabled]
  exact ⟨h_exec, h_mem, h_range, h_program, h_bitwise⟩

-- All bus multiplicities are zero when disabled
-- (every multiplicity in every bus row has is_enabled as a factor)
theorem multiplicities_zero :
    (h_disabled : is_enabled air row = 0) →
    ∀ entry, entry ∈ busRow air row → entry.1 = 0
    := by
  intro h_disabled
  intro entry h_mem
  simp [busRow, List.mem_append] at h_mem
  rcases h_mem with h_exec | h_mem | h_prog | h_range | h_bit
  · simp [executionBus_row, h_disabled] at h_exec
    rcases h_exec with rfl | rfl <;> simp
  · exact mem_memoryBus_row_disabled_zero h_mem h_disabled
  · simp [programBus_row, h_disabled] at h_prog
    rcases h_prog with rfl
    simp
  · exact mem_rangeCheckerBus_row_disabled_zero h_range h_disabled
  · exact mem_bitwiseBus_row_disabled_zero h_bit h_disabled

end NonValidRows

/-! ===== VALID ROWS ===== -/

namespace ValidRows

variable (air : Valid_XorinVmAir FBB ExtF) (row : ℕ)
variable (h_row : row ≤ air.last_row)
variable (h_constraints : allHold_simplified air row h_row)
variable (h_enabled : is_enabled air row = 1)
variable (h_axioms : axiomsPerRow air row)
variable (h_wf_assume : wf_propertiesToAssumePerRow air row)

/-! ### Step 1: wf_propertiesToAssert -/

private lemma propertiesToAssert_append
    {α : Type} [Interaction.BusEntry FBB α] (xs ys : List α) :
    propertiesToAssert (xs ++ ys) ↔
      propertiesToAssert xs ∧ propertiesToAssert ys := by
  unfold propertiesToAssert
  rw [List.map_append, List.forall_append]

private lemma propertiesToAssert_flatMap_of_each
    {β α : Type} [Interaction.BusEntry FBB α]
    (xs : List β) (f : β → List α)
    (h_each : ∀ x, x ∈ xs → propertiesToAssert (f x)) :
    propertiesToAssert (xs.flatMap f) := by
  induction xs with
  | nil =>
      simp [propertiesToAssert]
  | cons x xs ih =>
      rw [List.flatMap_cons, propertiesToAssert_append]
      refine ⟨h_each x (by simp), ih ?_⟩
      intro y hy
      exact h_each y (by simp [hy])

private lemma rangeChecker_pair_wf
    (factor val17 val12 : FBB)
    (hf : factor = 0 ∨ factor = 1) :
    propertiesToAssert
      ([{ multiplicity := factor, val := val17, deg := 17 },
        { multiplicity := factor, val := val12, deg := 12 }] :
          List (Interaction.RangeCheckerBusEntry FBB)) := by
  rcases hf with rfl | rfl <;>
    simp [propertiesToAssert, Interaction.BusEntry.assert]

private lemma memory_pair_wf
    (factor as ptr x0 x1 x2 x3 recvTs sendTs : FBB)
    (hf : factor = 0 ∨ factor = 1)
    (hwf : factor = 1 →
      as.val < 3 ∧
      ptr.val < OpenVM_address_space_size ∧
      x0.val < 256 ∧ x1.val < 256 ∧ x2.val < 256 ∧ x3.val < 256) :
    propertiesToAssert
      ([{ multiplicity := 2013265920 * factor, as := as, ptr := ptr,
          x0 := x0, x1 := x1, x2 := x2, x3 := x3, timestamp := recvTs },
        { multiplicity := factor, as := as, ptr := ptr,
          x0 := x0, x1 := x1, x2 := x2, x3 := x3, timestamp := sendTs }] :
          List (Interaction.MemoryBusEntry FBB)) := by
  rcases hf with rfl | rfl
  · simp [propertiesToAssert, Interaction.BusEntry.assert]
  · unfold propertiesToAssert
    simp [Interaction.BusEntry.assert]
    simpa using hwf rfl

private lemma memory_postimage_pair_wf
    (factor ptr recv0 recv1 recv2 recv3 recvTs send0 send1 send2 send3 sendTs : FBB)
    (hf : factor = 0 ∨ factor = 1)
    (hwf : factor = 1 →
      ptr.val < OpenVM_address_space_size ∧
      send0.val < 256 ∧ send1.val < 256 ∧ send2.val < 256 ∧ send3.val < 256) :
    propertiesToAssert
      ([{ multiplicity := 2013265920 * factor, as := 2, ptr := ptr,
          x0 := recv0, x1 := recv1, x2 := recv2, x3 := recv3, timestamp := recvTs },
        { multiplicity := factor, as := 2, ptr := ptr,
          x0 := send0, x1 := send1, x2 := send2, x3 := send3, timestamp := sendTs }] :
          List (Interaction.MemoryBusEntry FBB)) := by
  rcases hf with rfl | rfl
  · simp [propertiesToAssert, Interaction.BusEntry.assert]
  · unfold propertiesToAssert
    simp [Interaction.BusEntry.assert]
    have h := hwf rfl
    rcases h with ⟨hptr, hx0, hx1, hx2, hx3⟩
    exact ⟨hptr, hx0, hx1, hx2, hx3⟩

theorem execution_wf_propertiesToAssert :
    propertiesToAssert (_executionBus_row air row) := by
  simp [propertiesToAssert]

theorem program_wf_propertiesToAssert :
    (h_enabled : is_enabled air row = 1) →
    propertiesToAssert (_programBus_row air row) := by
  intro h_enabled
  unfold propertiesToAssert _programBus_row
  simp [programBus_row]
  intro h
  rw [h_enabled] at h
  norm_num at h

theorem rangeChecker_wf_propertiesToAssert :
    (h_constraints : allHold_simplified air row h_row) →
    (h_enabled : is_enabled air row = 1) →
    propertiesToAssert (_rangeCheckerBus_row air row) := by
  intro h_constraints h_enabled
  have h_prefix : propertiesToAssert (_rangeCheckerBus_prefix air row) := by
    simp [propertiesToAssert, Interaction.BusEntry.assert, _rangeCheckerBus_prefix, h_enabled]
  have h_preimage : propertiesToAssert (_rangeCheckerBus_preimage_aux air row) := by
    apply propertiesToAssert_flatMap_of_each
    intro j hj
    have hj_lt : j < 34 := List.mem_range.mp hj
    have hf :
        is_enabled air row * (1 - is_padding_byte air j row) = 0 ∨
        is_enabled air row * (1 - is_padding_byte air j row) = 1 := by
      rcases padding_byte_binary h_constraints j hj_lt with h_pad | h_pad
      · rw [h_enabled, h_pad, sub_zero, mul_one]
        exact Or.inr rfl
      · rw [h_enabled, h_pad]
        simp
    simpa [_rangeCheckerBus_preimage_aux_pair] using
      rangeChecker_pair_wf
        (is_enabled air row * (1 - is_padding_byte air j row))
        (mem_aux_col air (112 + 3 * j) row)
        (mem_aux_col air (113 + 3 * j) row) hf
  have h_input : propertiesToAssert (_rangeCheckerBus_input_aux air row) := by
    apply propertiesToAssert_flatMap_of_each
    intro j hj
    have hj_lt : j < 34 := List.mem_range.mp hj
    have hf :
        is_enabled air row * (1 - is_padding_byte air j row) = 0 ∨
        is_enabled air row * (1 - is_padding_byte air j row) = 1 := by
      rcases padding_byte_binary h_constraints j hj_lt with h_pad | h_pad
      · rw [h_enabled, h_pad, sub_zero, mul_one]
        exact Or.inr rfl
      · rw [h_enabled, h_pad]
        simp
    simpa [_rangeCheckerBus_input_aux_pair] using
      rangeChecker_pair_wf
        (is_enabled air row * (1 - is_padding_byte air j row))
        (mem_aux_col air (10 + 3 * j) row)
        (mem_aux_col air (11 + 3 * j) row) hf
  have h_postimage : propertiesToAssert (_rangeCheckerBus_postimage_aux air row) := by
    apply propertiesToAssert_flatMap_of_each
    intro j hj
    have hj_lt : j < 34 := List.mem_range.mp hj
    have hf :
        is_enabled air row * (1 - is_padding_byte air j row) = 0 ∨
        is_enabled air row * (1 - is_padding_byte air j row) = 1 := by
      rcases padding_byte_binary h_constraints j hj_lt with h_pad | h_pad
      · rw [h_enabled, h_pad, sub_zero, mul_one]
        exact Or.inr rfl
      · rw [h_enabled, h_pad]
        simp
    simpa [_rangeCheckerBus_postimage_aux_pair] using
      rangeChecker_pair_wf
        (is_enabled air row * (1 - is_padding_byte air j row))
        (mem_aux_col air (214 + 7 * j) row)
        (mem_aux_col air (215 + 7 * j) row) hf
  have h_input_post : propertiesToAssert (_rangeCheckerBus_input_aux air row ++ _rangeCheckerBus_postimage_aux air row) := by
    exact (propertiesToAssert_append (_rangeCheckerBus_input_aux air row) (_rangeCheckerBus_postimage_aux air row)).2
      ⟨h_input, h_postimage⟩
  have h_tail : propertiesToAssert
      (_rangeCheckerBus_preimage_aux air row ++
        (_rangeCheckerBus_input_aux air row ++ _rangeCheckerBus_postimage_aux air row)) := by
    exact (propertiesToAssert_append (_rangeCheckerBus_preimage_aux air row)
      (_rangeCheckerBus_input_aux air row ++ _rangeCheckerBus_postimage_aux air row)).2
      ⟨h_preimage, h_input_post⟩
  have h_all : propertiesToAssert
      (_rangeCheckerBus_prefix air row ++
        (_rangeCheckerBus_preimage_aux air row ++
          (_rangeCheckerBus_input_aux air row ++ _rangeCheckerBus_postimage_aux air row))) := by
    exact (propertiesToAssert_append (_rangeCheckerBus_prefix air row)
      (_rangeCheckerBus_preimage_aux air row ++
        (_rangeCheckerBus_input_aux air row ++ _rangeCheckerBus_postimage_aux air row))).2
      ⟨h_prefix, h_tail⟩
  simpa [_rangeCheckerBus_row, List.append_assoc] using h_all

theorem bitwise_wf_propertiesToAssert :
    (h_constraints : allHold_simplified air row h_row) →
    (h_enabled : is_enabled air row = 1) →
    propertiesToAssert (_bitwiseBus_row air row) := by
  intro h_constraints h_enabled
  unfold propertiesToAssert _bitwiseBus_row _bitwiseBus_prefix _bitwiseBus_active_bytes
  rw [List.map_append, List.forall_append]
  refine ⟨?_, ?_⟩
  · simp [Interaction.BusEntry.assert, h_enabled]
  · rw [List.forall_map_iff, List.forall_map_iff, List.forall_iff_forall_mem]
    intro i hi
    change Interaction.BusEntry.assert FBB (_bitwiseBus_active_byte air row i)
    intro h_neg
    have hi' : i < 136 := by
      simpa using hi
    have h_pad := padding_byte_binary h_constraints (i / 4) (by omega)
    rcases h_pad with h_pad | h_pad
    · simp [_bitwiseBus_active_byte, h_enabled, h_pad, sub_zero] at h_neg
    · simp [_bitwiseBus_active_byte, h_enabled, h_pad] at h_neg

theorem memory_wf_propertiesToAssert :
    (h_constraints : allHold_simplified air row h_row) →
    (h_enabled : is_enabled air row = 1) →
    (h_axioms : axiomsPerRow air row) →
    (h_wf_assume : wf_propertiesToAssumePerRow air row) →
    propertiesToAssert (_memoryBus_row air row) := by
  intro h_constraints h_enabled h_axioms h_wf_assume
  have h_buffer_reg : propertiesToAssert (_memoryBus_buffer_reg_pair air row) := by
    have h0 := range_check_buffer_ptr_limbs air row h_wf_assume h_enabled 0 (by omega)
    have h1 := range_check_buffer_ptr_limbs air row h_wf_assume h_enabled 1 (by omega)
    have h2 := range_check_buffer_ptr_limbs air row h_wf_assume h_enabled 2 (by omega)
    have h3 := range_check_buffer_ptr_limbs air row h_wf_assume h_enabled 3 (by omega)
    have hptr : (buffer_reg_ptr air row).val < OpenVM_address_space_size := by
      simpa using
        (buffer_reg_ptr_bound air row h_wf_assume h_enabled)
    simpa [_memoryBus_buffer_reg_pair] using
      memory_pair_wf
        (is_enabled air row) 1 (buffer_reg_ptr air row)
        (buffer_ptr_limb air 0 row) (buffer_ptr_limb air 1 row)
        (buffer_ptr_limb air 2 row) (buffer_ptr_limb air 3 row)
        (mem_aux_col air 0 row) (start_timestamp air row)
        (Or.inr h_enabled)
        (fun _ => ⟨by decide, hptr, h0, h1, h2, h3⟩)
  have h_input_reg : propertiesToAssert (_memoryBus_input_reg_pair air row) := by
    have h0 := range_check_input_ptr_limbs air row h_wf_assume h_enabled 0 (by omega)
    have h1 := range_check_input_ptr_limbs air row h_wf_assume h_enabled 1 (by omega)
    have h2 := range_check_input_ptr_limbs air row h_wf_assume h_enabled 2 (by omega)
    have h3 := range_check_input_ptr_limbs air row h_wf_assume h_enabled 3 (by omega)
    have hptr : (input_reg_ptr air row).val < OpenVM_address_space_size := by
      simpa using
        (input_reg_ptr_bound air row h_wf_assume h_enabled)
    simpa [_memoryBus_input_reg_pair] using
      memory_pair_wf
        (is_enabled air row) 1 (input_reg_ptr air row)
        (input_ptr_limb air 0 row) (input_ptr_limb air 1 row)
        (input_ptr_limb air 2 row) (input_ptr_limb air 3 row)
        (mem_aux_col air 3 row) (start_timestamp air row + 1)
        (Or.inr h_enabled)
        (fun _ => ⟨by decide, hptr, h0, h1, h2, h3⟩)
  have h_len_reg : propertiesToAssert (_memoryBus_len_reg_pair air row) := by
    have h0 := range_check_len_limbs air row h_wf_assume h_enabled 0 (by omega)
    have h1 := range_check_len_limbs air row h_wf_assume h_enabled 1 (by omega)
    have h2 := range_check_len_limbs air row h_wf_assume h_enabled 2 (by omega)
    have h3 := range_check_len_limbs air row h_wf_assume h_enabled 3 (by omega)
    have hptr : (len_reg_ptr air row).val < OpenVM_address_space_size := by
      simpa using
        (len_reg_ptr_bound air row h_wf_assume h_enabled)
    simpa [_memoryBus_len_reg_pair] using
      memory_pair_wf
        (is_enabled air row) 1 (len_reg_ptr air row)
        (len_limb air 0 row) (len_limb air 1 row)
        (len_limb air 2 row) (len_limb air 3 row)
        (mem_aux_col air 6 row) (start_timestamp air row + 2)
        (Or.inr h_enabled)
        (fun _ => ⟨by decide, hptr, h0, h1, h2, h3⟩)
  have h_reg : propertiesToAssert (_memoryBus_reg_pairs air row) := by
    have h_input_len : propertiesToAssert
        (_memoryBus_input_reg_pair air row ++ _memoryBus_len_reg_pair air row) := by
      exact (propsAssert_append (_memoryBus_input_reg_pair air row)
        (_memoryBus_len_reg_pair air row)).2 ⟨h_input_reg, h_len_reg⟩
    simpa [_memoryBus_reg_pairs, List.append_assoc] using
      (propsAssert_append (_memoryBus_buffer_reg_pair air row)
        (_memoryBus_input_reg_pair air row ++ _memoryBus_len_reg_pair air row)).2
        ⟨h_buffer_reg, h_input_len⟩
  have h_preimage : propertiesToAssert (_memoryBus_preimage_pairs air row) := by
    apply propsAssert_flatMap_of_each
    intro j hj
    have hj_lt : j < 34 := List.mem_range.mp hj
    have hf :
        memoryBus_word_factor air row j = 0 ∨
        memoryBus_word_factor air row j = 1 := by
      rcases padding_byte_binary h_constraints j hj_lt with h_pad | h_pad
      · rw [memoryBus_word_factor, h_enabled, h_pad, sub_zero, mul_one]
        exact Or.inr rfl
      · rw [memoryBus_word_factor, h_enabled, h_pad]
        simp
    simpa [_memoryBus_preimage_pair] using
      memory_pair_wf
        (memoryBus_word_factor air row j) 2
        (buffer_ptr air row + (↑(4 * j) : FBB))
        (preimage_buffer_byte air (4 * j) row)
        (preimage_buffer_byte air (4 * j + 1) row)
        (preimage_buffer_byte air (4 * j + 2) row)
        (preimage_buffer_byte air (4 * j + 3) row)
        (mem_aux_col air (111 + 3 * j) row)
        (start_timestamp air row + 3 + cumulativePadSum air row j)
        hf
        (fun h_one => by
          have h_pad0 : is_padding_byte air j row = 0 := by
            rcases padding_byte_binary h_constraints j hj_lt with h_pad | h_pad
            · exact h_pad
            · rw [memoryBus_word_factor, h_enabled, h_pad] at h_one
              simp at h_one
          rcases active_preimage_word_bounds air row h_wf_assume h_enabled j hj_lt h_pad0 with
            ⟨hptr, hx0, hx1, hx2, hx3⟩
          exact ⟨by decide, by simpa using hptr,
            hx0, hx1, hx2, hx3⟩)
  have h_input : propertiesToAssert (_memoryBus_input_pairs air row) := by
    apply propsAssert_flatMap_of_each
    intro j hj
    have hj_lt : j < 34 := List.mem_range.mp hj
    have hf :
        memoryBus_word_factor air row j = 0 ∨
        memoryBus_word_factor air row j = 1 := by
      rcases padding_byte_binary h_constraints j hj_lt with h_pad | h_pad
      · rw [memoryBus_word_factor, h_enabled, h_pad, sub_zero, mul_one]
        exact Or.inr rfl
      · rw [memoryBus_word_factor, h_enabled, h_pad]
        simp
    simpa [_memoryBus_input_pair] using
      memory_pair_wf
        (memoryBus_word_factor air row j) 2
        (input_ptr air row + (↑(4 * j) : FBB))
        (input_byte air (4 * j) row)
        (input_byte air (4 * j + 1) row)
        (input_byte air (4 * j + 2) row)
        (input_byte air (4 * j + 3) row)
        (mem_aux_col air (9 + 3 * j) row)
        (start_timestamp air row + 3 + cumulativePadSum air row 34 +
          cumulativePadSum air row j)
        hf
        (fun h_one => by
          have h_pad0 : is_padding_byte air j row = 0 := by
            rcases padding_byte_binary h_constraints j hj_lt with h_pad | h_pad
            · exact h_pad
            · rw [memoryBus_word_factor, h_enabled, h_pad] at h_one
              simp at h_one
          rcases active_input_word_bounds air row h_wf_assume h_enabled j hj_lt h_pad0 with
            ⟨hptr, hx0, hx1, hx2, hx3⟩
          exact ⟨by decide, by simpa using hptr,
            hx0, hx1, hx2, hx3⟩)
  have h_postimage : propertiesToAssert (_memoryBus_postimage_pairs air row) := by
    apply propsAssert_flatMap_of_each
    intro j hj
    have hj_lt : j < 34 := List.mem_range.mp hj
    have hf :
        memoryBus_word_factor air row j = 0 ∨
        memoryBus_word_factor air row j = 1 := by
      rcases padding_byte_binary h_constraints j hj_lt with h_pad | h_pad
      · rw [memoryBus_word_factor, h_enabled, h_pad, sub_zero, mul_one]
        exact Or.inr rfl
      · rw [memoryBus_word_factor, h_enabled, h_pad]
        simp
    simpa [_memoryBus_postimage_pair] using
      memory_postimage_pair_wf
        (memoryBus_word_factor air row j)
        (buffer_ptr air row + (↑(4 * j) : FBB))
        (mem_aux_col air (216 + 7 * j) row)
        (mem_aux_col air (217 + 7 * j) row)
        (mem_aux_col air (218 + 7 * j) row)
        (mem_aux_col air (219 + 7 * j) row)
        (mem_aux_col air (213 + 7 * j) row)
        (postimage_buffer_byte air (4 * j) row)
        (postimage_buffer_byte air (4 * j + 1) row)
        (postimage_buffer_byte air (4 * j + 2) row)
        (postimage_buffer_byte air (4 * j + 3) row)
        (start_timestamp air row + 3 + 2 * cumulativePadSum air row 34 +
          cumulativePadSum air row j)
        hf
        (fun h_one => by
          have h_pad0 : is_padding_byte air j row = 0 := by
            rcases padding_byte_binary h_constraints j hj_lt with h_pad | h_pad
            · exact h_pad
            · rw [memoryBus_word_factor, h_enabled, h_pad] at h_one
              simp at h_one
          have hj_active : j < activeWords air row :=
            (active_word_iff_not_padding h_constraints h_enabled j hj_lt).mp h_pad0
          rcases active_postimage_word_bounds air row h_wf_assume h_enabled h_constraints j hj_active with
            ⟨hptr, hx0, hx1, hx2, hx3⟩
          exact ⟨by simpa using hptr, hx0, hx1, hx2, hx3⟩)
  have h_input_post : propertiesToAssert
      (_memoryBus_input_pairs air row ++ _memoryBus_postimage_pairs air row) := by
    exact (propsAssert_append (_memoryBus_input_pairs air row)
      (_memoryBus_postimage_pairs air row)).2 ⟨h_input, h_postimage⟩
  have h_tail : propertiesToAssert
      (_memoryBus_preimage_pairs air row ++
        (_memoryBus_input_pairs air row ++ _memoryBus_postimage_pairs air row)) := by
    exact (propsAssert_append (_memoryBus_preimage_pairs air row)
      (_memoryBus_input_pairs air row ++ _memoryBus_postimage_pairs air row)).2
      ⟨h_preimage, h_input_post⟩
  simpa [_memoryBus_row, List.append_assoc] using
    (propsAssert_append (_memoryBus_reg_pairs air row)
      (_memoryBus_preimage_pairs air row ++
        (_memoryBus_input_pairs air row ++ _memoryBus_postimage_pairs air row))).2
      ⟨h_reg, h_tail⟩

theorem wf_propertiesToAssert :
    (h_constraints : allHold_simplified air row h_row) →
    (h_enabled : is_enabled air row = 1) →
    (h_axioms : axiomsPerRow air row) →
    (h_wf_assume : wf_propertiesToAssumePerRow air row) →
    wf_propertiesToAssertPerRow air row
    := by
  intro h_constraints h_enabled h_axioms h_wf_assume
  exact ⟨execution_wf_propertiesToAssert air row,
    memory_wf_propertiesToAssert air row h_row h_constraints h_enabled h_axioms h_wf_assume,
    rangeChecker_wf_propertiesToAssert air row h_row h_constraints h_enabled,
    program_wf_propertiesToAssert air row h_enabled,
    bitwise_wf_propertiesToAssert air row h_row h_constraints h_enabled⟩

/-! ### Step 2: Essentials Bundle (structure) -/

/-- Intermediate bundle of all derived column properties for an enabled row.
    Includes PC/timestamp bounds, pointer/length decomposition, byte bounds,
    padding structure, XOR correctness, and spec-level timestamp formula. -/
structure Essentials (air : Valid_XorinVmAir FBB ExtF) (row : ℕ) : Prop where
  pc_bound : (pc air row).val < 2 ^ 30
  pc_aligned : (pc air row).val % 4 = 0
  ts_bound : (start_timestamp air row).val < 2 ^ 29
  buffer_ptr_eq_limbs :
    buffer_ptr air row =
      buffer_ptr_limb air 0 row + buffer_ptr_limb air 1 row * 256 +
      buffer_ptr_limb air 2 row * 65536 + buffer_ptr_limb air 3 row * 16777216
  input_ptr_eq_limbs :
    input_ptr air row =
      input_ptr_limb air 0 row + input_ptr_limb air 1 row * 256 +
      input_ptr_limb air 2 row * 65536 + input_ptr_limb air 3 row * 16777216
  len_eq_limbs :
    xorin_len air row =
      len_limb air 0 row + len_limb air 1 row * 256 +
      len_limb air 2 row * 65536 + len_limb air 3 row * 16777216
  buffer_ptr_bound : activeWords air row > 0 → (buffer_ptr air row).val < 2 ^ 29
  input_ptr_bound : activeWords air row > 0 → (input_ptr air row).val < 2 ^ 29
  len_bound : (xorin_len air row).val ≤ 136
  len_mod4 : (xorin_len air row).val % 4 = 0
  padding_binary : ∀ j, j < 34 →
    is_padding_byte air j row = 0 ∨ is_padding_byte air j row = 1
  active_word_iff : ∀ j, j < 34 →
    (is_padding_byte air j row = 0 ↔ j < activeWords air row)
  xor_correct : ∀ i, i < (xorin_len air row).val →
    (postimage_buffer_byte air i row).val =
      (preimage_buffer_byte air i row).val ^^^ (input_byte air i row).val
  preimage_bound : ∀ i, i < (xorin_len air row).val →
    (preimage_buffer_byte air i row).val < 256
  input_bound : ∀ i, i < (xorin_len air row).val →
    (input_byte air i row).val < 256
  postimage_bound : ∀ i, i < (xorin_len air row).val →
    (postimage_buffer_byte air i row).val < 256
  buffer_ptr_limb_bound : ∀ i, i < 4 → (buffer_ptr_limb air i row).val < 256
  input_ptr_limb_bound : ∀ i, i < 4 → (input_ptr_limb air i row).val < 256
  len_limb_bound : ∀ i, i < 4 → (len_limb air i row).val < 256
  cumPadSum_34_val : (cumulativePadSum air row 34).val = activeWords air row
  end_timestamp_spec :
    (execute_xorin_pure (xorinInputOfRow air row)).end_timestamp =
      (start_timestamp air row).val + 3 + 3 * activeWords air row

/-- Construct `Essentials` from row constraints, bus axioms, and wellformedness. -/
theorem essentials
    (h_constraints : allHold_simplified air row h_row)
    (h_enabled : is_enabled air row = 1)
    (h_axioms : axiomsPerRow air row)
    (h_wf_assume : wf_propertiesToAssumePerRow air row) :
    Essentials air row := by
  have h_bounds := execution_bus_bounds air row h_axioms h_enabled
  have h_aw_le := activeWords_le_34 h_constraints h_enabled
  have h_mod := xorin_len_mod_four h_constraints h_enabled
  have h_len := xorin_len_le_max h_constraints h_enabled
  have h_aw_def : activeWords air row = (xorin_len air row).val / 4 := rfl
  have h_xorin_eq : (xorin_len air row).val = activeWords air row * 4 := by omega
  exact {
    pc_bound := h_bounds.1
    pc_aligned := h_bounds.2.1
    ts_bound := h_bounds.2.2
    buffer_ptr_eq_limbs := buffer_ptr_eq_limbs h_constraints
    input_ptr_eq_limbs := input_ptr_eq_limbs h_constraints
    len_eq_limbs := xorin_len_eq_limbs h_constraints
    buffer_ptr_bound := fun h_aw => buffer_ptr_val_bound air row h_wf_assume h_enabled
      ((active_word_iff_not_padding h_constraints h_enabled 0 (by omega)).mpr (by omega))
    input_ptr_bound := fun h_aw => input_ptr_val_bound air row h_wf_assume h_enabled
      ((active_word_iff_not_padding h_constraints h_enabled 0 (by omega)).mpr (by omega))
    len_bound := h_len
    len_mod4 := h_mod
    padding_binary := fun j hj => padding_byte_binary h_constraints j hj
    active_word_iff := fun j hj => active_word_iff_not_padding h_constraints h_enabled j hj
    xor_correct := fun i hi => (bitwise_xor_at_byte air row h_wf_assume h_enabled i (by omega)
      ((active_word_iff_not_padding h_constraints h_enabled (i / 4) (by omega)).mpr (by omega))).2.2
    preimage_bound := fun i hi => (bitwise_xor_at_byte air row h_wf_assume h_enabled i (by omega)
      ((active_word_iff_not_padding h_constraints h_enabled (i / 4) (by omega)).mpr (by omega))).1
    input_bound := fun i hi => (bitwise_xor_at_byte air row h_wf_assume h_enabled i (by omega)
      ((active_word_iff_not_padding h_constraints h_enabled (i / 4) (by omega)).mpr (by omega))).2.1
    postimage_bound := fun i hi => by
      have h := bitwise_xor_at_byte air row h_wf_assume h_enabled i (by omega)
        ((active_word_iff_not_padding h_constraints h_enabled (i / 4) (by omega)).mpr (by omega))
      rw [h.2.2]; exact Nat.xor_lt_two_pow (n := 8) h.1 h.2.1
    buffer_ptr_limb_bound := range_check_buffer_ptr_limbs air row h_wf_assume h_enabled
    input_ptr_limb_bound := range_check_input_ptr_limbs air row h_wf_assume h_enabled
    len_limb_bound := range_check_len_limbs air row h_wf_assume h_enabled
    cumPadSum_34_val := cumulativePadSum_34_val_eq_activeWords h_constraints h_enabled
    end_timestamp_spec := by
      simp [execute_xorin_pure, xorinInputOfRow, activeWords, num_active_words]
  }

/-! ### Step 3: Row Contract (structure) -/

/-- Full per-row contract for an enabled XORIN row. Bundles bus-effect facts
    (execution send, memory reads/writes, bitwise XOR), inactive entry zeroing,
    spec-level postimage equality, and all bounds needed by callers. -/
structure XorinRowContract (air : Valid_XorinVmAir FBB ExtF) (row : ℕ) : Prop where
  exec_send : ExecutionSendFact air row
  bitwise_bytes : ∀ i, i < (xorin_len air row).val → BitwiseByteFact air row i
  preimage_reads : ∀ j, j < activeWords air row → PreimageReadFact air row j
  input_reads : ∀ j, j < activeWords air row → InputReadFact air row j
  postimage_writes : ∀ j, j < activeWords air row → PostimageWriteFact air row j
  inactive_preimage_reads_zero : ∀ j, j < 34 → j ≥ activeWords air row →
    (preimageReadEntry air row j).multiplicity = 0
  inactive_input_reads_zero : ∀ j, j < 34 → j ≥ activeWords air row →
    (inputReadEntry air row j).multiplicity = 0
  inactive_postimage_writes_zero : ∀ j, j < 34 → j ≥ activeWords air row →
    (postimageWriteEntry air row j).multiplicity = 0
  inactive_bitwise_zero : ∀ i, i < 136 → i / 4 ≥ activeWords air row →
    (bitwiseByteEntry air row i).multiplicity = 0
  spec_postimage : ∀ i, i < (xorin_len air row).val →
    (execute_xorin_pure (xorinInputOfRow air row)).postimage i =
      (postimage_buffer_byte air i row).val
  len_valid : (xorin_len air row).val ≤ 136 ∧ (xorin_len air row).val % 4 = 0
  pc_bound : (pc air row).val < 2 ^ 30
  pc_aligned : (pc air row).val % 4 = 0
  ts_bound : (start_timestamp air row).val < 2 ^ 29
  buffer_ptr_eq_limbs :
    buffer_ptr air row =
      buffer_ptr_limb air 0 row + buffer_ptr_limb air 1 row * 256 +
      buffer_ptr_limb air 2 row * 65536 + buffer_ptr_limb air 3 row * 16777216
  input_ptr_eq_limbs :
    input_ptr air row =
      input_ptr_limb air 0 row + input_ptr_limb air 1 row * 256 +
      input_ptr_limb air 2 row * 65536 + input_ptr_limb air 3 row * 16777216
  buffer_ptr_bound : activeWords air row > 0 → (buffer_ptr air row).val < 2 ^ 29
  input_ptr_bound : activeWords air row > 0 → (input_ptr air row).val < 2 ^ 29
  preimage_bound : ∀ i, i < (xorin_len air row).val →
    (preimage_buffer_byte air i row).val < 256
  input_bound : ∀ i, i < (xorin_len air row).val →
    (input_byte air i row).val < 256
  postimage_bound : ∀ i, i < (xorin_len air row).val →
    (postimage_buffer_byte air i row).val < 256

/-- Construct `XorinRowContract` for an enabled row from constraints and axioms. -/
theorem row_contract
    (h_constraints : allHold_simplified air row h_row)
    (h_enabled : is_enabled air row = 1)
    (h_axioms : axiomsPerRow air row)
    (h_wf_assume : wf_propertiesToAssumePerRow air row) :
    XorinRowContract air row := by
  have E := essentials air row h_row h_constraints h_enabled h_axioms h_wf_assume
  have h_aw_le := activeWords_le_34 h_constraints h_enabled
  exact {
    exec_send := execution_send_fact air row h_enabled h_axioms h_constraints
    bitwise_bytes := fun i hi => bitwise_byte_fact air row i hi h_wf_assume h_enabled h_constraints
    preimage_reads := fun j hj =>
      preimage_read_fact air row j hj h_wf_assume h_enabled h_axioms h_constraints
    input_reads := fun j hj =>
      input_read_fact air row j hj h_wf_assume h_enabled h_axioms h_constraints
    postimage_writes := fun j hj =>
      postimage_write_fact air row j hj h_wf_assume h_enabled h_axioms h_constraints
    inactive_preimage_reads_zero := fun j hj1 hj2 =>
      inactive_preimage_read_zero air row h_enabled j hj1
        ((inactive_word_iff_padding h_constraints h_enabled j hj1).mpr hj2)
    inactive_input_reads_zero := fun j hj1 hj2 =>
      inactive_input_read_zero air row h_enabled j hj1
        ((inactive_word_iff_padding h_constraints h_enabled j hj1).mpr hj2)
    inactive_postimage_writes_zero := fun j hj1 hj2 =>
      inactive_postimage_write_zero air row h_enabled j hj1
        ((inactive_word_iff_padding h_constraints h_enabled j hj1).mpr hj2)
    inactive_bitwise_zero := fun i hi1 hi2 =>
      inactive_bitwise_byte_zero air row h_enabled i hi1
        ((inactive_word_iff_padding h_constraints h_enabled (i / 4) (by omega)).mpr hi2)
    spec_postimage := fun i hi => by
      simpa [execute_xorin_pure, xorinInputOfRow, Xorin.Spec.xorBytesNat, hi] using
        (E.xor_correct i hi).symm
    len_valid := ⟨E.len_bound, E.len_mod4⟩
    pc_bound := E.pc_bound
    pc_aligned := E.pc_aligned
    ts_bound := E.ts_bound
    buffer_ptr_eq_limbs := E.buffer_ptr_eq_limbs
    input_ptr_eq_limbs := E.input_ptr_eq_limbs
    buffer_ptr_bound := E.buffer_ptr_bound
    input_ptr_bound := E.input_ptr_bound
    preimage_bound := E.preimage_bound
    input_bound := E.input_bound
    postimage_bound := E.postimage_bound
  }

end ValidRows

/-! ===== TOP-LEVEL ENTRY POINT ===== -/

/-- Per-row soundness of the XorinVmAir circuit. If the row is disabled, all bus
    multiplicities are zero. If enabled, the row satisfies `XorinRowContract`:
    correct bus effects, spec-level XOR execution, and all arithmetic bounds. -/
theorem xorin_row_soundness
    (air : Valid_XorinVmAir FBB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_simplified air row h_row)
    (h_axioms : axiomsPerRow air row)
    (h_wf_assume : wf_propertiesToAssumePerRow air row) :
    wf_propertiesToAssertPerRow air row
    ∧
    ((is_enabled air row = 0 ∧
      ∀ entry, entry ∈ busRow air row → entry.1 = 0) ∨
     (is_enabled air row = 1 ∧
      ValidRows.XorinRowContract air row)) := by
  have h_binary := is_enabled_binary h_constraints
  rcases h_binary with h_dis | h_en
  · -- Disabled case
    exact ⟨NonValidRows.wf_propertiesToAssert air row h_dis,
           Or.inl ⟨h_dis, NonValidRows.multiplicities_zero air row h_dis⟩⟩
  · -- Enabled case
    exact ⟨ValidRows.wf_propertiesToAssert air row h_row h_constraints h_en h_axioms h_wf_assume,
           Or.inr ⟨h_en, ValidRows.row_contract air row h_row h_constraints h_en h_axioms h_wf_assume⟩⟩

/-- Spec-facing corollary for an enabled XORIN row: the circuit's postimage bytes
    and end timestamp agree with the pure specification `execute_xorin_pure`. -/
theorem xorin_row_matches_spec
    (air : Valid_XorinVmAir FBB ExtF) (row : ℕ)
    (h_row : row ≤ air.last_row)
    (h_constraints : allHold_simplified air row h_row)
    (h_axioms : axiomsPerRow air row)
    (h_wf_assume : wf_propertiesToAssumePerRow air row)
    (h_enabled : is_enabled air row = 1) :
    (∀ i, i < (xorin_len air row).val →
      (execute_xorin_pure (xorinInputOfRow air row)).postimage i =
        (postimage_buffer_byte air i row).val)
    ∧
    (execute_xorin_pure (xorinInputOfRow air row)).end_timestamp =
      (start_timestamp air row).val + 3 + 3 * activeWords air row := by
  have h_contract :=
    ValidRows.row_contract air row h_row h_constraints h_enabled h_axioms h_wf_assume
  have h_essentials :=
    ValidRows.essentials air row h_row h_constraints h_enabled h_axioms h_wf_assume
  exact ⟨h_contract.spec_postimage, h_essentials.end_timestamp_spec⟩

end XorinVmAir.Soundness
