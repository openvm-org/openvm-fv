import VmExtensions.Constraints.KeccakfOpAirBus
import VmExtensions.Soundness.KeccakfOpAir.RowProperties
import VmExtensions.Soundness.KeccakfOpAir.FieldLemmas

set_option linter.all false
set_option maxHeartbeats 800000

namespace KeccakfOpAir.Soundness

open KeccakfOpAir.constraints
open KeccakfOpAir.Views

/-!
# Bus Facts for KeccakfOpAir

## Non-valid rows: multiplicities_zero
When is_valid = 0, every bus entry multiplicity is 0 because all multiplicities
factor through is_valid or -(is_valid).

## Valid rows: bus-derived bounds
When is_valid = 1, bus axioms give range bounds on decomposition limbs,
postimage byte bounds, and pointer limb bounds.
-/

variable {ExtF : Type} [Field ExtF]

/-! ### List.Forall extraction helpers -/

private lemma forall_id_map_get {α : Type} {f : α → Prop} {l : List α}
    (h : List.Forall id (l.map f)) {n : ℕ} (hn : n < l.length) :
    f (l[n]) := by
  induction l generalizing n with
  | nil => exact absurd hn (Nat.not_lt_zero _)
  | cons a t ih =>
      rw [List.map_cons, List.forall_cons] at h
      cases n with
      | zero => exact h.1
      | succ n => exact ih h.2 (Nat.lt_of_succ_lt_succ hn)

private lemma forall_get {α : Type} {p : α → Prop} {l : List α}
    (h : List.Forall p l) {n : ℕ} (hn : n < l.length) :
    p (l[n]) := by
  induction l generalizing n with
  | nil => exact absurd hn (Nat.not_lt_zero _)
  | cons a t ih =>
      rw [List.forall_cons] at h
      cases n with
      | zero => exact h.1
      | succ n => exact ih h.2 (Nat.lt_of_succ_lt_succ hn)

private lemma forall_flatMap_range50_pair_even
    {P Q : ℕ → Prop}
    (h : List.Forall id ((List.range 50).flatMap (fun a => [P a, Q a])))
    (j : ℕ) (hj : j < 50) :
    P j := by
  have hidx : 2 * j < ((List.range 50).flatMap (fun a => [P a, Q a])).length := by
    have hlen : ((List.range 50).flatMap (fun a => [P a, Q a])).length = 100 := by simp
    omega
  have hjth := forall_get h hidx
  revert hjth
  interval_cases j <;> intro hjth <;> simpa using hjth

private lemma forall_flatMap_range50_pair_odd
    {P Q : ℕ → Prop}
    (h : List.Forall id ((List.range 50).flatMap (fun a => [P a, Q a])))
    (j : ℕ) (hj : j < 50) :
    Q j := by
  have hidx : 2 * j + 1 < ((List.range 50).flatMap (fun a => [P a, Q a])).length := by
    have hlen : ((List.range 50).flatMap (fun a => [P a, Q a])).length = 100 := by simp
    omega
  have hjth := forall_get h hidx
  revert hjth
  interval_cases j <;> intro hjth <;> simpa using hjth

/-! ### Generic bus assumptions -> chip-specific bus facts -/

theorem range_check_assume
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_valid air row = 1) :
    RangeCheckAssume air row := by
  have pa_range := h_wf.2.2.2.1
  simp [propertiesToAssume, _rangeCheckerBus_row, _rangeCheckerBus_rd_pair,
    _rangeCheckerBus_buf_pair, h_en] at pa_range
  refine {
    rd_aux_lo_bound := ?_,
    rd_aux_hi_bound := ?_,
    buf_aux_lo_bound := ?_,
    buf_aux_hi_bound := ?_
  }
  · refine ⟨(rd_aux_lower_decomp_0 air row).val, by simp, ?_⟩
    exact pa_range.1
  · refine ⟨(rd_aux_lower_decomp_1 air row).val, by simp, ?_⟩
    exact pa_range.2.1
  · intro k hk
    have hkth :=
      forall_flatMap_range50_pair_even pa_range.2.2 k hk
    refine ⟨(buf_aux_lower_decomp_0 air row k).val, by simp, ?_⟩
    exact hkth
  · intro k hk
    have hkth :=
      forall_flatMap_range50_pair_odd pa_range.2.2 k hk
    refine ⟨(buf_aux_lower_decomp_1 air row k).val, by simp, ?_⟩
    exact hkth

theorem bitwise_assume
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_valid air row = 1) :
    BitwiseAssume air row := by
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_rd_pair, _memoryBus_buf_pair, h_en] at pa_mem
  have pa_bit := h_wf.2.2.2.2.1
  simp [propertiesToAssume, _bitwiseBus_row, _bitwiseBus_ptr_entry, h_en] at pa_bit
  refine {
    ptr_limb3_bound := ?_,
    postimage_byte_bound := ?_
  }
  · have hmul : (buffer_ptr_limb_3 air row * 8).val < 256 := pa_bit.1
    have h_limb_byte : (buffer_ptr_limb_3 air row).val < 256 := pa_mem.1.2.2.2.2
    have h8 : (8 : FBB).val = 8 := by native_decide
    have hmul_val :
        (buffer_ptr_limb_3 air row * 8).val =
          (buffer_ptr_limb_3 air row).val * 8 := by
      rw [fbb_val_mul (by rw [h8]; omega), h8]
    have hlt : (buffer_ptr_limb_3 air row).val < 32 := by
      rw [hmul_val] at hmul
      omega
    refine ⟨(buffer_ptr_limb_3 air row).val, ?_, ?_⟩
    · simp
    · simpa using hlt
  · intro k hk
    let j : ℕ := k / 2
    have hj : j < 100 := by
      dsimp [j]
      omega
    have hkth :=
      forall_get pa_bit.2 (n := j) (by simpa [j] using hj)
    have hbytes :
        (postimage air row (2 * j)).val < 256 ∧
        (postimage air row (2 * j + 1)).val < 256 := by
      have hprops := hkth h_en
      simpa [_bitwiseBus_postimage_entry, List.getElem_range, hj, j] using hprops
    have hk_mod : k % 2 = 0 ∨ k % 2 = 1 := by
      omega
    rcases hk_mod with h0 | h1
    · have hk' : k = 2 * j := by
        dsimp [j]
        omega
      refine ⟨(postimage air row k).val, by simp, ?_⟩
      rw [hk']
      exact hbytes.1
    · have hk' : k = 2 * j + 1 := by
        dsimp [j]
        omega
      refine ⟨(postimage air row k).val, by simp, ?_⟩
      rw [hk']
      exact hbytes.2

theorem memory_read_assume
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_valid air row = 1) :
    MemoryReadAssume air row := by
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_rd_pair, _memoryBus_buf_pair, h_en] at pa_mem
  refine {
    rd_ptr_bound := ?_,
    buf_limb_0_byte := ?_,
    buf_limb_1_byte := ?_,
    buf_limb_2_byte := ?_,
    buf_limb_3_byte := ?_,
    buf_ptr_k_bound := ?_,
    preimage_byte_bound := ?_
  }
  · exact pa_mem.1.1
  · exact pa_mem.1.2.1
  · exact pa_mem.1.2.2.1
  · exact pa_mem.1.2.2.2.1
  · exact pa_mem.1.2.2.2.2
  · intro k hk
    have hkth := forall_flatMap_range50_pair_even pa_mem.2 k hk
    have hpow : 2 ^ 29 = 536870912 := by native_decide
    simpa [hpow] using hkth.1
  · intro k hk
    let j : ℕ := k / 4
    have hj : j < 50 := by
      dsimp [j]
      omega
    have hkth := forall_flatMap_range50_pair_even pa_mem.2 j hj
    have hk_mod : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
      omega
    rcases hk_mod with h0 | h1 | h2 | h3
    · have hk' : k = 4 * j := by
        dsimp [j]
        omega
      rw [hk']
      exact hkth.2.1
    · have hk' : k = 4 * j + 1 := by
        dsimp [j]
        omega
      rw [hk']
      exact hkth.2.2.1
    · have hk' : k = 4 * j + 2 := by
        dsimp [j]
        omega
      rw [hk']
      exact hkth.2.2.2.1
    · have hk' : k = 4 * j + 3 := by
        dsimp [j]
        omega
      rw [hk']
      exact hkth.2.2.2.2

/-! ### Execution-bus bounds from axiomsPerRow -/

-- PC and timestamp bounds from execution bus axioms.
-- Entry 0 (mult = -(is_valid)): when is_valid = 1, mult = -1 ≠ 0, so axioms fire.
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 65536 in
theorem execution_bus_bounds
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h_axioms : axiomsPerRow air row)
    (h_en : is_valid air row = 1) :
    (pc air row).val < 2 ^ 30 ∧
    (pc air row).val % 4 = 0 ∧
    (timestamp air row).val < 2 ^ 29 := by
  have pa_exec := h_axioms.1
  simp [axioms, _executionBus_row, -List.map_nil, -List.attach_cons] at pa_exec
  rw [h_en] at pa_exec
  have h1 := pa_exec.1 (by decide)
  refine ⟨h1.1, ?_, h1.2.2⟩
  have h_mod := congr_arg Fin.val h1.2.1
  simpa using h_mod

-- Timestamp bound in terms of `timestampBound` (convenience wrapper).
theorem timestamp_bound
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h_axioms : axiomsPerRow air row)
    (h_en : is_valid air row = 1) :
    (timestamp air row).val < Keccakf.Interface.timestampBound :=
  (execution_bus_bounds air row h_axioms h_en).2.2

/-! ### Per-bus multiplicity zeroing lemmas -/

lemma executionBus_mults_zero (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    ∀ entry ∈ executionBus_row air row, entry.1 = 0 := by
  intro entry h
  simp only [executionBus_row, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl
  · simp [hen]
  · exact hen

lemma programBus_mults_zero (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    ∀ entry ∈ programBus_row air row, entry.1 = 0 := by
  intro entry h
  simp only [programBus_row, List.mem_cons, List.mem_nil_iff, or_false] at h
  subst h; exact hen

lemma memoryBus_mults_zero (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    ∀ entry ∈ memoryBus_row air row, entry.1 = 0 := by
  intro entry h
  simp only [memoryBus_row, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with (rfl | rfl) | h
  · simp [hen]
  · exact hen
  · rw [List.mem_flatMap] at h
    obtain ⟨k, _, hk⟩ := h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl
    · simp [hen]
    · exact hen

lemma rangeTupleCheckerBus_mults_zero (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    ∀ entry ∈ rangeTupleCheckerBus_row air row, entry.1 = 0 := by
  intro entry h
  simp only [rangeTupleCheckerBus_row, List.mem_append, List.mem_cons,
             List.mem_nil_iff, or_false] at h
  rcases h with (rfl | rfl) | h
  · exact hen
  · exact hen
  · rw [List.mem_flatMap] at h
    obtain ⟨k, _, hk⟩ := h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl
    · exact hen
    · exact hen

lemma bitwiseBus_mults_zero (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    ∀ entry ∈ bitwiseBus_row air row, entry.1 = 0 := by
  intro entry h
  simp only [bitwiseBus_row, List.mem_append, List.mem_cons,
             List.mem_nil_iff, or_false] at h
  rcases h with rfl | h
  · exact hen
  · rw [List.mem_map] at h
    obtain ⟨k, _, rfl⟩ := h
    exact hen

lemma keccakfStateBus_mults_zero (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    ∀ entry ∈ keccakfStateBus_row air row, entry.1 = 0 := by
  intro entry h
  rw [← keccakfStateBus_bridge air row] at h
  rw [serialiseToList, List.mem_map] at h
  obtain ⟨typed, htyped, rfl⟩ := h
  simp only [_keccakfStateBus_row, List.mem_cons, List.mem_nil_iff, or_false] at htyped
  rcases htyped with rfl | rfl
  · exact hen
  · exact hen

/-! ### Combined multiplicities_zero -/

-- When is_valid = 0, all bus entry multiplicities are 0
lemma multiplicities_zero (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    ∀ entry ∈ busRow air row, entry.1 = 0 := by
  intro entry h
  unfold busRow at h
  simp only [List.mem_append] at h
  -- busRow = exec ++ mem ++ prog ++ range ++ bitwise ++ keccak (left-associated ++)
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact executionBus_mults_zero air row hen entry h
  · exact memoryBus_mults_zero air row hen entry h
  · exact programBus_mults_zero air row hen entry h
  · exact rangeTupleCheckerBus_mults_zero air row hen entry h
  · exact bitwiseBus_mults_zero air row hen entry h
  · exact keccakfStateBus_mults_zero air row hen entry h

/-! ### wf_propertiesToAssertPerRow — disabled case

When is_valid = 0, all bus entry multiplicities are 0. Since assert conditions
check mult = 1 or mult = -1, and 0 ≠ 1, 0 ≠ -1 in FBB, all assert implications
are vacuously true. -/

-- Typed bus row multiplicity zeroing, analogous to the raw bus multiplicity lemmas.
private lemma _memoryBus_typed_mults_zero (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    ∀ entry ∈ _memoryBus_row air row, entry.1 = 0 := by
  intro entry h
  simp only [_memoryBus_row, List.mem_append] at h
  rcases h with h | h
  · simp only [_memoryBus_rd_pair, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl <;> simp [hen]
  · rw [List.mem_flatMap] at h; obtain ⟨k, _, hk⟩ := h
    simp only [_memoryBus_buf_pair, List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl <;> simp [hen]

private lemma _rangeCheckerBus_typed_mults_zero (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    ∀ entry ∈ _rangeCheckerBus_row air row, entry.1 = 0 := by
  intro entry h
  simp only [_rangeCheckerBus_row, List.mem_append] at h
  rcases h with h | h
  · simp only [_rangeCheckerBus_rd_pair, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl <;> exact hen
  · rw [List.mem_flatMap] at h; obtain ⟨k, _, hk⟩ := h
    simp only [_rangeCheckerBus_buf_pair, List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl <;> exact hen

private lemma _bitwiseBus_typed_mults_zero (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    ∀ entry ∈ _bitwiseBus_row air row, entry.1 = 0 := by
  intro entry h
  simp only [_bitwiseBus_row, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | h
  · exact hen
  · rw [List.mem_map] at h
    obtain ⟨k, _, rfl⟩ := h
    exact hen

private lemma keccakfStateBus_pre_wf_enabled
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 1) :
    ((_keccakfStateBus_pre_entry air row).payload[0] = 0 ∨
      (_keccakfStateBus_pre_entry air row).payload[0] = 1) ∧
      ∀ i : Fin 100, ↑(_keccakfStateBus_pre_entry air row).payload[↑i + 2] < 2 ^ 16 := by
  change
    ((Keccakf.constraints.msgToAssertEntry (preMsgOfColumns air row)).payload[0] = 0 ∨
      (Keccakf.constraints.msgToAssertEntry (preMsgOfColumns air row)).payload[0] = 1) ∧
      ∀ i : Fin 100,
        ↑(Keccakf.constraints.msgToAssertEntry (preMsgOfColumns air row)).payload[↑i + 2] < 2 ^ 16
  exact (Keccakf.constraints.wf_msgToAssertEntry (preMsgOfColumns air row)) rfl

private lemma keccakfStateBus_post_wf_enabled
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 1) :
    ((_keccakfStateBus_post_entry air row).payload[0] = 0 ∨
      (_keccakfStateBus_post_entry air row).payload[0] = 1) ∧
      ∀ i : Fin 100, ↑(_keccakfStateBus_post_entry air row).payload[↑i + 2] < 2 ^ 16 := by
  change
    ((Keccakf.constraints.msgToAssertEntry (postMsgOfColumns air row)).payload[0] = 0 ∨
      (Keccakf.constraints.msgToAssertEntry (postMsgOfColumns air row)).payload[0] = 1) ∧
      ∀ i : Fin 100,
        ↑(Keccakf.constraints.msgToAssertEntry (postMsgOfColumns air row)).payload[↑i + 2] < 2 ^ 16
  exact (Keccakf.constraints.wf_msgToAssertEntry (postMsgOfColumns air row)) rfl

-- Combined disabled case
lemma wf_assert_disabled (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 0) :
    wf_propertiesToAssertPerRow air row := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- ExecutionBus: assert_cond = (mult = 1), wf_properties = True → vacuous
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    simp only [_executionBus_row, List.mem_cons, List.mem_nil_iff, or_false] at h_entry
    rcases h_entry with rfl | rfl <;> (intro; trivial)
  -- MemoryBus: assert_cond = (mult = 1), all mults = 0
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    have h0 := _memoryBus_typed_mults_zero air row hen entry h_entry
    change entry.1 = 1 → _; intro hc; rw [h0] at hc; exact absurd hc fbb_zero_ne_one
  -- ProgramBus: assert_cond = (mult = -1), mult = is_valid = 0
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    simp only [_programBus_row, List.mem_cons, List.mem_nil_iff, or_false] at h_entry
    subst h_entry; change is_valid air row = -1 → _; rw [hen]
    intro hc; exact absurd hc fbb_zero_ne_neg_one
  -- RangeCheckerBus: assert_cond = (mult = -1), all mults = 0
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    have h0 := _rangeCheckerBus_typed_mults_zero air row hen entry h_entry
    change entry.1 = -1 → _; intro hc; rw [h0] at hc; exact absurd hc fbb_zero_ne_neg_one
  -- BitwiseBus: assert_cond = (mult = -1), all mults = 0
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    have h0 := _bitwiseBus_typed_mults_zero air row hen entry h_entry
    change entry.1 = -1 → _; intro hc; rw [h0] at hc; exact absurd hc fbb_zero_ne_neg_one
  -- KeccakfStateBus: assert_cond = (mult = 1), mults = is_valid = 0
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    simp only [_keccakfStateBus_row, List.mem_cons, List.mem_nil_iff, or_false] at h_entry
    rcases h_entry with rfl | rfl
    · change is_valid air row = 1 → _; rw [hen]
      intro hc; exact absurd hc fbb_zero_ne_one
    · change is_valid air row = 1 → _; rw [hen]
      intro hc; exact absurd hc fbb_zero_ne_one

/-! ### wf_propertiesToAssertPerRow — enabled case

When is_valid = 1, non-vacuous assert conditions are:
- MemoryBus writes (51 entries): as < 3, ptr < 2^29, data bytes < 256
- KeccakfStateBus (2 entries): flag binary, u16 limbs < 2^16

All other buses have assert_cond that checks the opposite multiplicity direction,
so their asserts are vacuously true. -/

set_option maxHeartbeats 1600000 in
lemma wf_assert_enabled (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (hen : is_valid air row = 1)
    (h_mem : MemoryReadAssume air row)
    (h_bw : BitwiseAssume air row) :
    wf_propertiesToAssertPerRow air row := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- ExecutionBus: wf_properties = True for all entries → trivial
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    simp only [_executionBus_row, List.mem_cons, List.mem_nil_iff, or_false] at h_entry
    rcases h_entry with rfl | rfl <;> (intro; trivial)
  -- MemoryBus: reads vacuous (mult=-1, assert checks =1), writes need wf from h_mem + h_bw
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    simp only [_memoryBus_row, List.mem_append] at h_entry
    rcases h_entry with h | h
    · -- rd pair
      simp only [_memoryBus_rd_pair, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl
      · -- rd read: mult = -(is_valid) = -1, assert_cond = (mult=1) → vacuous
        change -(is_valid air row) = 1 → _; rw [hen]
        intro hc; exact absurd hc fbb_neg_one_ne_one
      · -- rd write: mult = is_valid = 1, need wf_properties
        change is_valid air row = 1 → _; intro _
        exact ⟨by native_decide, h_mem.rd_ptr_bound, h_mem.buf_limb_0_byte,
               h_mem.buf_limb_1_byte, h_mem.buf_limb_2_byte, h_mem.buf_limb_3_byte⟩
    · -- buf pairs
      rw [List.mem_flatMap] at h; obtain ⟨k, hk_mem, hk⟩ := h
      rw [List.mem_range] at hk_mem
      simp only [_memoryBus_buf_pair, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl
      · -- buf read: mult = -(is_valid) = -1, vacuous
        change -(is_valid air row) = 1 → _; rw [hen]
        intro hc; exact absurd hc fbb_neg_one_ne_one
      · -- buf write: mult = is_valid = 1, need wf_properties
        change is_valid air row = 1 → _; intro _
        exact ⟨by native_decide, h_mem.buf_ptr_k_bound k hk_mem,
               fbb_val_lt_of_exists (h_bw.postimage_byte_bound (4*k) (by omega)) (by omega),
               fbb_val_lt_of_exists (h_bw.postimage_byte_bound (4*k+1) (by omega)) (by omega),
               fbb_val_lt_of_exists (h_bw.postimage_byte_bound (4*k+2) (by omega)) (by omega),
               fbb_val_lt_of_exists (h_bw.postimage_byte_bound (4*k+3) (by omega)) (by omega)⟩
  -- ProgramBus: assert_cond = (mult=-1), mult=is_valid=1, vacuous
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    simp only [_programBus_row, List.mem_cons, List.mem_nil_iff, or_false] at h_entry
    subst h_entry; change is_valid air row = -1 → _; rw [hen]
    intro hc; exact absurd hc fbb_one_ne_neg_one
  -- RangeCheckerBus: assert_cond = (mult=-1), all mults=is_valid=1, vacuous
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    simp only [_rangeCheckerBus_row, List.mem_append] at h_entry
    rcases h_entry with h | h
    · simp only [_rangeCheckerBus_rd_pair, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl
      · change is_valid air row = -1 → _; rw [hen]
        intro hc; exact absurd hc fbb_one_ne_neg_one
      · change is_valid air row = -1 → _; rw [hen]
        intro hc; exact absurd hc fbb_one_ne_neg_one
    · rw [List.mem_flatMap] at h; obtain ⟨k, _, hk⟩ := h
      simp only [_rangeCheckerBus_buf_pair, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl
      · change is_valid air row = -1 → _; rw [hen]
        intro hc; exact absurd hc fbb_one_ne_neg_one
      · change is_valid air row = -1 → _; rw [hen]
        intro hc; exact absurd hc fbb_one_ne_neg_one
  -- BitwiseBus: assert_cond = (mult=-1), all mults=is_valid=1, vacuous
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    simp only [_bitwiseBus_row, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h_entry
    rcases h_entry with rfl | h
    · change is_valid air row = -1 → _; rw [hen]
      intro hc; exact absurd hc fbb_one_ne_neg_one
    · rw [List.mem_map] at h; obtain ⟨k, _, rfl⟩ := h
      change is_valid air row = -1 → _; rw [hen]
      intro hc; exact absurd hc fbb_one_ne_neg_one
  -- KeccakfStateBus: need flag binary + limbs < 2^16
  · simp only [propertiesToAssert]; rw [List.forall_iff_forall_mem]
    intro p hp; rw [List.mem_map] at hp; obtain ⟨entry, h_entry, rfl⟩ := hp
    simp only [_keccakfStateBus_row, List.mem_cons, List.mem_nil_iff, or_false] at h_entry
    rcases h_entry with rfl | rfl
    · change is_valid air row = 1 → _; intro h_eq
      exact keccakfStateBus_pre_wf_enabled air row h_eq
    · change is_valid air row = 1 → _; intro h_eq
      exact keccakfStateBus_post_wf_enabled air row h_eq

end KeccakfOpAir.Soundness
