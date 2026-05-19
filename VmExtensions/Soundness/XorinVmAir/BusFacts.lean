/-
  Bus-derived facts for XorinVmAir soundness (FBB-specialized).

  Bridges raw bus assumptions (axiomsPerRow, wf_propertiesToAssumePerRow,
  wf_propertiesToAssertPerRow) to usable per-byte/per-entry facts.

  Bus-effect-centric: fact structures carry exact address, timestamp,
  and payload equalities at ℕ level.
-/
import VmExtensions.Soundness.XorinVmAir.RowProperties
import VmExtensions.Constraints.XorinVmAirBus
import OpenvmFv.Fundamentals.BabyBear
import OpenvmFv.Fundamentals.Interaction

set_option autoImplicit false
set_option linter.unusedVariables false

namespace XorinVmAir.Soundness.BusFacts

open XorinVmAir.constraints
open XorinVmAir.Soundness

variable {ExtF : Type} [Field ExtF]
variable (air : Valid_XorinVmAir FBB ExtF) (row : ℕ)

/-! ## Concrete Typed Bus Entries -/

noncomputable def executionSendEntry :
    Interaction.ExecutionBusEntry FBB where
  multiplicity := is_enabled air row
  pc := pc air row + 4
  timestamp := start_timestamp air row + 3 + 3 * cumulativePadSum air row 34

noncomputable def preimageReadEntry (j : ℕ) :
    Interaction.MemoryBusEntry FBB where
  multiplicity := is_enabled air row * (1 - is_padding_byte air j row)
  as := 2
  ptr := buffer_ptr air row + (↑(4 * j) : FBB)
  x0 := preimage_buffer_byte air (4 * j) row
  x1 := preimage_buffer_byte air (4 * j + 1) row
  x2 := preimage_buffer_byte air (4 * j + 2) row
  x3 := preimage_buffer_byte air (4 * j + 3) row
  timestamp := start_timestamp air row + 3 + cumulativePadSum air row j

noncomputable def inputReadEntry (j : ℕ) :
    Interaction.MemoryBusEntry FBB where
  multiplicity := is_enabled air row * (1 - is_padding_byte air j row)
  as := 2
  ptr := input_ptr air row + (↑(4 * j) : FBB)
  x0 := input_byte air (4 * j) row
  x1 := input_byte air (4 * j + 1) row
  x2 := input_byte air (4 * j + 2) row
  x3 := input_byte air (4 * j + 3) row
  timestamp := start_timestamp air row + 3 + cumulativePadSum air row 34 +
    cumulativePadSum air row j

noncomputable def postimageWriteEntry (j : ℕ) :
    Interaction.MemoryBusEntry FBB where
  multiplicity := is_enabled air row * (1 - is_padding_byte air j row)
  as := 2
  ptr := buffer_ptr air row + (↑(4 * j) : FBB)
  x0 := postimage_buffer_byte air (4 * j) row
  x1 := postimage_buffer_byte air (4 * j + 1) row
  x2 := postimage_buffer_byte air (4 * j + 2) row
  x3 := postimage_buffer_byte air (4 * j + 3) row
  timestamp := start_timestamp air row + 3 + 2 * cumulativePadSum air row 34 +
    cumulativePadSum air row j

noncomputable def bitwiseByteEntry (i : ℕ) :
    Interaction.BitwiseBusEntry FBB where
  multiplicity := is_enabled air row * (1 - is_padding_byte air (i / 4) row)
  a := preimage_buffer_byte air i row
  b := input_byte air i row
  c := postimage_buffer_byte air i row
  op := 1

/-! ## List.Forall extraction helper -/

-- Extract a specific entry's property from List.Forall id (list.map f)
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

private lemma forall_flatMap_range34_pair_even
    {P Q : ℕ → Prop}
    (h : List.Forall id ((List.range 34).flatMap (fun a => [P a, Q a])))
    (j : ℕ) (hj : j < 34) :
    P j := by
  have hidx : 2 * j < ((List.range 34).flatMap (fun a => [P a, Q a])).length := by
    have hlen : ((List.range 34).flatMap (fun a => [P a, Q a])).length = 68 := by simp
    omega
  have hjth := forall_get h hidx
  revert hjth
  interval_cases j <;> intro hjth <;> simpa using hjth

private lemma forall_flatMap_range34_pair_odd
    {P Q : ℕ → Prop}
    (h : List.Forall id ((List.range 34).flatMap (fun a => [P a, Q a])))
    (j : ℕ) (hj : j < 34) :
    Q j := by
  have hidx : 2 * j + 1 < ((List.range 34).flatMap (fun a => [P a, Q a])).length := by
    have hlen : ((List.range 34).flatMap (fun a => [P a, Q a])).length = 68 := by simp
    omega
  have hjth := forall_get h hidx
  revert hjth
  interval_cases j <;> intro hjth <;> simpa using hjth

/-! ## Execution Bus Facts -/

-- PC and timestamp bounds from execution bus axioms
set_option maxHeartbeats 40000000 in
set_option maxRecDepth 65536 in
theorem execution_bus_bounds
    (h_axioms : axiomsPerRow air row)
    (h_en : is_enabled air row = 1) :
    (pc air row).val < 2 ^ 30 ∧
    (pc air row).val % 4 = 0 ∧
    (start_timestamp air row).val < 2 ^ 29 := by
  have pa_exec := h_axioms.1
  simp [axioms, XorinVmAir_constraint_and_interaction_simplification, executionBus_row,
    -List.map_nil, -List.attach_cons] at pa_exec
  unfold Interaction.ExecutionBusEntry.deserialise at pa_exec
  dsimp [List.attach] at pa_exec
  rw [h_en] at pa_exec
  have h1 := pa_exec.1 (by decide)
  refine ⟨h1.1, ?_, h1.2.2⟩
  have h_mod := congr_arg Fin.val h1.2.1
  simpa using h_mod

/-! ## Memory Bus wf_assume-Derived Bounds -/

-- Helper: extract entry from List.Forall on bus row by index, using `change` for efficiency.
-- The kernel evaluator handles list indexing much faster than simp.

-- Entry 0: buffer_reg_ptr recv → buffer_ptr_limb bounds
set_option maxHeartbeats 4000000 in
theorem range_check_buffer_ptr_limbs
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1) :
    ∀ i, i < 4 → (buffer_ptr_limb air i row).val < 256 := by
  intro i hi
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_reg_pairs,
    _memoryBus_buffer_reg_pair, _memoryBus_input_reg_pair, _memoryBus_len_reg_pair, h_en] at pa_mem
  have h0 := pa_mem.1 (by decide)
  rcases h0 with ⟨_, hx0, hx1, hx2, hx3⟩
  interval_cases i <;> simp_all

theorem buffer_reg_ptr_bound
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1) :
    (buffer_reg_ptr air row).val < 2 ^ 29 := by
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_reg_pairs,
    _memoryBus_buffer_reg_pair, _memoryBus_input_reg_pair, _memoryBus_len_reg_pair, h_en] at pa_mem
  exact (pa_mem.1 (by decide)).1

-- Entry 2: input_reg_ptr recv → input_ptr_limb bounds
set_option maxHeartbeats 4000000 in
theorem range_check_input_ptr_limbs
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1) :
    ∀ i, i < 4 → (input_ptr_limb air i row).val < 256 := by
  intro i hi
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_reg_pairs,
    _memoryBus_buffer_reg_pair, _memoryBus_input_reg_pair, _memoryBus_len_reg_pair, h_en] at pa_mem
  have h0 := pa_mem.2.1 (by decide)
  rcases h0 with ⟨_, hx0, hx1, hx2, hx3⟩
  interval_cases i <;> simp_all

theorem input_reg_ptr_bound
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1) :
    (input_reg_ptr air row).val < 2 ^ 29 := by
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_reg_pairs,
    _memoryBus_buffer_reg_pair, _memoryBus_input_reg_pair, _memoryBus_len_reg_pair, h_en] at pa_mem
  exact (pa_mem.2.1 (by decide)).1

-- Entry 4: len_reg_ptr recv → len_limb bounds
set_option maxHeartbeats 4000000 in
theorem range_check_len_limbs
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1) :
    ∀ i, i < 4 → (len_limb air i row).val < 256 := by
  intro i hi
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_reg_pairs,
    _memoryBus_buffer_reg_pair, _memoryBus_input_reg_pair, _memoryBus_len_reg_pair, h_en] at pa_mem
  have h0 := pa_mem.2.2.1 (by decide)
  rcases h0 with ⟨_, hx0, hx1, hx2, hx3⟩
  interval_cases i <;> simp_all

theorem len_reg_ptr_bound
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1) :
    (len_reg_ptr air row).val < 2 ^ 29 := by
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_reg_pairs,
    _memoryBus_buffer_reg_pair, _memoryBus_input_reg_pair, _memoryBus_len_reg_pair, h_en] at pa_mem
  exact (pa_mem.2.2.1 (by decide)).1

-- Entry 6: preimage word 0 recv → buffer_ptr.val < 2^29
set_option maxHeartbeats 4000000 in
theorem buffer_ptr_val_bound
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    (h_active_0 : is_padding_byte air 0 row = 0) :
    (buffer_ptr air row).val < 2 ^ 29 := by
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_reg_pairs,
    _memoryBus_buffer_reg_pair, _memoryBus_input_reg_pair, _memoryBus_len_reg_pair,
    _memoryBus_preimage_pairs, _memoryBus_preimage_pair, h_en] at pa_mem
  have pa_pre := pa_mem.2.2.2.1
  have hidx : 0 < (List.flatMap
      (fun a =>
        [2013265920 * memoryBus_word_factor air row a = -1 →
            ↑(buffer_ptr air row + 4 * ↑a) < 536870912 ∧
              ↑(preimage_buffer_byte air (4 * a) row) < 256 ∧
                ↑(preimage_buffer_byte air (4 * a + 1) row) < 256 ∧
                  ↑(preimage_buffer_byte air (4 * a + 2) row) < 256 ∧
                    ↑(preimage_buffer_byte air (4 * a + 3) row) < 256,
          memoryBus_word_factor air row a = -1 →
            ↑(buffer_ptr air row + 4 * ↑a) < 536870912 ∧
              ↑(preimage_buffer_byte air (4 * a) row) < 256 ∧
                ↑(preimage_buffer_byte air (4 * a + 1) row) < 256 ∧
                  ↑(preimage_buffer_byte air (4 * a + 2) row) < 256 ∧
                    ↑(preimage_buffer_byte air (4 * a + 3) row) < 256])
      (List.range 34)).length := by
    simp
  have h0 := forall_get pa_pre hidx
  have hmul : 2013265920 * memoryBus_word_factor air row 0 = 2013265920 := by
    simp [memoryBus_word_factor, h_en, h_active_0]
  have hwf := h0 hmul
  simpa using hwf.1

-- Entry 74: input word 0 recv → input_ptr.val < 2^29
set_option maxHeartbeats 8000000 in
theorem input_ptr_val_bound
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    (h_active_0 : is_padding_byte air 0 row = 0) :
    (input_ptr air row).val < 2 ^ 29 := by
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_reg_pairs,
    _memoryBus_buffer_reg_pair, _memoryBus_input_reg_pair, _memoryBus_len_reg_pair,
    _memoryBus_input_pairs, _memoryBus_input_pair, h_en] at pa_mem
  have pa_input := pa_mem.2.2.2.2.1
  have hidx : 0 < (List.flatMap
      (fun a =>
        [2013265920 * memoryBus_word_factor air row a = -1 →
            ↑(input_ptr air row + 4 * ↑a) < 536870912 ∧
              ↑(input_byte air (4 * a) row) < 256 ∧
                ↑(input_byte air (4 * a + 1) row) < 256 ∧
                  ↑(input_byte air (4 * a + 2) row) < 256 ∧ ↑(input_byte air (4 * a + 3) row) < 256,
          memoryBus_word_factor air row a = -1 →
            ↑(input_ptr air row + 4 * ↑a) < 536870912 ∧
              ↑(input_byte air (4 * a) row) < 256 ∧
                ↑(input_byte air (4 * a + 1) row) < 256 ∧
                  ↑(input_byte air (4 * a + 2) row) < 256 ∧ ↑(input_byte air (4 * a + 3) row) < 256])
      (List.range 34)).length := by
    simp
  have h0 := forall_get pa_input hidx
  have hmul : 2013265920 * memoryBus_word_factor air row 0 = 2013265920 := by
    simp [memoryBus_word_factor, h_en, h_active_0]
  have hwf := h0 hmul
  simpa using hwf.1

set_option maxHeartbeats 64000000 in
theorem active_preimage_word_bounds
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    (j : ℕ) (hj : j < 34)
    (h_active : is_padding_byte air j row = 0) :
    (buffer_ptr air row + (↑(4 * j) : FBB)).val < 2 ^ 29 ∧
    (preimage_buffer_byte air (4 * j) row).val < 256 ∧
    (preimage_buffer_byte air (4 * j + 1) row).val < 256 ∧
    (preimage_buffer_byte air (4 * j + 2) row).val < 256 ∧
    (preimage_buffer_byte air (4 * j + 3) row).val < 256 := by
  let P : ℕ → Prop := fun a =>
    2013265920 * memoryBus_word_factor air row a = -1 →
      ↑(buffer_ptr air row + 4 * ↑a) < 536870912 ∧
        ↑(preimage_buffer_byte air (4 * a) row) < 256 ∧
          ↑(preimage_buffer_byte air (4 * a + 1) row) < 256 ∧
            ↑(preimage_buffer_byte air (4 * a + 2) row) < 256 ∧
              ↑(preimage_buffer_byte air (4 * a + 3) row) < 256
  let Q : ℕ → Prop := fun a =>
    memoryBus_word_factor air row a = -1 →
      ↑(buffer_ptr air row + 4 * ↑a) < 536870912 ∧
        ↑(preimage_buffer_byte air (4 * a) row) < 256 ∧
          ↑(preimage_buffer_byte air (4 * a + 1) row) < 256 ∧
            ↑(preimage_buffer_byte air (4 * a + 2) row) < 256 ∧
              ↑(preimage_buffer_byte air (4 * a + 3) row) < 256
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_reg_pairs,
    _memoryBus_buffer_reg_pair, _memoryBus_input_reg_pair, _memoryBus_len_reg_pair,
    _memoryBus_preimage_pairs, _memoryBus_preimage_pair, h_en] at pa_mem
  have hrecv : P j := forall_flatMap_range34_pair_even pa_mem.2.2.2.1 j hj
  have hmul : 2013265920 * memoryBus_word_factor air row j = 2013265920 := by
    simp [memoryBus_word_factor, h_en, h_active]
  have hwf := hrecv hmul
  have hpow : 2 ^ 29 = 536870912 := by decide
  simpa [hpow, P] using hwf

set_option maxHeartbeats 64000000 in
theorem active_input_word_bounds
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    (j : ℕ) (hj : j < 34)
    (h_active : is_padding_byte air j row = 0) :
    (input_ptr air row + (↑(4 * j) : FBB)).val < 2 ^ 29 ∧
    (input_byte air (4 * j) row).val < 256 ∧
    (input_byte air (4 * j + 1) row).val < 256 ∧
    (input_byte air (4 * j + 2) row).val < 256 ∧
    (input_byte air (4 * j + 3) row).val < 256 := by
  let P : ℕ → Prop := fun a =>
    2013265920 * memoryBus_word_factor air row a = -1 →
      ↑(input_ptr air row + 4 * ↑a) < 536870912 ∧
        ↑(input_byte air (4 * a) row) < 256 ∧
          ↑(input_byte air (4 * a + 1) row) < 256 ∧
            ↑(input_byte air (4 * a + 2) row) < 256 ∧
              ↑(input_byte air (4 * a + 3) row) < 256
  let Q : ℕ → Prop := fun a =>
    memoryBus_word_factor air row a = -1 →
      ↑(input_ptr air row + 4 * ↑a) < 536870912 ∧
        ↑(input_byte air (4 * a) row) < 256 ∧
          ↑(input_byte air (4 * a + 1) row) < 256 ∧
            ↑(input_byte air (4 * a + 2) row) < 256 ∧
              ↑(input_byte air (4 * a + 3) row) < 256
  have pa_mem := h_wf.2.1
  simp [propertiesToAssume, _memoryBus_row, _memoryBus_reg_pairs,
    _memoryBus_buffer_reg_pair, _memoryBus_input_reg_pair, _memoryBus_len_reg_pair,
    _memoryBus_input_pairs, _memoryBus_input_pair, h_en] at pa_mem
  have hrecv : P j := forall_flatMap_range34_pair_even pa_mem.2.2.2.2.1 j hj
  have hmul : 2013265920 * memoryBus_word_factor air row j = 2013265920 := by
    simp [memoryBus_word_factor, h_en, h_active]
  have hwf := hrecv hmul
  have hpow : 2 ^ 29 = 536870912 := by decide
  simpa [hpow, P] using hwf

/-! ## Bitwise Bus Facts -/

set_option maxHeartbeats 800000000 in
set_option maxRecDepth 8192 in
/-- Per-byte XOR correctness: for active byte `i`, preimage and input are < 256
    and postimage = preimage XOR input. Derived from bitwise bus wellformedness. -/
theorem bitwise_xor_at_byte
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    (i : ℕ) (hi : i < 136)
    (h_active : is_padding_byte air (i / 4) row = 0) :
    (preimage_buffer_byte air i row).val < 256 ∧
    (input_byte air i row).val < 256 ∧
    (postimage_buffer_byte air i row).val =
      (preimage_buffer_byte air i row).val ^^^ (input_byte air i row).val := by
  have pa_bit := h_wf.2.2.2.2
  simp only [propertiesToAssume] at pa_bit
  have hidx : i + 2 < (_bitwiseBus_row air row).length := by
    rw [_bitwiseBus_row_length]
    omega
  have h := forall_id_map_get pa_bit hidx
  rw [getElem__bitwiseBus_row_active air row i hi hidx] at h
  simp [Interaction.BusEntry.assume, _bitwiseBus_active_byte, h_en, h_active, sub_zero] at h
  simpa using h

theorem active_byte_postimage_bound
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    (i : ℕ) (hi : i < 136)
    (h_active : is_padding_byte air (i / 4) row = 0) :
    (postimage_buffer_byte air i row).val < 256 := by
  have h := bitwise_xor_at_byte air row h_wf h_en i hi h_active
  rw [h.2.2]
  exact Nat.xor_lt_two_pow (n := 8) h.1 h.2.1

theorem active_postimage_word_bounds
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    {h_row : row ≤ air.last_row} (h_constraints : allHold_simplified air row h_row)
    (j : ℕ) (hj : j < activeWords air row) :
    (buffer_ptr air row + (↑(4 * j) : FBB)).val < 2 ^ 29 ∧
    (postimage_buffer_byte air (4 * j) row).val < 256 ∧
    (postimage_buffer_byte air (4 * j + 1) row).val < 256 ∧
    (postimage_buffer_byte air (4 * j + 2) row).val < 256 ∧
    (postimage_buffer_byte air (4 * j + 3) row).val < 256 := by
  have h_aw_le := activeWords_le_34 h_constraints h_en
  have h_active : is_padding_byte air j row = 0 :=
    (active_word_iff_not_padding h_constraints h_en j (by omega)).mpr hj
  have h_active0 : is_padding_byte air 0 row = 0 :=
    (active_word_iff_not_padding h_constraints h_en 0 (by omega)).mpr (by omega)
  have h_pre := active_preimage_word_bounds air row h_wf h_en j (by omega) h_active
  have h0_div : (4 * j) / 4 = j := by omega
  have h1_div : (4 * j + 1) / 4 = j := by omega
  have h2_div : (4 * j + 2) / 4 = j := by omega
  have h3_div : (4 * j + 3) / 4 = j := by omega
  have hb0 := active_byte_postimage_bound air row h_wf h_en (4 * j) (by omega) (by simpa [h0_div] using h_active)
  have hb1 := active_byte_postimage_bound air row h_wf h_en (4 * j + 1) (by omega) (by simpa [h1_div] using h_active)
  have hb2 := active_byte_postimage_bound air row h_wf h_en (4 * j + 2) (by omega) (by simpa [h2_div] using h_active)
  have hb3 := active_byte_postimage_bound air row h_wf h_en (4 * j + 3) (by omega) (by simpa [h3_div] using h_active)
  exact ⟨h_pre.1, hb0, hb1, hb2, hb3⟩

/-! ## Simplified Bus-Effect Fact Structures

These structures capture the essential properties from bus interactions without
requiring `in_row` membership proofs on large typed bus rows. The bus interaction
correctness is enforced by the logup argument (proved separately).
-/

/-- Execution bus send: multiplicity is 1, PC advances by 4, timestamp advances correctly. -/
structure ExecutionSendFact (air : Valid_XorinVmAir FBB ExtF) (row : ℕ) : Prop where
  multiplicity_one : (executionSendEntry air row).multiplicity = 1
  next_pc_val : (pc air row + 4).val = (pc air row).val + 4
  end_ts_val :
    (start_timestamp air row + 3 + 3 * cumulativePadSum air row 34).val =
      (start_timestamp air row).val + 3 + 3 * activeWords air row

/-- Memory read of preimage word `j`: multiplicity 1, address = buffer_ptr + 4j. -/
structure PreimageReadFact (air : Valid_XorinVmAir FBB ExtF) (row j : ℕ) : Prop where
  multiplicity_one : is_enabled air row * (1 - is_padding_byte air j row) = 1
  addr_val : (buffer_ptr air row + (↑(4 * j) : FBB)).val =
    (buffer_ptr air row).val + 4 * j
  timestamp_val :
    (start_timestamp air row + 3 + cumulativePadSum air row j).val =
      (start_timestamp air row).val + 3 + j

/-- Memory read of input word `j`: multiplicity 1, address = input_ptr + 4j. -/
structure InputReadFact (air : Valid_XorinVmAir FBB ExtF) (row j : ℕ) : Prop where
  multiplicity_one : is_enabled air row * (1 - is_padding_byte air j row) = 1
  addr_val : (input_ptr air row + (↑(4 * j) : FBB)).val =
    (input_ptr air row).val + 4 * j
  timestamp_val :
    (start_timestamp air row + 3 + cumulativePadSum air row 34 +
      cumulativePadSum air row j).val =
      (start_timestamp air row).val + 3 + activeWords air row + j

/-- Memory write of postimage word `j`: multiplicity 1, address = buffer_ptr + 4j,
    each byte is preimage XOR input. -/
structure PostimageWriteFact (air : Valid_XorinVmAir FBB ExtF) (row j : ℕ) : Prop where
  multiplicity_one : is_enabled air row * (1 - is_padding_byte air j row) = 1
  addr_val : (buffer_ptr air row + (↑(4 * j) : FBB)).val =
    (buffer_ptr air row).val + 4 * j
  timestamp_val :
    (start_timestamp air row + 3 + 2 * cumulativePadSum air row 34 +
      cumulativePadSum air row j).val =
      (start_timestamp air row).val + 3 + 2 * activeWords air row + j
  xor_correct : ∀ k, k < 4 →
    (postimage_buffer_byte air (4 * j + k) row).val =
      (preimage_buffer_byte air (4 * j + k) row).val ^^^
      (input_byte air (4 * j + k) row).val

/-- Bitwise XOR for byte `i`: multiplicity 1, both operands < 256, result is XOR. -/
structure BitwiseByteFact (air : Valid_XorinVmAir FBB ExtF) (row i : ℕ) : Prop where
  multiplicity_one : is_enabled air row * (1 - is_padding_byte air (i / 4) row) = 1
  a_bound : (preimage_buffer_byte air i row).val < 256
  b_bound : (input_byte air i row).val < 256
  xor_correct :
    (postimage_buffer_byte air i row).val =
      (preimage_buffer_byte air i row).val ^^^ (input_byte air i row).val

/-! ## Fact-Producing Theorems -/

theorem execution_send_fact
    (h_en : is_enabled air row = 1)
    (h_axioms : axiomsPerRow air row)
    {h_row : row ≤ air.last_row} (h_constraints : allHold_simplified air row h_row) :
    ExecutionSendFact air row := by
  have h_bounds := execution_bus_bounds air row h_axioms h_en
  have h_aw_le := activeWords_le_34 h_constraints h_en
  have h_cps34 := cumulativePadSum_34_val_eq_activeWords h_constraints h_en
  have h_cps34_le := cPS_val_le h_constraints 34 (le_refl _)
  refine ⟨?_, ?_, ?_⟩
  · -- multiplicity_one: is_enabled = 1 by h_en
    exact h_en
  · -- next_pc_val: (pc + 4).val = pc.val + 4
    exact fbb_val_add (by omega)
  · -- end_ts_val: (ts + 3 + 3*cPS(34)).val = ts.val + 3 + 3*activeWords
    have h3 : (3 : FBB).val = 3 := by decide
    have h_3cps : (3 * cumulativePadSum air row 34).val = 3 * (cumulativePadSum air row 34).val :=
      fbb_val_mul (by rw [h3]; omega)
    have h1 : (start_timestamp air row + 3).val = (start_timestamp air row).val + 3 :=
      fbb_val_add (by omega)
    have h2 : (start_timestamp air row + 3 + 3 * cumulativePadSum air row 34).val =
        (start_timestamp air row).val + 3 + 3 * (cumulativePadSum air row 34).val := by
      rw [fbb_val_add (by rw [h1, h_3cps]; omega), h1, h_3cps]
    rw [h2, h_cps34]

/-! ## Inactive Word Absence -/

-- When pad[j] = 1, the memory bus multiplicity for word j is 0
theorem inactive_word_multiplicity_zero
    (h_en : is_enabled air row = 1)
    (j : ℕ) (hj : j < 34) (h_pad : is_padding_byte air j row = 1) :
    is_enabled air row * (1 - is_padding_byte air j row) = 0 := by
  rw [h_pad, sub_self, mul_zero]

theorem inactive_preimage_read_zero
    (h_en : is_enabled air row = 1)
    (j : ℕ) (hj : j < 34) (h_pad : is_padding_byte air j row = 1) :
    (preimageReadEntry air row j).multiplicity = 0 := by
  exact inactive_word_multiplicity_zero air row h_en j hj h_pad

theorem inactive_input_read_zero
    (h_en : is_enabled air row = 1)
    (j : ℕ) (hj : j < 34) (h_pad : is_padding_byte air j row = 1) :
    (inputReadEntry air row j).multiplicity = 0 := by
  exact inactive_word_multiplicity_zero air row h_en j hj h_pad

theorem inactive_postimage_write_zero
    (h_en : is_enabled air row = 1)
    (j : ℕ) (hj : j < 34) (h_pad : is_padding_byte air j row = 1) :
    (postimageWriteEntry air row j).multiplicity = 0 := by
  exact inactive_word_multiplicity_zero air row h_en j hj h_pad

theorem inactive_bitwise_byte_zero
    (h_en : is_enabled air row = 1)
    (i : ℕ) (hi : i < 136)
    (h_pad : is_padding_byte air (i / 4) row = 1) :
    (bitwiseByteEntry air row i).multiplicity = 0 := by
  rw [bitwiseByteEntry, h_en, h_pad, sub_self, mul_zero]

/-! ## Timestamp Bridge Theorems -/

-- For active word j, the FBB cumulative sum collapses to j at ℕ level.
theorem preimage_read_timestamp_val (j : ℕ) (hj : j < activeWords air row)
    (h_en : is_enabled air row = 1)
    (h_axioms : axiomsPerRow air row)
    {h_row : row ≤ air.last_row} (h_constraints : allHold_simplified air row h_row) :
    (start_timestamp air row + 3 + cumulativePadSum air row j).val =
      (start_timestamp air row).val + 3 + j := by
  -- j < activeWords → all k < j have pad[k] = 0 → cPS(j) = (j : FBB)
  have h_aw_le := activeWords_le_34 h_constraints h_en
  have h_prefix : ∀ k, k < j → is_padding_byte air k row = 0 := by
    intro k hk
    exact (active_word_iff_not_padding h_constraints h_en k (by omega)).mpr (by omega)
  have h_cps := cumulative_pad_sum_for_active_prefix j (by omega) h_prefix
  rw [h_cps]
  -- Now need: (ts + 3 + (j : FBB)).val = ts.val + 3 + j
  -- ts.val < 2^29, j ≤ 33, so total < 2^29 + 36 < p
  have h_bounds := execution_bus_bounds air row h_axioms h_en
  have h_ts := h_bounds.2.2
  have h_j_cast : (j : FBB).val = j := fbb_val_natCast (by omega)
  have h3 : (3 : FBB).val = 3 := by decide
  -- ts + 3
  have h_add1 : (start_timestamp air row + 3).val =
      (start_timestamp air row).val + 3 := by
    apply fbb_val_add; omega
  -- (ts + 3) + j
  have h_add2 : (start_timestamp air row + 3 + (j : FBB)).val =
      (start_timestamp air row).val + 3 + j := by
    rw [fbb_val_add (by rw [h_add1, h_j_cast]; omega), h_add1, h_j_cast]
  exact h_add2

theorem input_read_timestamp_val (j : ℕ) (hj : j < activeWords air row)
    (h_en : is_enabled air row = 1)
    (h_axioms : axiomsPerRow air row)
    {h_row : row ≤ air.last_row} (h_constraints : allHold_simplified air row h_row) :
    (start_timestamp air row + 3 + cumulativePadSum air row 34 +
      cumulativePadSum air row j).val =
      (start_timestamp air row).val + 3 + activeWords air row + j := by
  have h_aw_le := activeWords_le_34 h_constraints h_en
  have h_bounds := execution_bus_bounds air row h_axioms h_en
  have h_ts := h_bounds.2.2
  -- cPS(34).val = activeWords
  have h_cps34 := cumulativePadSum_34_val_eq_activeWords h_constraints h_en
  -- cPS(j) = (j : FBB) for active j
  have h_prefix : ∀ k, k < j → is_padding_byte air k row = 0 := by
    intro k hk
    exact (active_word_iff_not_padding h_constraints h_en k (by omega)).mpr (by omega)
  have h_cps := cumulative_pad_sum_for_active_prefix j (by omega) h_prefix
  rw [h_cps]
  have h_j_cast : (j : FBB).val = j := fbb_val_natCast (by omega)
  have h_cps34_le := cPS_val_le h_constraints 34 (le_refl _)
  -- Build up the sum: ts + 3 + cPS(34) + j
  have h1 : (start_timestamp air row + 3).val =
      (start_timestamp air row).val + 3 :=
    fbb_val_add (by omega)
  have h2 : (start_timestamp air row + 3 + cumulativePadSum air row 34).val =
      (start_timestamp air row).val + 3 + (cumulativePadSum air row 34).val := by
    rw [fbb_val_add (by rw [h1]; omega), h1]
  have h3 : (start_timestamp air row + 3 + cumulativePadSum air row 34 + (↑j : FBB)).val =
      (start_timestamp air row).val + 3 + (cumulativePadSum air row 34).val + j := by
    rw [fbb_val_add (by rw [h2, h_j_cast]; omega), h2, h_j_cast]
  rw [h3, h_cps34]

theorem postimage_write_timestamp_val (j : ℕ) (hj : j < activeWords air row)
    (h_en : is_enabled air row = 1)
    (h_axioms : axiomsPerRow air row)
    {h_row : row ≤ air.last_row} (h_constraints : allHold_simplified air row h_row) :
    (start_timestamp air row + 3 + 2 * cumulativePadSum air row 34 +
      cumulativePadSum air row j).val =
      (start_timestamp air row).val + 3 + 2 * activeWords air row + j := by
  have h_aw_le := activeWords_le_34 h_constraints h_en
  have h_bounds := execution_bus_bounds air row h_axioms h_en
  have h_ts := h_bounds.2.2
  have h_cps34 := cumulativePadSum_34_val_eq_activeWords h_constraints h_en
  have h_cps34_le := cPS_val_le h_constraints 34 (le_refl _)
  -- cPS(j) = (j : FBB) for active j
  have h_prefix : ∀ k, k < j → is_padding_byte air k row = 0 := by
    intro k hk
    exact (active_word_iff_not_padding h_constraints h_en k (by omega)).mpr (by omega)
  have h_cps := cumulative_pad_sum_for_active_prefix j (by omega) h_prefix
  rw [h_cps]
  have h_j_cast : (j : FBB).val = j := fbb_val_natCast (by omega)
  have h2_cast : (2 : FBB).val = 2 := by decide
  -- 2 * cPS(34)
  have h_2cps : (2 * cumulativePadSum air row 34).val =
      2 * (cumulativePadSum air row 34).val := by
    rw [fbb_val_mul (by rw [h2_cast]; omega), h2_cast]
  -- Build: ts + 3 + 2*cPS(34) + j
  have h1 : (start_timestamp air row + 3).val =
      (start_timestamp air row).val + 3 :=
    fbb_val_add (by omega)
  have h2 : (start_timestamp air row + 3 + 2 * cumulativePadSum air row 34).val =
      (start_timestamp air row).val + 3 + 2 * (cumulativePadSum air row 34).val := by
    rw [fbb_val_add (by rw [h1, h_2cps]; omega), h1, h_2cps]
  have h3 : (start_timestamp air row + 3 + 2 * cumulativePadSum air row 34 + (↑j : FBB)).val =
      (start_timestamp air row).val + 3 + 2 * (cumulativePadSum air row 34).val + j := by
    rw [fbb_val_add (by rw [h2, h_j_cast]; omega), h2, h_j_cast]
  rw [h3, h_cps34]

/-! ## Fact-Producing Theorems -/

theorem preimage_read_fact (j : ℕ) (hj : j < activeWords air row)
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    (h_axioms : axiomsPerRow air row)
    {h_row : row ≤ air.last_row} (h_constraints : allHold_simplified air row h_row) :
    PreimageReadFact air row j := by
  have h_aw_le := activeWords_le_34 h_constraints h_en
  have h_active : is_padding_byte air j row = 0 :=
    (active_word_iff_not_padding h_constraints h_en j (by omega)).mpr hj
  have h_active0 : is_padding_byte air 0 row = 0 :=
    (active_word_iff_not_padding h_constraints h_en 0 (by omega)).mpr (by omega)
  have h_ptr0 := buffer_ptr_val_bound air row h_wf h_en h_active0
  have h4j : ((↑(4 * j) : FBB)).val = 4 * j := fbb_val_natCast (by omega)
  have h_addr : (buffer_ptr air row + (↑(4 * j) : FBB)).val =
      (buffer_ptr air row).val + 4 * j := by
    rw [fbb_val_add (by rw [h4j]; omega), h4j]
  refine ⟨?_, h_addr, preimage_read_timestamp_val air row j hj h_en h_axioms h_constraints⟩
  rw [h_en, h_active, sub_zero, mul_one]

theorem input_read_fact (j : ℕ) (hj : j < activeWords air row)
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    (h_axioms : axiomsPerRow air row)
    {h_row : row ≤ air.last_row} (h_constraints : allHold_simplified air row h_row) :
    InputReadFact air row j := by
  have h_aw_le := activeWords_le_34 h_constraints h_en
  have h_active : is_padding_byte air j row = 0 :=
    (active_word_iff_not_padding h_constraints h_en j (by omega)).mpr hj
  have h_active0 : is_padding_byte air 0 row = 0 :=
    (active_word_iff_not_padding h_constraints h_en 0 (by omega)).mpr (by omega)
  have h_ptr0 := input_ptr_val_bound air row h_wf h_en h_active0
  have h4j : ((↑(4 * j) : FBB)).val = 4 * j := fbb_val_natCast (by omega)
  have h_addr : (input_ptr air row + (↑(4 * j) : FBB)).val =
      (input_ptr air row).val + 4 * j := by
    rw [fbb_val_add (by rw [h4j]; omega), h4j]
  refine ⟨?_, h_addr, input_read_timestamp_val air row j hj h_en h_axioms h_constraints⟩
  rw [h_en, h_active, sub_zero, mul_one]

theorem postimage_write_fact (j : ℕ) (hj : j < activeWords air row)
    (h_wf_assume : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    (h_axioms : axiomsPerRow air row)
    {h_row : row ≤ air.last_row} (h_constraints : allHold_simplified air row h_row) :
    PostimageWriteFact air row j := by
  have h_aw_le := activeWords_le_34 h_constraints h_en
  have h_active : is_padding_byte air j row = 0 :=
    (active_word_iff_not_padding h_constraints h_en j (by omega)).mpr hj
  have h_active0 : is_padding_byte air 0 row = 0 :=
    (active_word_iff_not_padding h_constraints h_en 0 (by omega)).mpr (by omega)
  have h_ptr0 := buffer_ptr_val_bound air row h_wf_assume h_en h_active0
  have h4j : ((↑(4 * j) : FBB)).val = 4 * j := fbb_val_natCast (by omega)
  have h_addr : (buffer_ptr air row + (↑(4 * j) : FBB)).val =
      (buffer_ptr air row).val + 4 * j := by
    rw [fbb_val_add (by rw [h4j]; omega), h4j]
  refine ⟨?_, h_addr,
    postimage_write_timestamp_val air row j hj h_en h_axioms h_constraints, ?_⟩
  · rw [h_en, h_active, sub_zero, mul_one]
  · intro k hk
    have hdiv : (4 * j + k) / 4 = j := by omega
    have hxor := bitwise_xor_at_byte air row h_wf_assume h_en (4 * j + k) (by omega)
      (by simpa [hdiv] using h_active)
    exact hxor.2.2

theorem bitwise_byte_fact (i : ℕ) (hi : i < (xorin_len air row).val)
    (h_wf : wf_propertiesToAssumePerRow air row)
    (h_en : is_enabled air row = 1)
    {h_row : row ≤ air.last_row} (h_constraints : allHold_simplified air row h_row) :
    BitwiseByteFact air row i := by
  have h_len_le := xorin_len_le_max h_constraints h_en
  have h_mod := xorin_len_mod_four h_constraints h_en
  have h_aw_def : activeWords air row = (xorin_len air row).val / 4 := rfl
  have h_xorin_eq : (xorin_len air row).val = activeWords air row * 4 := by omega
  have h_active : is_padding_byte air (i / 4) row = 0 :=
    (active_word_iff_not_padding h_constraints h_en (i / 4) (by omega)).mpr (by omega)
  have h := bitwise_xor_at_byte air row h_wf h_en i (by omega) h_active
  exact ⟨by rw [h_en, h_active, sub_zero, mul_one], h.1, h.2.1, h.2.2⟩

end XorinVmAir.Soundness.BusFacts
