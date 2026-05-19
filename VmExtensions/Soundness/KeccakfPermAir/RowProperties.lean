/-
  Row-constraint-derived lemmas for KeccakfPermAir (FBB-specialized).

  Extracts the export_flag boolean constraint and named parametric constraint
  families from the 3183 row constraints via the segment-split infrastructure
  in AllHoldSplit.lean.

  Constraint families extracted:
  - Control step-init (seg_A, 24 constraints)
  - Transition step-rotation (seg_B, 24 constraints)
  - Preimage init (seg_C, 100 constraints)
  - Preimage consistency (seg_D, 100 constraints)
  - Output chaining (seg_F, 100 constraints)
-/
import VmExtensions.Constraints.KeccakfPermAir.AllHoldSplit
import VmExtensions.Soundness.KeccakfPermAir.AllHoldSplitExt
import VmExtensions.Soundness.KeccakfPermAir.Round.Surface
import OpenvmFv.Fundamentals.BabyBear

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfPermAir.Soundness

open KeccakfPermAir.constraints
open BabyBear

variable {ExtF : Type} [Field ExtF]

/-! ## Constraint Extraction -/

-- Extract the row-constraint conjunction from allHold_simplified.
lemma rows_of_allHold_simplified
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : allHold_simplified air row) :
    List.Forall (·) (row_constraint_list air row) :=
  h.2

/-! ## Export Flag Boolean (constraint_248)

constraint_248 is the first element of seg_E (rot=0, Theta+Chi+Iota segment).
We extract it via the segment split: allHold → rot0 → seg_E → head.
-/

-- export_flag is binary: export_flag * (export_flag - 1) = 0.
-- Derived from constraint_248, the first element of seg_E in the rot0 constraint list.
lemma export_flag_boolean
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : allHold_simplified air row) :
    export_flag air row * (export_flag air row - 1) = 0 := by
  have h_rot0 := forall_rot0_of_forall_row air row h.2
  simp only [rot0_constraint_list, List.forall_append] at h_rot0
  -- h_rot0 : ((seg_A ∧ seg_C) ∧ seg_E) ∧ seg_G
  -- seg_E starts with constraint_248; .1 extracts the head via List.Forall
  exact h_rot0.1.2.1

/-! ## Parametric Extraction Infrastructure

The approach: for each constraint family, prove the segment list equals a
`List.range`-mapped (or permutation-mapped) parametric form by `rfl`, then
use `List.Forall` membership to extract individual constraints without
`interval_cases` on the full range.
-/

section extraction_helpers

-- Helper: extract a true proposition from List.Forall id by membership.
private lemma forall_id_mem {l : List Prop} (h : List.Forall id l)
    {p : Prop} (hp : p ∈ l) : p :=
  List.forall_iff_forall_mem.mp h p hp

-- From List.Forall id on a range-mapped list, extract the predicate at index i.
private lemma forall_range_map {n : ℕ} {f : ℕ → Prop}
    (h : List.Forall id ((List.range n).map f)) {i : ℕ} (hi : i < n) : f i :=
  forall_id_mem h (List.mem_map_of_mem (List.mem_range.mpr hi))

-- From List.Forall id on a mapped list, extract the predicate for any member.
private lemma forall_list_map_mem {l : List ℕ} {f : ℕ → Prop}
    (h : List.Forall id (l.map f)) {i : ℕ} (hi : i ∈ l) : f i :=
  forall_id_mem h (List.mem_map_of_mem hi)

end extraction_helpers

/-! ## Segment-Level Extraction from allHold_simplified -/

section segment_extraction

variable {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}

-- rot=0 segments: seg_A (control), seg_C (preimage init)
private lemma seg_A_forall (h : allHold_simplified air row) :
    List.Forall id (seg_A air row) := by
  have h_rot0 := forall_rot0_of_forall_row air row h.2
  simp only [rot0_constraint_list, List.forall_append] at h_rot0
  exact h_rot0.1.1.1

private lemma seg_C_forall (h : allHold_simplified air row) :
    List.Forall id (seg_C air row) := by
  have h_rot0 := forall_rot0_of_forall_row air row h.2
  simp only [rot0_constraint_list, List.forall_append] at h_rot0
  exact h_rot0.1.1.2

-- rot=1 segments: seg_B (step rotation), seg_D (preimage consistency), seg_F (output chaining)
private lemma seg_B_forall (h : allHold_simplified air row) :
    List.Forall id (seg_B air row) := by
  have h_rot1 := forall_rot1_of_forall_row air row h.2
  simp only [rot1_constraint_list, List.forall_append] at h_rot1
  exact h_rot1.1.1

private lemma seg_D_forall (h : allHold_simplified air row) :
    List.Forall id (seg_D air row) := by
  have h_rot1 := forall_rot1_of_forall_row air row h.2
  simp only [rot1_constraint_list, List.forall_append] at h_rot1
  exact h_rot1.1.2

private lemma seg_F_forall (h : allHold_simplified air row) :
    List.Forall id (seg_F air row) := by
  have h_rot1 := forall_rot1_of_forall_row air row h.2
  simp only [rot1_constraint_list, List.forall_append] at h_rot1
  exact h_rot1.2

end segment_extraction

/-! ## Control Step-Init (seg_A, constraints 0-23)

constraint_0: isFirstRow * (step_flag 0 - 1) = 0
constraints 1-23: isFirstRow * step_flag j = 0

At row 0 (where isFirstRow = 1), these force step_flag 0 = 1 and all other
step flags to 0. At other rows (isFirstRow = 0), the constraints are trivially
satisfied.
-/

-- seg_A equals the parametric range-mapped form.
set_option maxHeartbeats 400000 in
private lemma seg_A_eq_map {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row : ℕ) :
    seg_A c row = (List.range 24).map (fun j =>
      if j = 0 then Circuit.isFirstRow c row * (step_flag c 0 row - 1) = 0
      else Circuit.isFirstRow c row * step_flag c j row = 0) := by
  rfl

-- Control step-init constraint family (24 constraints from seg_A).
-- For j = 0: isFirstRow * (step_flag 0 - 1) = 0.
-- For j > 0: isFirstRow * step_flag j = 0.
lemma control_step_init_constraint
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : allHold_simplified air row) (j : ℕ) (hj : j < 24) :
    if j = 0 then Circuit.isFirstRow air row * (step_flag air 0 row - 1) = 0
    else Circuit.isFirstRow air row * step_flag air j row = 0 := by
  have h_segA := seg_A_forall h
  rw [seg_A_eq_map] at h_segA
  exact forall_range_map h_segA hj

/-! ## Transition Step-Rotation (seg_B, constraints 24-47)

constraint_{24+j}: isTransitionRow * (step_flag j - step_flag_next ((j+1) % 24)) = 0

On transition rows (isTransitionRow = 1), these propagate the one-hot step flag
forward by one position modulo 24. The wrap-around at j=23 maps step_flag 23
to step_flag_next 0.
-/

-- seg_B equals the parametric range-mapped form.
set_option maxHeartbeats 400000 in
private lemma seg_B_eq_map {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row : ℕ) :
    seg_B c row = (List.range 24).map (fun j =>
      Circuit.isTransitionRow c row *
        (step_flag c j row - step_flag_next c ((j + 1) % 24) row) = 0) := by
  rfl

-- Transition step-rotation constraint family (24 constraints from seg_B).
-- isTransitionRow * (step_flag j - step_flag_next ((j+1) % 24)) = 0
lemma transition_step_rotation_constraint
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : allHold_simplified air row) (j : ℕ) (hj : j < 24) :
    Circuit.isTransitionRow air row *
      (step_flag air j row - step_flag_next air ((j + 1) % 24) row) = 0 := by
  have h_segB := seg_B_forall h
  rw [seg_B_eq_map] at h_segB
  exact forall_range_map h_segB hj

/-! ## Preimage Init (seg_C, constraints 48-147)

constraint_{48+i}: step_flag 0 * (preimage i - a i) = 0

At step 0 (step_flag 0 = 1): forces preimage i = a i, linking the preimage
to the initial state columns. At other steps: trivially satisfied.
-/

-- seg_C equals the parametric range-mapped form.
set_option maxHeartbeats 800000 in
private lemma seg_C_eq_map {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row : ℕ) :
    seg_C c row = (List.range 100).map (fun i =>
      step_flag c 0 row * (preimage c i row - a c i row) = 0) := by
  rfl

-- Preimage-init constraint family (100 constraints from seg_C).
-- step_flag 0 * (preimage i - a i) = 0
lemma preimage_init_constraint
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : allHold_simplified air row) (i : ℕ) (hi : i < 100) :
    step_flag air 0 row * (preimage air i row - a air i row) = 0 := by
  have h_segC := seg_C_forall h
  rw [seg_C_eq_map] at h_segC
  exact forall_range_map h_segC hi

/-! ## Preimage Consistency (seg_D, constraints 148-247)

constraint_{148+i}: (1 - step_flag 23) * (isTransitionRow * (preimage i - preimage_next i)) = 0

On transition rows where step_flag 23 = 0 (i.e., not the final step of a block):
forces preimage i to persist to the next row. This keeps the preimage constant
across all 24 rows of a block.
-/

-- seg_D equals the parametric range-mapped form.
set_option maxHeartbeats 800000 in
private lemma seg_D_eq_map {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row : ℕ) :
    seg_D c row = (List.range 100).map (fun i =>
      (1 - step_flag c 23 row) *
        (Circuit.isTransitionRow c row *
          (preimage c i row - preimage_next c i row)) = 0) := by
  rfl

-- Preimage-consistency constraint family (100 constraints from seg_D).
-- (1 - step_flag 23) * (isTransitionRow * (preimage i - preimage_next i)) = 0
lemma preimage_consistency_constraint
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : allHold_simplified air row) (i : ℕ) (hi : i < 100) :
    (1 - step_flag air 23 row) *
      (Circuit.isTransitionRow air row *
        (preimage air i row - preimage_next air i row)) = 0 := by
  have h_segD := seg_D_forall h
  rw [seg_D_eq_map] at h_segD
  exact forall_range_map h_segD hi

/-! ## Output Chaining (seg_F, constraints 3082-3181)

constraint_{3082+k}: isTransitionRow * ((1 - step_flag 23) * (output_col i - a_next i)) = 0

where output_col i = a_ppp_00_limb i for i < 4 (lane [0][0], post-iota),
      output_col i = a_prime_prime i for i >= 4.

The 100 constraints cover all limb indices 0..99 but in rho-pi-permuted order
within seg_F. Each constraint equates the round-output column to a_next, linking
the current row's output to the next row's input state.
-/

-- The output column for limb i: a_ppp_00_limb for the first 4 limbs (lane [0][0],
-- which receives the iota round constant), a_prime_prime for the remaining 96.
def output_col {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (i : ℕ) (row : ℕ) : F :=
  if i < 4 then a_ppp_00_limb c i row else a_prime_prime c i row

-- The rho-pi-permuted order in which output-chaining limb indices appear in seg_F.
-- Each group of 4 corresponds to one Keccak lane; lane [0][0] uses a_ppp_00_limb
-- (first 4 entries), the remaining 24 lanes use a_prime_prime in rho-pi order.
private def outputChainingOrder : List ℕ :=
  [ 0,  1,  2,  3, 20, 21, 22, 23, 40, 41, 42, 43, 60, 61, 62, 63, 80, 81, 82, 83,
    4,  5,  6,  7, 24, 25, 26, 27, 44, 45, 46, 47, 64, 65, 66, 67, 84, 85, 86, 87,
    8,  9, 10, 11, 28, 29, 30, 31, 48, 49, 50, 51, 68, 69, 70, 71, 88, 89, 90, 91,
   12, 13, 14, 15, 32, 33, 34, 35, 52, 53, 54, 55, 72, 73, 74, 75, 92, 93, 94, 95,
   16, 17, 18, 19, 36, 37, 38, 39, 56, 57, 58, 59, 76, 77, 78, 79, 96, 97, 98, 99]

-- seg_F equals the permutation-mapped parametric form.
set_option maxHeartbeats 1600000 in
private lemma seg_F_eq_map {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row : ℕ) :
    seg_F c row = outputChainingOrder.map (fun i =>
      Circuit.isTransitionRow c row *
        ((1 - step_flag c 23 row) *
          (output_col c i row - a_next c i row)) = 0) := by
  rfl

-- Every limb index 0..99 appears in the rho-pi-permuted output-chaining order.
set_option maxRecDepth 4096 in
private lemma outputChainingOrder_complete :
    (List.range 100).Forall (· ∈ outputChainingOrder) := by decide

private lemma mem_outputChainingOrder {i : ℕ} (hi : i < 100) :
    i ∈ outputChainingOrder := by
  have h := List.forall_iff_forall_mem.mp outputChainingOrder_complete
  exact h i (List.mem_range.mpr hi)

-- Output-chaining constraint family (100 constraints from seg_F).
-- isTransitionRow * ((1 - step_flag 23) * (output_col i - a_next i)) = 0
-- For i < 4 (post-iota lane [0][0]): output_col = a_ppp_00_limb.
-- For i >= 4: output_col = a_prime_prime.
lemma output_chaining_constraint
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : allHold_simplified air row) (i : ℕ) (hi : i < 100) :
    Circuit.isTransitionRow air row *
      ((1 - step_flag air 23 row) *
        (output_col air i row - a_next air i row)) = 0 := by
  have h_segF := seg_F_forall h
  rw [seg_F_eq_map] at h_segF
  exact forall_list_map_mem h_segF (mem_outputChainingOrder hi)

-- Final: RoundLocalConstraints from allHold_simplified
-- Each field is proved by a dedicated helper in AllHoldSplitExt.lean.
lemma roundLocalConstraints_of_allHold_simplified
    {air : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : allHold_simplified air row) :
    RoundLocalConstraints air row := by
  have h_seg : List.Forall id (seg_E air row) := by
    have h_rot0 := forall_rot0_of_forall_row air row h.2
    simp only [rot0_constraint_list, List.forall_append] at h_rot0
    exact h_rot0.1.2
  exact {
    c_bit_bool := c_bit_bool_of_seg_E air row h_seg
    c_prime_def := c_prime_def_of_seg_E air row h_seg
    a_prime_bit_bool := a_prime_bit_bool_of_seg_E air row h_seg
    theta_xor3_recompose := theta_xor3_recompose_of_seg_E air row h_seg
    theta_parity := theta_parity_of_seg_E air row h_seg
    chi := chi_of_seg_E air row h_seg
    a_pp_00_bit_bool := a_pp_00_bit_bool_of_seg_E air row h_seg
    iota_preiota_recompose := iota_preiota_recompose_of_seg_E air row h_seg
    iota_output_3078 := iota_output_3078_of_seg_E air row h_seg
    iota_output_3079 := iota_output_3079_of_seg_E air row h_seg
    iota_output_3080 := iota_output_3080_of_seg_E air row h_seg
    iota_output_3081 := iota_output_3081_of_seg_E air row h_seg
  }

end KeccakfPermAir.Soundness
