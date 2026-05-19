/-
  Layer C: Round Step (Core)
  Carry range facts and wrap-aware state/word projections used by round-step
  proofs.
  Depends on: FieldArithmetic, BaseFacts, MessageSchedule.Core
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.FieldArithmetic
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.BaseFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.MessageSchedule.Core

set_option autoImplicit false

set_option maxHeartbeats 10000000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## C1: Carry range constraints

The implemented AIR only proves that round-step carries are bytes via the
bitwise lookup bus. They are not boolean carries, so the proof bridge must use
bounded-carry arithmetic lemmas. -/

/-! ## C2: Field-level round step

The round constant K[t] is selected by the encoder polynomial. -/

def k_limb_at (row_idx slot limb : ℕ) : FBB :=
  let t := row_idx * 4 + slot
  if limb = 0 then ((sha256K[t]!.toNat % 2^16 : ℕ) : FBB)
  else ((sha256K[t]!.toNat / 2^16 : ℕ) : FBB)

/-- Concatenated a-word: a[j]@local if j < 4, a[j-4]@next if j ≥ 4.
    Needed because slots 1–3 read earlier slots' results from next row. -/
def concatAWord (air : C FBB ExtF) (row j : ℕ) : Word :=
  if j < 4 then aWord air row j else aWord air (nextRow air row) (j - 4)

/-- Concatenated e-word: same logic as concatAWord. -/
def concatEWord (air : C FBB ExtF) (row j : ℕ) : Word :=
  if j < 4 then eWord air row j else eWord air (nextRow air row) (j - 4)

/-- Concatenated a-bits: field-level version. -/
def concatABitsWord (air : C FBB ExtF) (row j : ℕ) : BitsWord :=
  if j < 4 then aBitsWord air row j else aBitsWord air (nextRow air row) (j - 4)

/-- Concatenated e-bits: field-level version. -/
def concatEBitsWord (air : C FBB ExtF) (row j : ℕ) : BitsWord :=
  if j < 4 then eBitsWord air row j else eBitsWord air (nextRow air row) (j - 4)

/-- Raw rotation-1 view of the next-row a word used by the AIR. -/
def nextABitsWord (air : C FBB ExtF) (row slot : ℕ) : BitsWord :=
  fun i => next_work_vars_a air slot i.val row

/-- Raw rotation-1 view of the next-row e word used by the AIR. -/
def nextEBitsWord (air : C FBB ExtF) (row slot : ℕ) : BitsWord :=
  fun i => next_work_vars_e air slot i.val row

/-- Raw 8-word a window used by the AIR: local `0..3`, then rotation-1 next `4..7`. -/
def rawConcatABitsWord (air : C FBB ExtF) (row j : ℕ) : BitsWord :=
  if j < 4 then aBitsWord air row j else nextABitsWord air row (j - 4)

/-- Raw 8-word e window used by the AIR: local `0..3`, then rotation-1 next `4..7`. -/
def rawConcatEBitsWord (air : C FBB ExtF) (row j : ℕ) : BitsWord :=
  if j < 4 then eBitsWord air row j else nextEBitsWord air row (j - 4)

def roundStepALoConstraint (air : C FBB ExtF) (row slot : ℕ) : Prop :=
  match slot with
  | 0 => constraint_721 air row
  | 1 => constraint_725 air row
  | 2 => constraint_729 air row
  | 3 => constraint_733 air row
  | _ => False

def roundStepAHiConstraint (air : C FBB ExtF) (row slot : ℕ) : Prop :=
  match slot with
  | 0 => constraint_722 air row
  | 1 => constraint_726 air row
  | 2 => constraint_730 air row
  | 3 => constraint_734 air row
  | _ => False

def roundStepELoConstraint (air : C FBB ExtF) (row slot : ℕ) : Prop :=
  match slot with
  | 0 => constraint_723 air row
  | 1 => constraint_727 air row
  | 2 => constraint_731 air row
  | 3 => constraint_735 air row
  | _ => False

def roundStepEHiConstraint (air : C FBB ExtF) (row slot : ℕ) : Prop :=
  match slot with
  | 0 => constraint_724 air row
  | 1 => constraint_728 air row
  | 2 => constraint_732 air row
  | 3 => constraint_736 air row
  | _ => False

/-- The a-update low limb constraint for slot i. -/
theorem round_step_a_lo (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hrs : round_step_constraints air row) :
    roundStepALoConstraint air row slot := by
  unfold round_step_constraints constraints_721_736 at hrs
  interval_cases slot
  · have h721 : constraint_721 air row := by tauto
    simpa [roundStepALoConstraint] using h721
  · have h725 : constraint_725 air row := by tauto
    simpa [roundStepALoConstraint] using h725
  · have h729 : constraint_729 air row := by tauto
    simpa [roundStepALoConstraint] using h729
  · have h733 : constraint_733 air row := by tauto
    simpa [roundStepALoConstraint] using h733

/-- The a-update high limb constraint for slot i. -/
theorem round_step_a_hi (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hrs : round_step_constraints air row) :
    roundStepAHiConstraint air row slot := by
  unfold round_step_constraints constraints_721_736 at hrs
  interval_cases slot
  · have h722 : constraint_722 air row := by tauto
    simpa [roundStepAHiConstraint] using h722
  · have h726 : constraint_726 air row := by tauto
    simpa [roundStepAHiConstraint] using h726
  · have h730 : constraint_730 air row := by tauto
    simpa [roundStepAHiConstraint] using h730
  · have h734 : constraint_734 air row := by tauto
    simpa [roundStepAHiConstraint] using h734

/-- The e-update low limb constraint for slot i. -/
theorem round_step_e_lo (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hrs : round_step_constraints air row) :
    roundStepELoConstraint air row slot := by
  unfold round_step_constraints constraints_721_736 at hrs
  interval_cases slot
  · have h723 : constraint_723 air row := by tauto
    simpa [roundStepELoConstraint] using h723
  · have h727 : constraint_727 air row := by tauto
    simpa [roundStepELoConstraint] using h727
  · have h731 : constraint_731 air row := by tauto
    simpa [roundStepELoConstraint] using h731
  · have h735 : constraint_735 air row := by tauto
    simpa [roundStepELoConstraint] using h735

/-- The e-update high limb constraint for slot i. -/
theorem round_step_e_hi (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hrs : round_step_constraints air row) :
    roundStepEHiConstraint air row slot := by
  unfold round_step_constraints constraints_721_736 at hrs
  interval_cases slot
  · have h724 : constraint_724 air row := by tauto
    simpa [roundStepEHiConstraint] using h724
  · have h728 : constraint_728 air row := by tauto
    simpa [roundStepEHiConstraint] using h728
  · have h732 : constraint_732 air row := by tauto
    simpa [roundStepEHiConstraint] using h732
  · have h736 : constraint_736 air row := by tauto
    simpa [roundStepEHiConstraint] using h736

/-! ## C3: Single round step field-to-UInt32 bridge -/

/-- The input working state for slot i, assembled from the concatenated view. -/
def slotInputState (air : C FBB ExtF) (row slot : ℕ) : WorkingVars where
  a := concatAWord air row (slot + 3)
  b := concatAWord air row (slot + 2)
  c := concatAWord air row (slot + 1)
  d := concatAWord air row slot
  e := concatEWord air row (slot + 3)
  f := concatEWord air row (slot + 2)
  g := concatEWord air row (slot + 1)
  h := concatEWord air row slot


theorem nextABitsWord_eq_aBitsWord_nextRow
    (air : C FBB ExtF) (row slot : ℕ)
    (hrot : rotation_consistent air)
    (hrow : row ≤ Circuit.last_row air) :
    nextABitsWord air row slot = aBitsWord air (nextRow air row) slot := by
  funext i
  simp [nextABitsWord, aBitsWord,
    next_work_vars_a_eq_nextRow air hrot slot i.val row hrow]

theorem nextEBitsWord_eq_eBitsWord_nextRow
    (air : C FBB ExtF) (row slot : ℕ)
    (hrot : rotation_consistent air)
    (hrow : row ≤ Circuit.last_row air) :
    nextEBitsWord air row slot = eBitsWord air (nextRow air row) slot := by
  funext i
  simp [nextEBitsWord, eBitsWord,
    next_work_vars_e_eq_nextRow air hrot slot i.val row hrow]

theorem rawConcatABitsWord_eq_concatABitsWord
    (air : C FBB ExtF) (row j : ℕ)
    (hrot : rotation_consistent air)
    (hrow : row ≤ Circuit.last_row air) :
    rawConcatABitsWord air row j = concatABitsWord air row j := by
  by_cases hj : j < 4
  · simp [rawConcatABitsWord, concatABitsWord, hj]
  · simp [rawConcatABitsWord, concatABitsWord, hj,
      nextABitsWord_eq_aBitsWord_nextRow air row (j - 4) hrot hrow]

theorem rawConcatEBitsWord_eq_concatEBitsWord
    (air : C FBB ExtF) (row j : ℕ)
    (hrot : rotation_consistent air)
    (hrow : row ≤ Circuit.last_row air) :
    rawConcatEBitsWord air row j = concatEBitsWord air row j := by
  by_cases hj : j < 4
  · simp [rawConcatEBitsWord, concatEBitsWord, hj]
  · simp [rawConcatEBitsWord, concatEBitsWord, hj,
      nextEBitsWord_eq_eBitsWord_nextRow air row (j - 4) hrot hrow]

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
