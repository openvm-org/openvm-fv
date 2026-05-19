/-
  Layer C: Round Step (Core)

  Core round-step helpers for the SHA-512 block hasher. This file packages the
  proof-side contract consumed by `RowChain`:

  - wrap-aware local/next projections for the 8-word working-state window;
  - decoded round-constant limbs for the successor row;
  - the AIR-shaped 4-limb update equalities for `a` and `e`;
  - word-level bridge fields for limb-to-`UInt64` reconstruction.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.FieldArithmetic
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.Defs

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-- The `limb`-th 16-bit chunk of `K[row_idx * 4 + slot]` in little-endian order. -/
def k_limb_at (row_idx slot limb : ℕ) : FBB :=
  let t := row_idx * 4 + slot
  (((sha512K[t]!.toNat / 2 ^ (16 * limb)) % 2 ^ 16 : ℕ) : FBB)

/-- Concatenated a-word: local slots `0..3`, then successor-row slots `4..7`. -/
def concatAWord (air : C FBB ExtF) (row j : ℕ) : Word :=
  if j < 4 then aWord air row j else aWord air (nextRow air row) (j - 4)

/-- Concatenated e-word: local slots `0..3`, then successor-row slots `4..7`. -/
def concatEWord (air : C FBB ExtF) (row j : ℕ) : Word :=
  if j < 4 then eWord air row j else eWord air (nextRow air row) (j - 4)

/-- Concatenated a-bits: local slots `0..3`, then successor-row slots `4..7`. -/
def concatABitsWord (air : C FBB ExtF) (row j : ℕ) : BitsWord :=
  if j < 4 then aBitsWord air row j else aBitsWord air (nextRow air row) (j - 4)

/-- Concatenated e-bits: local slots `0..3`, then successor-row slots `4..7`. -/
def concatEBitsWord (air : C FBB ExtF) (row j : ℕ) : BitsWord :=
  if j < 4 then eBitsWord air row j else eBitsWord air (nextRow air row) (j - 4)

/-- Raw rotation-1 view of the successor-row `a` word used by the AIR. -/
def nextABitsWord (air : C FBB ExtF) (row slot : ℕ) : BitsWord :=
  fun i => next_work_vars_a air slot i.val row

/-- Raw rotation-1 view of the successor-row `e` word used by the AIR. -/
def nextEBitsWord (air : C FBB ExtF) (row slot : ℕ) : BitsWord :=
  fun i => next_work_vars_e air slot i.val row

/-- Raw 8-word `a` window used by the AIR: local `0..3`, then raw successor `4..7`. -/
def rawConcatABitsWord (air : C FBB ExtF) (row j : ℕ) : BitsWord :=
  if j < 4 then aBitsWord air row j else nextABitsWord air row (j - 4)

/-- Raw 8-word `e` window used by the AIR: local `0..3`, then raw successor `4..7`. -/
def rawConcatEBitsWord (air : C FBB ExtF) (row j : ℕ) : BitsWord :=
  if j < 4 then eBitsWord air row j else nextEBitsWord air row (j - 4)

/-- Proof-side decoded round constant for the successor row.

For successor-row selectors `0..19`, this returns the corresponding SHA-512
constant limb; otherwise it is `0`. -/
def roundConstantPolyAtNext (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  let idx := (encoder_selector_idx air (nextRow air row)).val
  if hslot : slot < 4 then
    if hlimb : limb < 4 then
      if hidx : idx < 20 then k_limb_at idx slot limb else 0
    else
      0
  else
    0

/-- Compose the `limb`-th 16-bit chunk of a bit-word, returning `0` out of range. -/
def bitsU16Limb (bits : BitsWord) (limb : ℕ) : FBB :=
  if hlimb : limb < 4 then composeU16Limb bits ⟨limb, hlimb⟩ else 0

theorem bitsU16Limb_eq_composeU16Limb (bits : BitsWord) (limb : ℕ)
    (hlimb : limb < 4) :
    bitsU16Limb bits limb = composeU16Limb bits ⟨limb, hlimb⟩ := by
  simp [bitsU16Limb, hlimb]

/-- Carry entering the `limb`-th `a`-update limb. -/
def roundStepCarryInA (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  if limb = 0 then 0 else next_carry_a air slot (limb - 1) row

/-- Carry entering the `limb`-th `e`-update limb. -/
def roundStepCarryInE (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  if limb = 0 then 0 else next_carry_e air slot (limb - 1) row

/-- The input working state for slot `i`, assembled from the concatenated view. -/
def slotInputState (air : C FBB ExtF) (row slot : ℕ) : WorkingVars where
  a := concatAWord air row (slot + 3)
  b := concatAWord air row (slot + 2)
  c := concatAWord air row (slot + 1)
  d := concatAWord air row slot
  e := concatEWord air row (slot + 3)
  f := concatEWord air row (slot + 2)
  g := concatEWord air row (slot + 1)
  h := concatEWord air row slot

/-- Expected successor-row `a` word for one round-step slot. -/
abbrev roundStepAExpected (air : C FBB ExtF) (row slot row_idx : ℕ) : Word :=
  (roundStep (slotInputState air row slot)
    (sha512K[row_idx * 4 + slot]!)
    (scheduleWordAtRow air (nextRow air row) slot)).a

/-- Expected successor-row `e` word for one round-step slot. -/
abbrev roundStepEExpected (air : C FBB ExtF) (row slot row_idx : ℕ) : Word :=
  (roundStep (slotInputState air row slot)
    (sha512K[row_idx * 4 + slot]!)
    (scheduleWordAtRow air (nextRow air row) slot)).e

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

/--
Proof-side round-step contract for the 64-bit `a` and `e` update constraints.

The constraints layer carries the raw extracted round-step slice. This record
packages the two 4-limb carry-chain equalities used to derive the word-level
SHA-512 round-step statements.
-/
structure round_step_constraints (air : C FBB ExtF) (row : ℕ) : Prop where
  a_update_limb_eq :
    ∀ (slot limb : ℕ) (hslot : slot < 4) (hlimb : limb < 4),
      roundStepCarryInA air row slot limb +
        bitsU16Limb (rawConcatEBitsWord air row slot) limb +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) limb +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row (slot + 3))
            (rawConcatEBitsWord air row (slot + 2))
            (rawConcatEBitsWord air row (slot + 1))) limb +
        roundConstantPolyAtNext air row slot limb +
        bitsU16Limb (nextScheduleBitsWord air row slot) limb * next_is_round_row air row +
        bitsU16Limb (fieldBigSigma0 (rawConcatABitsWord air row (slot + 3))) limb +
        bitsU16Limb
          (fieldMaj (rawConcatABitsWord air row (slot + 3))
            (rawConcatABitsWord air row (slot + 2))
            (rawConcatABitsWord air row (slot + 1))) limb =
      bitsU16Limb (nextABitsWord air row slot) limb +
        next_carry_a air slot limb row * (2 ^ 16 : ℕ)
  e_update_limb_eq :
    ∀ (slot limb : ℕ) (hslot : slot < 4) (hlimb : limb < 4),
      roundStepCarryInE air row slot limb +
        bitsU16Limb (rawConcatABitsWord air row slot) limb +
        bitsU16Limb (rawConcatEBitsWord air row slot) limb +
        bitsU16Limb (fieldBigSigma1 (rawConcatEBitsWord air row (slot + 3))) limb +
        bitsU16Limb
          (fieldCh (rawConcatEBitsWord air row (slot + 3))
            (rawConcatEBitsWord air row (slot + 2))
            (rawConcatEBitsWord air row (slot + 1))) limb +
        roundConstantPolyAtNext air row slot limb +
        bitsU16Limb (nextScheduleBitsWord air row slot) limb * next_is_round_row air row =
        bitsU16Limb (nextEBitsWord air row slot) limb +
        next_carry_e air slot limb row * (2 ^ 16 : ℕ)

/-- Raw extracted `a`-update limb constraint selected by round slot and u16 limb. -/
def raw_a_update_constraint (air : C FBB ExtF) (row slot limb : ℕ) : Prop :=
  match slot, limb with
  | 0, 0 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1416 air row
  | 0, 1 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1417 air row
  | 0, 2 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1418 air row
  | 0, 3 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1419 air row
  | 1, 0 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1424 air row
  | 1, 1 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1425 air row
  | 1, 2 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1426 air row
  | 1, 3 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1427 air row
  | 2, 0 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1432 air row
  | 2, 1 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1433 air row
  | 2, 2 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1434 air row
  | 2, 3 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1435 air row
  | 3, 0 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1440 air row
  | 3, 1 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1441 air row
  | 3, 2 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1442 air row
  | 3, 3 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1443 air row
  | _, _ => False

/-- Raw extracted `e`-update limb constraint selected by round slot and u16 limb. -/
def raw_e_update_constraint (air : C FBB ExtF) (row slot limb : ℕ) : Prop :=
  match slot, limb with
  | 0, 0 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1420 air row
  | 0, 1 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1421 air row
  | 0, 2 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1422 air row
  | 0, 3 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1423 air row
  | 1, 0 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1428 air row
  | 1, 1 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1429 air row
  | 1, 2 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1430 air row
  | 1, 3 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1431 air row
  | 2, 0 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1436 air row
  | 2, 1 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1437 air row
  | 2, 2 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1438 air row
  | 2, 3 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1439 air row
  | 3, 0 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1444 air row
  | 3, 1 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1445 air row
  | 3, 2 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1446 air row
  | 3, 3 => Sha2BlockHasherVmAir_sha512.constraints.constraint_1447 air row
  | _, _ => False

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
