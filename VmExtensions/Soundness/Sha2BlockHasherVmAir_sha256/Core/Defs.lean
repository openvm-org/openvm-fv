/-
  Proof Definitions

  Shared definitions used across the proof layers.
  These supplement the definitions in `TraceSpec.lean`.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## Schedule helpers

The message-schedule constraints are written over the 8-word window
`[local.w[0..3], next.w[0..3]]`, not just the 4 local words. These helpers
expose that concatenated view and keep the limb decomposition explicit. -/

/-- Concatenated schedule word bits:
    slots `0..3` are local, slots `4..7` are read from the successor row. -/
def concatScheduleBitsWord (air : C FBB ExtF) (row slot : ℕ) : BitsWord :=
  if slot < 4 then scheduleBitsWord air row slot
  else scheduleBitsWord air (nextRow air row) (slot - 4)

/-- Schedule-word bits from the raw rotation-1 "next row" view used in the AIR. -/
def nextScheduleBitsWord (air : C FBB ExtF) (row slot : ℕ) : BitsWord :=
  fun i => next_msg_schedule_w air slot i.val row

/-- Raw 8-word schedule window used by the AIR constraints:
    local slots `0..3`, then raw rotation-1 next slots `4..7`. -/
def rawConcatScheduleBitsWord (air : C FBB ExtF) (row slot : ℕ) : BitsWord :=
  if slot < 4 then scheduleBitsWord air row slot
  else nextScheduleBitsWord air row (slot - 4)

/-- Concatenated schedule word as a UInt32, using the same `0..3` / `4..7` split. -/
def concatScheduleWord (air : C FBB ExtF) (row slot : ℕ) : Word :=
  bitsWordToUInt32 (concatScheduleBitsWord air row slot)

/-- Low 16-bit limb of a concatenated schedule word. -/
def concatScheduleLo16 (air : C FBB ExtF) (row slot : ℕ) : FBB :=
  composeLo16 (concatScheduleBitsWord air row slot)

/-- High 16-bit limb of a concatenated schedule word. -/
def concatScheduleHi16 (air : C FBB ExtF) (row slot : ℕ) : FBB :=
  composeHi16 (concatScheduleBitsWord air row slot)

/-- Message-schedule carries are encoded using two boolean cells per 16-bit limb.
    This decodes the carry for `limb = 0` or `limb = 1` into the field element
    `bit0 + 2 * bit1`. -/
def scheduleCarryValue (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  msg_schedule_carry_or_buffer air slot (2 * limb) row +
  2 * msg_schedule_carry_or_buffer air slot (2 * limb + 1) row

/-- The `w[t-7]` low limb source used by the schedule recurrence.
    Slots `0..2` read from `schedule_helper_w_3`; slot `3` reads local `w[0]`
    directly, matching constraint `683`. -/
def scheduleW7Lo16 (air : C FBB ExtF) (row slot : ℕ) : FBB :=
  if slot < 3 then schedule_helper_w_3 air slot 0 row
  else concatScheduleLo16 air row 0

/-- The `w[t-7]` high limb source used by the schedule recurrence. -/
def scheduleW7Hi16 (air : C FBB ExtF) (row slot : ℕ) : FBB :=
  if slot < 3 then schedule_helper_w_3 air slot 1 row
  else concatScheduleHi16 air row 0

theorem nextScheduleBitsWord_eq_scheduleBitsWord_nextRow
    (air : C FBB ExtF) (row slot : ℕ)
    (hrot : rotation_consistent air)
    (hrow : row ≤ Circuit.last_row air) :
    nextScheduleBitsWord air row slot = scheduleBitsWord air (nextRow air row) slot := by
  funext i
  simp [nextScheduleBitsWord, scheduleBitsWord,
    next_msg_schedule_w_eq_nextRow air hrot slot i.val row hrow]

theorem nextScheduleCarryValue_eq_scheduleCarryValue_nextRow
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hrot : rotation_consistent air)
    (hrow : row ≤ Circuit.last_row air) :
    next_msg_schedule_carry_or_buffer air slot (2 * limb) row +
      2 * next_msg_schedule_carry_or_buffer air slot (2 * limb + 1) row =
        scheduleCarryValue air (nextRow air row) slot limb := by
  simp [scheduleCarryValue,
    next_msg_schedule_carry_or_buffer_eq_nextRow air hrot slot (2 * limb) row hrow,
    next_msg_schedule_carry_or_buffer_eq_nextRow air hrot slot (2 * limb + 1) row hrow]

theorem rawConcatScheduleBitsWord_eq_concatScheduleBitsWord
    (air : C FBB ExtF) (row slot : ℕ)
    (hrot : rotation_consistent air)
    (hrow : row ≤ Circuit.last_row air) :
    rawConcatScheduleBitsWord air row slot = concatScheduleBitsWord air row slot := by
  by_cases hslot : slot < 4
  · simp [rawConcatScheduleBitsWord, concatScheduleBitsWord, hslot]
  · rw [rawConcatScheduleBitsWord, concatScheduleBitsWord, if_neg hslot, if_neg hslot]
    simpa using
      nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row (slot - 4) hrot hrow

/-- Every schedule word on the 16 round rows of the block rooted at `start`
    is a boolean bit-vector. This is the block-local schedule-bit contract
    actually consumed by the schedule and round-step proof layers. -/
def scheduleBitsBooleanOnBlock (air : C FBB ExtF) (start : ℕ) : Prop :=
  ∀ offset slot, offset < 16 → slot < 4 →
    isBitsWord (scheduleBitsWord air (start + offset) slot)

/-! ## Digest helpers

On the digest row, the addition `final_hash[w] = prev_hash[w] + work_var[w] (mod 2^32)`
is enforced via 16-bit limbed carry addition. The following helpers extract the
relevant limb values for each of the 8 digest words. -/

/-- Low 16-bit limb of digest prev_hash[word].
    These columns are already stored as little-endian u16 limbs. -/
def digestPrevHashLo16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  prev_hash air word 0 row

/-- High 16-bit limb of digest prev_hash[word]. -/
def digestPrevHashHi16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  prev_hash air word 1 row

/-- All `prev_hash` u16 limbs on a digest row fit in `0 .. 2^16 - 1`. -/
def digestPrevHashLimbRange (air : C FBB ExtF) (row : ℕ) : Prop :=
  ∀ word limb, word < 8 → limb < 2 →
    (prev_hash air word limb row).val < 2 ^ 16

/-- Low 16-bit limb of digest final_hash[word], composed from 2 little-endian bytes. -/
def digestFinalHashLo16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  final_hash air word 0 row + final_hash air word 1 row * 256

/-- High 16-bit limb of digest final_hash[word], composed from 2 little-endian bytes. -/
def digestFinalHashHi16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  final_hash air word 2 row + final_hash air word 3 row * 256

/-- Digest work variable lo-16 limb for word w.
    Words 0–3 map to a[3-w], words 4–7 map to e[7-w]. -/
def digestWorkVarLo16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  if word < 4 then composeLo16 (aBitsWord air row (3 - word))
  else composeLo16 (eBitsWord air row (7 - word))

/-- Digest work variable hi-16 limb for word w. -/
def digestWorkVarHi16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  if word < 4 then composeHi16 (aBitsWord air row (3 - word))
  else composeHi16 (eBitsWord air row (7 - word))

/-- The work variable corresponding to digest word w, as UInt32. -/
def digestWorkVarWord (air : C FBB ExtF) (row word : ℕ) : Word :=
  if word < 4 then aWord air row (3 - word)
  else eWord air row (7 - word)

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
