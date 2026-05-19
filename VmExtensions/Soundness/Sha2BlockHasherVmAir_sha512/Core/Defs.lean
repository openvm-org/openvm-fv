import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.SpecFacts

set_option autoImplicit false

/-!
Shared block-hasher definitions used across the SHA-512 proof layers.

The helper surface is built around SHA-512 64-bit words:
- schedule words are exposed as four u16 limbs;
- digest words are exposed as four u16 limbs;
- low/high-style helpers expose the boundary limbs.
-/

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## Schedule helpers -/

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

/-- Concatenated schedule word as a UInt64, using the same `0..3` / `4..7` split. -/
def concatScheduleWord (air : C FBB ExtF) (row slot : ℕ) : Word :=
  bitsWordToUInt64 (concatScheduleBitsWord air row slot)

/-- The `limb`-th 16-bit chunk of a concatenated schedule word. -/
def concatScheduleU16Limb (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  if hlimb : limb < 4 then
    composeU16Limb (concatScheduleBitsWord air row slot) ⟨limb, hlimb⟩
  else
    0

/-- Convenience alias for the low 16-bit limb of a concatenated schedule word. -/
def concatScheduleLo16 (air : C FBB ExtF) (row slot : ℕ) : FBB :=
  concatScheduleU16Limb air row slot 0

/-- Convenience alias for the high 16-bit limb of a concatenated schedule word. -/
def concatScheduleHi16 (air : C FBB ExtF) (row slot : ℕ) : FBB :=
  concatScheduleU16Limb air row slot 3

/-- Message-schedule carries are encoded using two boolean cells per 16-bit limb.
    This decodes the carry for limb `0..3` into the field element
    `bit0 + 2 * bit1`. -/
def scheduleCarryValue (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  msg_schedule_carry_or_buffer air slot (2 * limb) row +
  2 * msg_schedule_carry_or_buffer air slot (2 * limb + 1) row

/-- The `w[t-7]` limb source used by the schedule recurrence.
    Slots `0..2` read from `schedule_helper_w_3`; slot `3` reads local `w[0]`
    directly. -/
def scheduleW7U16Limb (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  if slot < 3 then schedule_helper_w_3 air slot limb row
  else concatScheduleU16Limb air row 0 limb

/-- The low 16-bit limb source for `w[t-7]`. -/
def scheduleW7Lo16 (air : C FBB ExtF) (row slot : ℕ) : FBB :=
  scheduleW7U16Limb air row slot 0

/-- The high 16-bit limb source for `w[t-7]`. -/
def scheduleW7Hi16 (air : C FBB ExtF) (row slot : ℕ) : FBB :=
  scheduleW7U16Limb air row slot 3

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

/-- Every schedule word on the 20 round rows of the block rooted at `start`
    is a boolean bit-vector. This is the block-local schedule-bit contract
    actually consumed by the schedule and round-step proof layers. -/
def scheduleBitsBooleanOnBlock (air : C FBB ExtF) (start : ℕ) : Prop :=
  ∀ offset slot, offset < 20 → slot < 4 →
    isBitsWord (scheduleBitsWord air (start + offset) slot)

/-! ## Digest helpers -/

/-- The `limb`-th 16-bit limb of digest `prev_hash[word]`.
    These columns are already stored as little-endian u16 limbs. -/
def digestPrevHashU16Limb (air : C FBB ExtF) (row word limb : ℕ) : FBB :=
  if limb < 4 then prev_hash air word limb row else 0

/-- The low 16-bit limb of digest `prev_hash[word]`. -/
def digestPrevHashLo16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  digestPrevHashU16Limb air row word 0

/-- The high 16-bit limb of digest `prev_hash[word]`. -/
def digestPrevHashHi16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  digestPrevHashU16Limb air row word 3

/-- All `prev_hash` u16 limbs on a digest row fit in `0 .. 2^16 - 1`. -/
def digestPrevHashLimbRange (air : C FBB ExtF) (row : ℕ) : Prop :=
  ∀ word limb, word < 8 → limb < 4 →
    (prev_hash air word limb row).val < 2 ^ 16

/-- The `limb`-th 16-bit limb of digest `final_hash[word]`, composed from
    little-endian byte pairs. -/
def digestFinalHashU16Limb (air : C FBB ExtF) (row word limb : ℕ) : FBB :=
  if limb < 4 then
    final_hash air word (2 * limb) row + final_hash air word (2 * limb + 1) row * 256
  else
    0

/-- The low 16-bit limb of digest `final_hash[word]`. -/
def digestFinalHashLo16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  digestFinalHashU16Limb air row word 0

/-- The high 16-bit limb of digest `final_hash[word]`. -/
def digestFinalHashHi16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  digestFinalHashU16Limb air row word 3

/-- Digest work-variable limb for word `w`.
    Words `0..3` map to `a[3-w]`, words `4..7` map to `e[7-w]`. -/
def digestWorkVarU16Limb (air : C FBB ExtF) (row word limb : ℕ) : FBB :=
  if hlimb : limb < 4 then
    if word < 4 then composeU16Limb (aBitsWord air row (3 - word)) ⟨limb, hlimb⟩
    else composeU16Limb (eBitsWord air row (7 - word)) ⟨limb, hlimb⟩
  else
    0

/-- The low 16-bit limb of the digest work variable for word `w`. -/
def digestWorkVarLo16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  digestWorkVarU16Limb air row word 0

/-- The high 16-bit limb of the digest work variable for word `w`. -/
def digestWorkVarHi16 (air : C FBB ExtF) (row word : ℕ) : FBB :=
  digestWorkVarU16Limb air row word 3

/-- The work variable corresponding to digest word `w`, as `UInt64`. -/
def digestWorkVarWord (air : C FBB ExtF) (row word : ℕ) : Word :=
  if word < 4 then aWord air row (3 - word)
  else eWord air row (7 - word)

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
