/-
  Layer B: Message Schedule Correctness (Block Window)

  Covers the field-to-UInt32 bridge and the full schedule correctness
  over a block window.

  Depends on: CarryPipeline, Recurrence, FieldArithmetic
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.Defs
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.FieldArithmetic
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.SelectorFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.MessageSchedule.CarryPipeline
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.MessageSchedule.Recurrence

set_option autoImplicit false

set_option maxHeartbeats 4000000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

theorem getElem!_push_lt {α : Type} [Inhabited α]
    {xs : Array α} {x : α} {i : Nat} (hi : i < xs.size) :
    (xs.push x)[i]! = xs[i]! := by
  simp [Array.getElem!_eq_getD, Array.getElem?_push, hi, Nat.ne_of_lt hi]

theorem getElem!_push_size {α : Type} [Inhabited α]
    {xs : Array α} {x : α} :
    (xs.push x)[xs.size]! = x := by
  rw [Array.getElem!_eq_getD]
  simp

private theorem getElem!_foldl_push_preserved {α β : Type} [Inhabited β]
    (l : List α) (f : Array β → α → β) (xs : Array β) (i : Nat) (hi : i < xs.size) :
    (l.foldl (fun acc a => acc.push (f acc a)) xs)[i]! = xs[i]! := by
  induction l generalizing xs with
  | nil =>
      rfl
  | cons a l ih =>
      simp [List.foldl]
      have hi' : i < (xs.push (f xs a)).size := by
        simpa using Nat.lt_succ_of_lt hi
      rw [ih (xs := xs.push (f xs a)) hi']
      exact getElem!_push_lt hi

private theorem foldl_push_size {α β : Type} [Inhabited β]
    (l : List α) (f : Array β → α → β) (xs : Array β) :
    (l.foldl (fun acc a => acc.push (f acc a)) xs).size = xs.size + l.length := by
  induction l generalizing xs with
  | nil =>
      simp
  | cons a l ih =>
      simp [List.foldl, ih, Nat.add_left_comm, Nat.add_comm]

private theorem expandSchedule_eq_foldl (input : Array Word) :
    expandSchedule input =
      (List.range 48).foldl
        (fun acc offset =>
          acc.push
            (smallSigma1 acc[offset + 14]! +
             acc[offset + 9]! +
             smallSigma0 acc[offset + 1]! +
             acc[offset]!))
        input := by
  simpa [expandSchedule] using
    (List.idRun_forIn_yield_eq_foldl
      (l := List.range 48)
      (f := fun offset acc =>
        pure
          (acc.push
            (smallSigma1 acc[offset + 14]! +
             acc[offset + 9]! +
             smallSigma0 acc[offset + 1]! +
             acc[offset]!)))
      (init := input))

/-! ## B5: Field-to-UInt32 bridge for schedule words

Combines schedule_recurrence_lo/hi + schedule_carry_bits_boolean +
schedule_carry_value_lt_four +
schedule_bits_boolean + intermed pipeline + w3_helper +
limbed_addition_three_inputs from FieldArithmetic
to get the UInt32-level recurrence. -/

/-- The intermed_12 pipeline correctly delivers the earlier `intermed_4` cell:
    `intermed_4` is written on the successor row, then carried through
    `intermed_8` and `intermed_12` on the next two rows. So at row `r`,
    `intermed_12[slot][limb]` equals `intermed_4[slot][limb]` from row `r - 2`.

    This chaining is needed to bridge the 3-row schedule pipeline. -/
theorem intermed_pipeline_delivers (air : C FBB ExtF) (start row : ℕ) (slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 2)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hrow : start + 3 ≤ row) (hrow_bound : row ≤ start + 14) :
    intermed_12 air slot limb row =
      intermed_4 air slot limb (row - 2) := by
  have hrow_lt_last : row < Circuit.last_row air := by
    have hsupp : start + 16 ≤ Circuit.last_row air := by
      simpa [blockWindowSupported] using hwindow
    omega
  have hnext_rowm1 : nextRow air (row - 1) = row := by
    have hne : row - 1 ≠ Circuit.last_row air := by
      omega
    have hsucc : nextRow air (row - 1) = row - 1 + 1 := by
      simp [nextRow, hne]
    omega
  have hnext_rowm2 : nextRow air (row - 2) = row - 1 := by
    have hne : row - 2 ≠ Circuit.last_row air := by
      omega
    have hsucc : nextRow air (row - 2) = row - 2 + 1 := by
      simp [nextRow, hne]
    omega
  have hsel_row :
      encoder_selector_idx air row = (((row - start : ℕ)) : FBB) := by
    have hoffset : row - start < 16 := by
      omega
    have hshape_row := hshape.2.1 (row - start) hoffset
    have hrow_eq : start + (row - start) = row := by
      omega
    simpa [hrow_eq] using hshape_row.1
  have hsel_rowm1 :
      encoder_selector_idx air (row - 1) = (((row - 1 - start : ℕ)) : FBB) := by
    have hoffset : row - 1 - start < 16 := by
      omega
    have hshape_row := hshape.2.1 (row - 1 - start) hoffset
    have hrow_eq : start + (row - 1 - start) = row - 1 := by
      omega
    simpa [hrow_eq] using hshape_row.1
  have hsel_row_next :
      encoder_selector_idx air (nextRow air (row - 1)) = ((row - start : ℕ) : FBB) := by
    simpa [hnext_rowm1] using hsel_row
  have hsel_rowm1_next :
      encoder_selector_idx air (nextRow air (row - 2)) = ((row - 1 - start : ℕ) : FBB) := by
    simpa [hnext_rowm2] using hsel_rowm1
  have hrow_offset_lo : 3 ≤ row - start := by
    omega
  have hrow_offset_hi : row - start ≤ 14 := by
    omega
  have hrowm1_offset_lo : 2 ≤ row - 1 - start := by
    omega
  have hrowm1_offset_hi : row - 1 - start ≤ 13 := by
    omega
  have h12 :=
    intermed_12_carry air (row - 1) slot limb hslot hlimb (by omega) hrot
      (hsc (row - 1)) (by simpa [hnext_rowm1] using hf row)
      ⟨row - start, hrow_offset_lo, hrow_offset_hi, hsel_row_next⟩
  have h8 :=
    intermed_8_carry air (row - 2) slot limb hslot hlimb (by omega) hrot
      (hsc (row - 2)) (by simpa [hnext_rowm2] using hf (row - 1))
      ⟨row - 1 - start, hrowm1_offset_lo, hrowm1_offset_hi, hsel_rowm1_next⟩
  have h12' : intermed_12 air slot limb row = intermed_8 air slot limb (row - 1) := by
    simpa [hnext_rowm1] using h12
  have h8' : intermed_8 air slot limb (row - 1) = intermed_4 air slot limb (row - 2) := by
    simpa [hnext_rowm2] using h8
  exact h12'.trans h8'

private theorem bitsWordToUInt32_toNat_eq_compose16 (bits : BitsWord) (hb : isBitsWord bits) :
    (bitsWordToUInt32 bits).toNat =
      (composeLo16 bits).val + (composeHi16 bits).val * 2 ^ 16 := by
  have hword :
      bitsWordToUInt32 bits =
        (((composeLo16 bits).val + (composeHi16 bits).val * 2 ^ 16).toUInt32) := by
    exact bitsWordToUInt32_eq_compose16 bits hb
  have hlt :
      (composeLo16 bits).val + (composeHi16 bits).val * 2 ^ 16 < 2 ^ 32 := by
    have hlo := composeLo16_val_lt bits hb
    have hhi := composeHi16_val_lt bits hb
    omega
  have hnat := congrArg UInt32.toNat hword
  have hnat_rhs :
      ((((composeLo16 bits).val + (composeHi16 bits).val * 2 ^ 16).toUInt32)).toNat =
        ((composeLo16 bits).val + (composeHi16 bits).val * 2 ^ 16) % 2 ^ 32 := by
    simpa using
      (UInt32.toNat_ofNat (n := (composeLo16 bits).val + (composeHi16 bits).val * 2 ^ 16))
  rw [Nat.mod_eq_of_lt hlt] at hnat_rhs
  exact hnat.trans hnat_rhs

private theorem schedule_recurrence_hi_for_addition (air : C FBB ExtF) (row slot : ℕ)
    (hslot : slot < 4)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) +
    scheduleW7Hi16 air row slot +
    intermed_12 air slot 1 row +
    scheduleCarryValue air (nextRow air row) slot 0 =
      composeHi16 (scheduleBitsWord air (nextRow air row) slot) +
      (next_msg_schedule_carry_or_buffer air slot 2 row +
        2 * next_msg_schedule_carry_or_buffer air slot 3 row) * (2 ^ 16 : ℕ) := by
  have h550_599 := constraints_550_599_of_schedule_constraints air row hs
  have h600_649 := constraints_600_649_of_schedule_constraints air row hs
  have h650_699 := constraints_650_699_of_schedule_constraints air row hs
  unfold constraints_550_599 at h550_599
  unfold constraints_600_649 at h600_649
  unfold constraints_650_699 at h650_699
  have hvalid : row ≤ Circuit.last_row air := hrow.le
  interval_cases slot
  · have h570 : constraint_570 air row := by tauto
    have h := schedule_recurrence_hi_slot0 air row hrow h570
    rw [rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 2 hrot hvalid,
      nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 0 hrot hvalid,
      nextScheduleCarryValue_eq_scheduleCarryValue_nextRow air row 0 0 hrot hvalid] at h
    calc
      composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row (0 + 2))) +
          scheduleW7Hi16 air row 0 +
          intermed_12 air 0 1 row +
          scheduleCarryValue air (nextRow air row) 0 0 =
          scheduleCarryValue air (nextRow air row) 0 0 +
          composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) +
          schedule_helper_w_3 air 0 1 row +
          intermed_12 air 0 1 row := by
            simp [scheduleW7Hi16]
            ring
      _ = composeHi16 (scheduleBitsWord air (nextRow air row) 0) +
          (next_msg_schedule_carry_or_buffer air 0 2 row +
            2 * next_msg_schedule_carry_or_buffer air 0 3 row) * (2 ^ 16 : ℕ) := h
  · have h608 : constraint_608 air row := by tauto
    have h := schedule_recurrence_hi_slot1 air row hrow h608
    rw [rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 3 hrot hvalid,
      nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 1 hrot hvalid,
      nextScheduleCarryValue_eq_scheduleCarryValue_nextRow air row 1 0 hrot hvalid] at h
    calc
      composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row (1 + 2))) +
          scheduleW7Hi16 air row 1 +
          intermed_12 air 1 1 row +
          scheduleCarryValue air (nextRow air row) 1 0 =
          scheduleCarryValue air (nextRow air row) 1 0 +
          composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row 3)) +
          schedule_helper_w_3 air 1 1 row +
          intermed_12 air 1 1 row := by
            simp [scheduleW7Hi16]
            ring
      _ = composeHi16 (scheduleBitsWord air (nextRow air row) 1) +
          (next_msg_schedule_carry_or_buffer air 1 2 row +
            2 * next_msg_schedule_carry_or_buffer air 1 3 row) * (2 ^ 16 : ℕ) := h
  · have h646 : constraint_646 air row := by tauto
    have h := schedule_recurrence_hi_slot2 air row hrow h646
    rw [rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 4 hrot hvalid,
      nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 2 hrot hvalid,
      nextScheduleCarryValue_eq_scheduleCarryValue_nextRow air row 2 0 hrot hvalid] at h
    calc
      composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row (2 + 2))) +
          scheduleW7Hi16 air row 2 +
          intermed_12 air 2 1 row +
          scheduleCarryValue air (nextRow air row) 2 0 =
          scheduleCarryValue air (nextRow air row) 2 0 +
          composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row 4)) +
          schedule_helper_w_3 air 2 1 row +
          intermed_12 air 2 1 row := by
            simp [scheduleW7Hi16]
            ring
      _ = composeHi16 (scheduleBitsWord air (nextRow air row) 2) +
          (next_msg_schedule_carry_or_buffer air 2 2 row +
            2 * next_msg_schedule_carry_or_buffer air 2 3 row) * (2 ^ 16 : ℕ) := h
  · have h684 : constraint_684 air row := by tauto
    have h := schedule_recurrence_hi_slot3 air row hrow h684
    rw [rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row 5 hrot hvalid,
      nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row 3 hrot hvalid,
      nextScheduleCarryValue_eq_scheduleCarryValue_nextRow air row 3 0 hrot hvalid] at h
    calc
      composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row (3 + 2))) +
          scheduleW7Hi16 air row 3 +
          intermed_12 air 3 1 row +
          scheduleCarryValue air (nextRow air row) 3 0 =
          scheduleCarryValue air (nextRow air row) 3 0 +
          composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row 5)) +
          concatScheduleHi16 air row 0 +
          intermed_12 air 3 1 row := by
            simp [scheduleW7Hi16]
            ring
      _ = composeHi16 (scheduleBitsWord air (nextRow air row) 3) +
          (next_msg_schedule_carry_or_buffer air 3 2 row +
            2 * next_msg_schedule_carry_or_buffer air 3 3 row) * (2 ^ 16 : ℕ) := h

/-- Sub-lemma 2: the lo/hi limb equations + decoded 2-bit carry bounds +
    explicit u16 no-wrap bounds for the helper/intermediate limbs +
    `limbed_addition_three_inputs`
    yield the packed 32-bit addition identity. -/
theorem schedule_recurrence_addition_uint32 (air : C FBB ExtF) (row slot : ℕ)
    (hslot : slot < 4)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hsc : ∀ r, schedule_constraints air r)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0)
    (hconcat_bits : isBitsWord (concatScheduleBitsWord air row (slot + 2)))
    (hw7_lo : (scheduleW7Lo16 air row slot).val < 2 ^ 16)
    (hw7_hi : (scheduleW7Hi16 air row slot).val < 2 ^ 16)
    (hint_lo : (intermed_12 air slot 0 row).val < 2 ^ 17)
    (hint_hi : (intermed_12 air slot 1 row).val < 2 ^ 17) :
    (((composeLo16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))).val +
       (composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))).val * 2 ^ 16) +
      ((scheduleW7Lo16 air row slot).val +
       (scheduleW7Hi16 air row slot).val * 2 ^ 16) +
      ((intermed_12 air slot 0 row).val +
       (intermed_12 air slot 1 row).val * 2 ^ 16)) ≡
    (composeLo16 (scheduleBitsWord air (nextRow air row) slot)).val +
    (composeHi16 (scheduleBitsWord air (nextRow air row) slot)).val * 2^16 [MOD 2^32] := by
  have hsigma_bits :
      isBitsWord (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) := by
    have hrot17 := fieldRotr_preserves_boolean (concatScheduleBitsWord air row (slot + 2)) 17
      hconcat_bits
    have hrot19 := fieldRotr_preserves_boolean (concatScheduleBitsWord air row (slot + 2)) 19
      hconcat_bits
    have hshr10 := fieldShr_preserves_boolean (concatScheduleBitsWord air row (slot + 2)) 10
      hconcat_bits
    intro i
    exact fieldXor_boolean_closed _ _
      (fieldXor_boolean_closed _ _ (hrot17 i) (hrot19 i))
      (hshr10 i)
  have hnext_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot) := by
    intro i
    simpa [scheduleBitsWord] using
      schedule_bits_boolean air row hrow.le hrot (hsc row) hround_next slot i.val hslot i.isLt
  set a_lo := composeLo16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))
  set a_hi := composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))
  set b_lo := scheduleW7Lo16 air row slot
  set b_hi := scheduleW7Hi16 air row slot
  set c_lo := intermed_12 air slot 0 row
  set c_hi := intermed_12 air slot 1 row
  set r_lo := composeLo16 (scheduleBitsWord air (nextRow air row) slot)
  set r_hi := composeHi16 (scheduleBitsWord air (nextRow air row) slot)
  set carry_lo := scheduleCarryValue air (nextRow air row) slot 0
  set carry_hi := next_msg_schedule_carry_or_buffer air slot 2 row +
    2 * next_msg_schedule_carry_or_buffer air slot 3 row
  have ha_lo : a_lo.val < 2 ^ 16 := by
    dsimp [a_lo]
    exact composeLo16_val_lt _ hsigma_bits
  have ha_hi : a_hi.val < 2 ^ 16 := by
    dsimp [a_hi]
    exact composeHi16_val_lt _ hsigma_bits
  have hr_lo : r_lo.val < 2 ^ 16 := by
    dsimp [r_lo]
    exact composeLo16_val_lt _ hnext_bits
  have hr_hi : r_hi.val < 2 ^ 16 := by
    dsimp [r_hi]
    exact composeHi16_val_lt _ hnext_bits
  have hcarry_lo_raw : carry_lo.val < 4 := by
    dsimp [carry_lo]
    simpa using
      schedule_carry_value_lt_four air row slot 0 hslot (by omega) hrow.le hrot (hsc row)
        hround_next hnot_first4_next
  have hcarry_hi_raw :
      carry_hi.val < 4 := by
    dsimp [carry_hi]
    simpa [nextScheduleCarryValue_eq_scheduleCarryValue_nextRow air row slot 1 hrot hrow.le] using
      schedule_carry_value_lt_four air row slot 1 hslot (by omega) hrow.le hrot (hsc row)
        hround_next hnot_first4_next
  have h_lo_field :
      a_lo + b_lo + c_lo = r_lo + carry_lo * (2 ^ 16 : ℕ) := by
    dsimp [a_lo, b_lo, c_lo, r_lo, carry_lo]
    exact schedule_recurrence_lo air row slot hslot hrow hrot (hsc row)
  have h_hi_field :
      a_hi + b_hi + c_hi + carry_lo = r_hi + carry_hi * (2 ^ 16 : ℕ) := by
    dsimp [a_hi, b_hi, c_hi, r_hi, carry_lo, carry_hi]
    exact schedule_recurrence_hi_for_addition air row slot hslot hrow hrot (hsc row) hround_next
  have h_lo_nat :
      a_lo.val + b_lo.val + c_lo.val = r_lo.val + carry_lo.val * 2 ^ 16 := by
    have h := congrArg Fin.val h_lo_field
    have hab :
        (a_lo + b_lo).val = a_lo.val + b_lo.val := by
      rw [babybear_add_no_wrap _ _ (by omega)]
    have habc :
        (a_lo + b_lo + c_lo).val = a_lo.val + b_lo.val + c_lo.val := by
      have hmid : (a_lo + b_lo).val + c_lo.val < BB_prime := by
        rw [hab]
        omega
      rw [babybear_add_no_wrap _ _ hmid, hab]
    have hcarry :
        (carry_lo * (2 ^ 16 : ℕ)).val = carry_lo.val * 2 ^ 16 := by
      exact small_carry_mul_65536_val carry_lo hcarry_lo_raw
    have hsum_r :
        (r_lo + carry_lo * (2 ^ 16 : ℕ)).val =
          r_lo.val + (carry_lo * (2 ^ 16 : ℕ)).val := by
      rw [babybear_add_no_wrap _ _ (by rw [hcarry]; omega)]
    rw [habc, hsum_r, hcarry] at h
    exact h
  have h_hi_nat :
      a_hi.val + b_hi.val + c_hi.val + carry_lo.val = r_hi.val + carry_hi.val * 2 ^ 16 := by
    have h := congrArg Fin.val h_hi_field
    have hab :
        (a_hi + b_hi).val = a_hi.val + b_hi.val := by
      rw [babybear_add_no_wrap _ _ (by omega)]
    have habc :
        (a_hi + b_hi + c_hi).val = a_hi.val + b_hi.val + c_hi.val := by
      have hmid : (a_hi + b_hi).val + c_hi.val < BB_prime := by
        rw [hab]
        omega
      rw [babybear_add_no_wrap _ _ hmid, hab]
    have habcc :
        (a_hi + b_hi + c_hi + carry_lo).val =
          a_hi.val + b_hi.val + c_hi.val + carry_lo.val := by
      have hmid : (a_hi + b_hi + c_hi).val + carry_lo.val < BB_prime := by
        rw [habc]
        omega
      rw [babybear_add_no_wrap _ _ hmid, habc]
    have hcarry :
        (carry_hi * (2 ^ 16 : ℕ)).val = carry_hi.val * 2 ^ 16 := by
      exact small_carry_mul_65536_val carry_hi hcarry_hi_raw
    have hsum_r :
        (r_hi + carry_hi * (2 ^ 16 : ℕ)).val =
          r_hi.val + (carry_hi * (2 ^ 16 : ℕ)).val := by
      rw [babybear_add_no_wrap _ _ (by rw [hcarry]; omega)]
    rw [habcc, hsum_r, hcarry] at h
    exact h
  change _ % (2 ^ 32) = _ % (2 ^ 32)
  omega

/-- Sub-lemma: the σ₁ term in the recurrence. Field-level σ₁ on boolean bits
    equals UInt32 smallSigma1. Uses fieldSmallSigma1_eq_smallSigma1 from Layer 0. -/
theorem schedule_sigma1_term (air : C FBB ExtF) (row slot : ℕ)
    (hbits : isBitsWord (concatScheduleBitsWord air row (slot + 2))) :
    bitsWordToUInt32 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) =
      smallSigma1 (concatScheduleWord air row (slot + 2)) := by
  simpa [concatScheduleWord] using
    fieldSmallSigma1_eq_smallSigma1 (concatScheduleBitsWord air row (slot + 2)) hbits

private theorem schedule_sigma1_term_nat (air : C FBB ExtF) (row slot : ℕ)
    (hbits : isBitsWord (concatScheduleBitsWord air row (slot + 2))) :
    (smallSigma1 (concatScheduleWord air row (slot + 2))).toNat =
      (composeLo16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))).val +
        (composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))).val * 2 ^ 16 := by
  have hsigma_bits :
      isBitsWord (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) := by
    have hrot17 := fieldRotr_preserves_boolean (concatScheduleBitsWord air row (slot + 2)) 17 hbits
    have hrot19 := fieldRotr_preserves_boolean (concatScheduleBitsWord air row (slot + 2)) 19 hbits
    have hshr10 := fieldShr_preserves_boolean (concatScheduleBitsWord air row (slot + 2)) 10 hbits
    intro i
    exact fieldXor_boolean_closed _ _
      (fieldXor_boolean_closed _ _ (hrot17 i) (hrot19 i))
      (hshr10 i)
  rw [(schedule_sigma1_term air row slot hbits).symm]
  exact bitsWordToUInt32_toNat_eq_compose16 _ hsigma_bits

private theorem scheduleBits_isBitsWord_from_block
    (air : C FBB ExtF) (start row slot : ℕ)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hslot : slot < 4)
    (hrow_lo : start ≤ row)
    (hrow_hi : row ≤ start + 15) :
    isBitsWord (scheduleBitsWord air row slot) := by
  have hrow_eq : start + (row - start) = row := by
    omega
  simpa [hrow_eq] using hsched_bits (row - start) slot (by omega) hslot

private theorem concatScheduleBits_isBitsWord_from_block
    (air : C FBB ExtF) (start row slot : ℕ)
    (hwindow : blockWindowSupported air start)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hslot : slot < 6)
    (hrow_lo : start ≤ row)
    (hrow_hi : row ≤ start + 14) :
    isBitsWord (concatScheduleBitsWord air row slot) := by
  have hsupp : start + 16 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    omega
  have hsucc : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  interval_cases slot
  · simpa [concatScheduleBitsWord] using
      scheduleBits_isBitsWord_from_block air start row 0 hsched_bits (by omega) hrow_lo
        (by omega)
  · simpa [concatScheduleBitsWord] using
      scheduleBits_isBitsWord_from_block air start row 1 hsched_bits (by omega) hrow_lo
        (by omega)
  · simpa [concatScheduleBitsWord] using
      scheduleBits_isBitsWord_from_block air start row 2 hsched_bits (by omega) hrow_lo
        (by omega)
  · simpa [concatScheduleBitsWord] using
      scheduleBits_isBitsWord_from_block air start row 3 hsched_bits (by omega) hrow_lo
        (by omega)
  · simpa [concatScheduleBitsWord, hsucc] using
      scheduleBits_isBitsWord_from_block air start (row + 1) 0 hsched_bits (by omega) (by omega)
        (by omega)
  · simpa [concatScheduleBitsWord, hsucc] using
      scheduleBits_isBitsWord_from_block air start (row + 1) 1 hsched_bits (by omega) (by omega)
        (by omega)

private theorem scheduleBits_isBitsWord_at_block_row
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hrow_lo : start + 1 ≤ row)
    (hrow_hi : row ≤ start + 15) :
    isBitsWord (scheduleBitsWord air row slot) := by
  intro bit
  have hsupp : start + 16 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hprev_le : prevRow air row ≤ Circuit.last_row air := by
    rw [hprev_eq]
    omega
  have hprev_next : nextRow air (prevRow air row) = row := by
    rw [hprev_eq, nextRow]
    have hne : row - 1 ≠ Circuit.last_row air := by
      omega
    simp [hne]
    omega
  have hoffset : row - start < 16 := by
    omega
  have hshape_row := hshape.2.1 (row - start) hoffset
  have hrow_eq : start + (row - start) = row := by
    omega
  have hnext_round : next_is_round_row air (prevRow air row) = 1 := by
    rw [next_is_round_row_eq_nextRow air hrot (prevRow air row) hprev_le, hprev_next]
    simpa [hrow_eq] using hshape_row.2.1
  simpa [scheduleBitsWord, hprev_next] using
    schedule_bits_boolean air (prevRow air row) hprev_le hrot (hsc (prevRow air row))
      hnext_round slot bit hslot bit.isLt

/-- Sub-lemma: the w[t-7] term uses the w3_helper, which stores compose16
    of the correct word from 3 rows back via the pipeline. -/
theorem schedule_w7_from_helper (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 3)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row) (hnext_bound : nextRow air row ≤ start + 15) :
    let t := (nextRow air row - start) * 4 + slot
    (schedule_helper_w_3 air slot 0 row).val +
    (schedule_helper_w_3 air slot 1 row).val * 2^16 ≡
    (scheduleWordAtRow air (start + (t - 7) / 4) ((t - 7) % 4)).toNat [MOD 2^32] := by
  dsimp
  have hsupp : start + 16 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by simp [nextRow, hlast]
      omega
  have hrow_pos : 0 < row := by
    have hsucc : nextRow air row = row + 1 := by simp [nextRow, hrow_lt_last.ne]
    omega
  have hsucc : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hprev_le : prevRow air row ≤ Circuit.last_row air := by
    rw [hprev_eq]
    omega
  have hprev_next : nextRow air (prevRow air row) = row := by
    rw [hprev_eq, nextRow]
    have hne : row - 1 ≠ Circuit.last_row air := by
      omega
    simp [hne]
    omega
  have hslot1 : slot + 1 < 4 := by
    omega
  have hnext_succ : start + 4 ≤ row + 1 := by
    simpa [hsucc] using hnext
  have hnext_bound_succ : row + 1 ≤ start + 15 := by
    simpa [hsucc] using hnext_bound
  have hprev_round : is_round_row air (prevRow air row) = 1 := by
    have hprev_lo : start + 2 ≤ prevRow air row := by
      rw [hprev_eq]
      omega
    have hprev_hi : prevRow air row ≤ start + 13 := by
      rw [hprev_eq]
      omega
    have hoffset : prevRow air row - start < 16 := by
      omega
    have hshape_prev := hshape.2.1 (prevRow air row - start) hoffset
    have hrow_eq : start + (prevRow air row - start) = prevRow air row := by
      omega
    simpa [hrow_eq] using hshape_prev.2.1
  have hw3_lo :
      schedule_helper_w_3 air slot 0 row =
        composeLo16 (scheduleBitsWord air (prevRow air row) (slot + 1)) := by
    have hraw :=
      w3_helper_correct air (prevRow air row) slot 0 hslot (by omega) hprev_le hrot
        (hsc (prevRow air row)) hprev_round
    rw [hprev_next] at hraw
    simpa [concatScheduleLo16, concatScheduleBitsWord, hslot1] using hraw
  have hw3_hi :
      schedule_helper_w_3 air slot 1 row =
        composeHi16 (scheduleBitsWord air (prevRow air row) (slot + 1)) := by
    have hraw :=
      w3_helper_correct air (prevRow air row) slot 1 hslot (by omega) hprev_le hrot
        (hsc (prevRow air row)) hprev_round
    rw [hprev_next] at hraw
    simpa [concatScheduleHi16, concatScheduleBitsWord, hslot1] using hraw
  have hbits :
      isBitsWord (scheduleBitsWord air (prevRow air row) (slot + 1)) := by
    apply scheduleBits_isBitsWord_at_block_row air start (prevRow air row) (slot + 1) (by omega)
      hwindow hrot hshape hsc
    · rw [hprev_eq]
      omega
    · rw [hprev_eq]
      omega
  have hword :
      scheduleWordAtRow air (prevRow air row) (slot + 1) =
        (((schedule_helper_w_3 air slot 0 row).val +
            (schedule_helper_w_3 air slot 1 row).val * 2 ^ 16).toUInt32) := by
    rw [scheduleWordAtRow_eq_bitsWordToUInt32, bitsWordToUInt32_eq_compose16 _ hbits, hw3_lo, hw3_hi]
  have hhelper_lt :
      (schedule_helper_w_3 air slot 0 row).val +
        (schedule_helper_w_3 air slot 1 row).val * 2 ^ 16 < 2 ^ 32 := by
    rw [hw3_lo, hw3_hi]
    have hlo := composeLo16_val_lt (scheduleBitsWord air (prevRow air row) (slot + 1)) hbits
    have hhi := composeHi16_val_lt (scheduleBitsWord air (prevRow air row) (slot + 1)) hbits
    omega
  have hword_nat :
      (scheduleWordAtRow air (prevRow air row) (slot + 1)).toNat =
        (schedule_helper_w_3 air slot 0 row).val +
          (schedule_helper_w_3 air slot 1 row).val * 2 ^ 16 := by
    have hnat := congrArg UInt32.toNat hword
    have hnat_rhs :
        ((((schedule_helper_w_3 air slot 0 row).val +
            (schedule_helper_w_3 air slot 1 row).val * 2 ^ 16).toUInt32)).toNat =
          ((schedule_helper_w_3 air slot 0 row).val +
            (schedule_helper_w_3 air slot 1 row).val * 2 ^ 16) % 2 ^ 32 := by
      simpa using
        (UInt32.toNat_ofNat
          (n := (schedule_helper_w_3 air slot 0 row).val +
            (schedule_helper_w_3 air slot 1 row).val * 2 ^ 16))
    rw [Nat.mod_eq_of_lt hhelper_lt] at hnat_rhs
    exact hnat.trans hnat_rhs
  have htarget_row :
      start + ((((nextRow air row - start) * 4 + slot) - 7) / 4) = prevRow air row := by
    rw [hprev_eq]
    have hsucc : nextRow air row = row + 1 := by simp [nextRow, hrow_lt_last.ne]
    omega
  have htarget_slot :
      ((((nextRow air row - start) * 4 + slot) - 7) % 4) = slot + 1 := by
    omega
  rw [htarget_row, htarget_slot]
  simpa [hword_nat] using
    (Nat.ModEq.refl ((scheduleWordAtRow air (prevRow air row) (slot + 1)).toNat) :
      (scheduleWordAtRow air (prevRow air row) (slot + 1)).toNat ≡
        (scheduleWordAtRow air (prevRow air row) (slot + 1)).toNat [MOD 2 ^ 32])

private theorem schedule_w7_from_source (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row) (hnext_bound : nextRow air row ≤ start + 15) :
    let t := (nextRow air row - start) * 4 + slot
    (scheduleW7Lo16 air row slot).val +
    (scheduleW7Hi16 air row slot).val * 2^16 ≡
    (scheduleWordAtRow air (start + (t - 7) / 4) ((t - 7) % 4)).toNat [MOD 2^32] := by
  dsimp
  interval_cases slot
  · simpa using
      schedule_w7_from_helper air start row 0 (by omega) hwindow hrot hshape hsc hnext
        hnext_bound
  · simpa using
      schedule_w7_from_helper air start row 1 (by omega) hwindow hrot hshape hsc hnext
        hnext_bound
  · simpa using
      schedule_w7_from_helper air start row 2 (by omega) hwindow hrot hshape hsc hnext
        hnext_bound
  · have hsupp : start + 16 ≤ Circuit.last_row air := by
      simpa [blockWindowSupported] using hwindow
    have hrow_lt_last : row < Circuit.last_row air := by
      by_cases hlast : row = Circuit.last_row air
      · have hzero : nextRow air row = 0 := by simp [nextRow, hlast]
        omega
      · have hsucc : nextRow air row = row + 1 := by simp [nextRow, hlast]
        omega
    have hnext_succ : nextRow air row = row + 1 := by
      simp [nextRow, hrow_lt_last.ne]
    have hrow_lo : start ≤ row := by
      omega
    have hrow_hi : row ≤ start + 15 := by
      omega
    have hrow_hi' : row ≤ start + 14 := by
      simpa [hnext_succ] using hnext_bound
    have hbits :
        isBitsWord (scheduleBitsWord air row 0) := by
      exact
        scheduleBits_isBitsWord_from_block air start row 0 hsched_bits (by omega) hrow_lo hrow_hi
    have hword_nat :
        (scheduleWordAtRow air row 0).toNat =
          (concatScheduleLo16 air row 0).val +
            (concatScheduleHi16 air row 0).val * 2 ^ 16 := by
      rw [scheduleWordAtRow_eq_bitsWordToUInt32]
      simpa [concatScheduleLo16, concatScheduleHi16, concatScheduleBitsWord] using
        bitsWordToUInt32_toNat_eq_compose16 (scheduleBitsWord air row 0) hbits
    have htarget_row :
        start + ((((nextRow air row - start) * 4 + 3) - 7) / 4) = row := by
      rw [hnext_succ]
      omega
    have htarget_slot :
        ((((nextRow air row - start) * 4 + 3) - 7) % 4) = 0 := by
      rw [hnext_succ]
      omega
    rw [htarget_row, htarget_slot]
    simpa [scheduleW7Lo16, scheduleW7Hi16, hword_nat, concatScheduleLo16, concatScheduleHi16,
      concatScheduleBitsWord] using
      (Nat.ModEq.refl ((scheduleWordAtRow air row 0).toNat) :
        (scheduleWordAtRow air row 0).toNat ≡
          (scheduleWordAtRow air row 0).toNat [MOD 2 ^ 32])

private theorem scheduleW7_bounds_from_helper (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 3)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row) (hnext_bound : nextRow air row ≤ start + 15) :
    (scheduleW7Lo16 air row slot).val < 2 ^ 16 ∧
      (scheduleW7Hi16 air row slot).val < 2 ^ 16 := by
  have hsupp : start + 16 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by simp [nextRow, hlast]
      omega
  have hrow_pos : 0 < row := by
    have hsucc : nextRow air row = row + 1 := by simp [nextRow, hrow_lt_last.ne]
    omega
  have hsucc : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hprev_le : prevRow air row ≤ Circuit.last_row air := by
    rw [hprev_eq]
    omega
  have hprev_next : nextRow air (prevRow air row) = row := by
    rw [hprev_eq, nextRow]
    have hne : row - 1 ≠ Circuit.last_row air := by
      omega
    simp [hne]
    omega
  have hslot1 : slot + 1 < 4 := by
    omega
  have hprev_round : is_round_row air (prevRow air row) = 1 := by
    have hoffset : prevRow air row - start < 16 := by
      rw [hprev_eq]
      omega
    have hshape_prev := hshape.2.1 (prevRow air row - start) hoffset
    have hrow_eq : start + (prevRow air row - start) = prevRow air row := by
      omega
    simpa [hrow_eq] using hshape_prev.2.1
  have hw3_lo :
      schedule_helper_w_3 air slot 0 row =
        composeLo16 (scheduleBitsWord air (prevRow air row) (slot + 1)) := by
    have hraw :=
      w3_helper_correct air (prevRow air row) slot 0 hslot (by omega) hprev_le hrot
        (hsc (prevRow air row)) hprev_round
    rw [hprev_next] at hraw
    simpa [concatScheduleLo16, concatScheduleBitsWord, hslot1] using hraw
  have hw3_hi :
      schedule_helper_w_3 air slot 1 row =
        composeHi16 (scheduleBitsWord air (prevRow air row) (slot + 1)) := by
    have hraw :=
      w3_helper_correct air (prevRow air row) slot 1 hslot (by omega) hprev_le hrot
        (hsc (prevRow air row)) hprev_round
    rw [hprev_next] at hraw
    simpa [concatScheduleHi16, concatScheduleBitsWord, hslot1] using hraw
  have hbits :
      isBitsWord (scheduleBitsWord air (prevRow air row) (slot + 1)) := by
    apply scheduleBits_isBitsWord_at_block_row air start (prevRow air row) (slot + 1) (by omega)
      hwindow hrot hshape hsc
    · rw [hprev_eq]
      omega
    · rw [hprev_eq]
      omega
  constructor
  · rw [scheduleW7Lo16, if_pos hslot, hw3_lo]
    exact composeLo16_val_lt _ hbits
  · rw [scheduleW7Hi16, if_pos hslot, hw3_hi]
    exact composeHi16_val_lt _ hbits

private theorem scheduleW7_bounds_from_source (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row) (hnext_bound : nextRow air row ≤ start + 15) :
    (scheduleW7Lo16 air row slot).val < 2 ^ 16 ∧
      (scheduleW7Hi16 air row slot).val < 2 ^ 16 := by
  interval_cases slot
  · exact scheduleW7_bounds_from_helper air start row 0 (by omega) hwindow hrot hshape hsc hnext
      hnext_bound
  · exact scheduleW7_bounds_from_helper air start row 1 (by omega) hwindow hrot hshape hsc hnext
      hnext_bound
  · exact scheduleW7_bounds_from_helper air start row 2 (by omega) hwindow hrot hshape hsc hnext
      hnext_bound
  · have hsupp : start + 16 ≤ Circuit.last_row air := by
      simpa [blockWindowSupported] using hwindow
    have hrow_lt_last : row < Circuit.last_row air := by
      by_cases hlast : row = Circuit.last_row air
      · have hzero : nextRow air row = 0 := by simp [nextRow, hlast]
        omega
      · have hsucc : nextRow air row = row + 1 := by simp [nextRow, hlast]
        omega
    have hnext_succ : nextRow air row = row + 1 := by
      simp [nextRow, hrow_lt_last.ne]
    have hrow_lo : start ≤ row := by
      omega
    have hrow_hi : row ≤ start + 15 := by
      omega
    have hrow_hi' : row ≤ start + 14 := by
      simpa [hnext_succ] using hnext_bound
    have hbits :
        isBitsWord (scheduleBitsWord air row 0) := by
      exact
        scheduleBits_isBitsWord_from_block air start row 0 hsched_bits (by omega) hrow_lo hrow_hi
    constructor
    · simpa [scheduleW7Lo16, concatScheduleLo16, concatScheduleBitsWord] using
        composeLo16_val_lt (scheduleBitsWord air row 0) hbits
    · simpa [scheduleW7Hi16, concatScheduleHi16, concatScheduleBitsWord] using
        composeHi16_val_lt (scheduleBitsWord air row 0) hbits

private theorem intermed12_u17_bounds_from_pipeline (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row) (hnext_bound : nextRow air row ≤ start + 15) :
    (intermed_12 air slot 0 row).val < 2 ^ 17 ∧
      (intermed_12 air slot 1 row).val < 2 ^ 17 := by
  have hsupp : start + 16 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by simp [nextRow, hlast]
      omega
  have hsucc : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hsucc] using hnext
  have hrow_hi : row ≤ start + 14 := by
    simpa [hsucc] using hnext_bound
  have hpipe_lo :=
    intermed_pipeline_delivers air start row slot 0 hslot (by omega)
      hwindow hrot hshape hf hsc hrow_lo hrow_hi
  have hpipe_hi :=
    intermed_pipeline_delivers air start row slot 1 hslot (by omega)
      hwindow hrot hshape hf hsc hrow_lo hrow_hi
  have hrowm3_lt_last : row - 3 < Circuit.last_row air := by
    omega
  have hnext_rowm3 : nextRow air (row - 3) = row - 2 := by
    simp [nextRow, hrowm3_lt_last.ne]
    omega
  have h4_lo_raw :=
    intermed_4_correct air (row - 3) slot 0 hslot (by omega) hrowm3_lt_last hrot (hsc (row - 3))
  have h4_hi_raw :=
    intermed_4_correct air (row - 3) slot 1 hslot (by omega) hrowm3_lt_last hrot (hsc (row - 3))
  have h4_lo :
      intermed_4 air slot 0 (row - 2) =
        concatScheduleLo16 air (row - 3) slot +
          composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    simpa [hnext_rowm3] using h4_lo_raw
  have h4_hi :
      intermed_4 air slot 1 (row - 2) =
        concatScheduleHi16 air (row - 3) slot +
          composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    simpa [hnext_rowm3] using h4_hi_raw
  have hword_bits :
      isBitsWord (scheduleBitsWord air (row - 3) slot) := by
    exact scheduleBits_isBitsWord_from_block air start (row - 3) slot hsched_bits hslot (by omega)
      (by omega)
  have hconcat_bits :
      isBitsWord (concatScheduleBitsWord air (row - 3) (slot + 1)) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (row - 3) (slot + 1) hwindow hsched_bits
        (by omega) (by omega) (by omega)
  have hsigma_bits :
      isBitsWord (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    have hrot7 :=
      fieldRotr_preserves_boolean (concatScheduleBitsWord air (row - 3) (slot + 1)) 7 hconcat_bits
    have hrot18 :=
      fieldRotr_preserves_boolean (concatScheduleBitsWord air (row - 3) (slot + 1)) 18 hconcat_bits
    have hshr3 :=
      fieldShr_preserves_boolean (concatScheduleBitsWord air (row - 3) (slot + 1)) 3 hconcat_bits
    intro i
    exact fieldXor_boolean_closed _ _
      (fieldXor_boolean_closed _ _ (hrot7 i) (hrot18 i))
      (hshr3 i)
  have hw_lo_lt : (concatScheduleLo16 air (row - 3) slot).val < 2 ^ 16 := by
    simpa [concatScheduleLo16, concatScheduleBitsWord, hslot] using
      composeLo16_val_lt (scheduleBitsWord air (row - 3) slot) hword_bits
  have hw_hi_lt : (concatScheduleHi16 air (row - 3) slot).val < 2 ^ 16 := by
    simpa [concatScheduleHi16, concatScheduleBitsWord, hslot] using
      composeHi16_val_lt (scheduleBitsWord air (row - 3) slot) hword_bits
  have hsig_lo_lt :
      (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val <
        2 ^ 16 := by
    exact composeLo16_val_lt _ hsigma_bits
  have hsig_hi_lt :
      (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val <
        2 ^ 16 := by
    exact composeHi16_val_lt _ hsigma_bits
  have hlo_eq :
      intermed_12 air slot 0 row =
        concatScheduleLo16 air (row - 3) slot +
          composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    exact hpipe_lo.trans h4_lo
  have hhi_eq :
      intermed_12 air slot 1 row =
        concatScheduleHi16 air (row - 3) slot +
          composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    exact hpipe_hi.trans h4_hi
  have hlo_val :
      (intermed_12 air slot 0 row).val =
        (concatScheduleLo16 air (row - 3) slot).val +
          (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val := by
    have hsum_lt :
        (concatScheduleLo16 air (row - 3) slot).val +
            (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val <
          BB_prime := by
      omega
    have h := congrArg Fin.val hlo_eq
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    exact h
  have hhi_val :
      (intermed_12 air slot 1 row).val =
        (concatScheduleHi16 air (row - 3) slot).val +
          (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val := by
    have hsum_lt :
        (concatScheduleHi16 air (row - 3) slot).val +
            (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val <
          BB_prime := by
      omega
    have h := congrArg Fin.val hhi_eq
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    exact h
  constructor
  · rw [hlo_val]
    omega
  · rw [hhi_val]
    omega

/-- Sub-lemma: the w[t-16] + σ₀(w[t-15]) term from the intermed pipeline. -/
theorem schedule_w16_sigma0_from_pipeline (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row) (hnext_bound : nextRow air row ≤ start + 15) :
    (intermed_12 air slot 0 row).val +
    (intermed_12 air slot 1 row).val * 2^16 ≡
    ((scheduleWordAtRow air (row - 3) slot).toNat +
     (smallSigma0 (concatScheduleWord air (row - 3) (slot + 1))).toNat) [MOD 2^32] := by
  have hsupp : start + 16 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by simp [nextRow, hlast]
      omega
  have hsucc : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hsucc] using hnext
  have hrow_hi : row ≤ start + 14 := by
    simpa [hsucc] using hnext_bound
  have hpipe_lo :=
    intermed_pipeline_delivers air start row slot 0 hslot (by omega)
      hwindow hrot hshape hf hsc hrow_lo hrow_hi
  have hpipe_hi :=
    intermed_pipeline_delivers air start row slot 1 hslot (by omega)
      hwindow hrot hshape hf hsc hrow_lo hrow_hi
  have hrowm3_lt_last : row - 3 < Circuit.last_row air := by
    omega
  have hnext_rowm3 : nextRow air (row - 3) = row - 2 := by
    simp [nextRow, hrowm3_lt_last.ne]
    omega
  have h4_lo_raw :=
    intermed_4_correct air (row - 3) slot 0 hslot (by omega) hrowm3_lt_last hrot (hsc (row - 3))
  have h4_hi_raw :=
    intermed_4_correct air (row - 3) slot 1 hslot (by omega) hrowm3_lt_last hrot (hsc (row - 3))
  have h4_lo :
      intermed_4 air slot 0 (row - 2) =
        concatScheduleLo16 air (row - 3) slot +
          composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    simpa [hnext_rowm3] using h4_lo_raw
  have h4_hi :
      intermed_4 air slot 1 (row - 2) =
        concatScheduleHi16 air (row - 3) slot +
          composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    simpa [hnext_rowm3] using h4_hi_raw
  have hrowm3_eq : start + (row - 3 - start) = row - 3 := by
    omega
  have hrowm2_eq : start + (row - 2 - start) = row - 2 := by
    omega
  have hword_bits : isBitsWord (scheduleBitsWord air (row - 3) slot) := by
    simpa [hrowm3_eq] using
      hsched_bits (row - 3 - start) slot (by omega) hslot
  have hconcat_bits : isBitsWord (concatScheduleBitsWord air (row - 3) (slot + 1)) := by
    interval_cases slot
    · simpa [concatScheduleBitsWord, hrowm3_eq] using
        hsched_bits (row - 3 - start) 1 (by omega) (by omega)
    · simpa [concatScheduleBitsWord, hrowm3_eq] using
        hsched_bits (row - 3 - start) 2 (by omega) (by omega)
    · simpa [concatScheduleBitsWord, hrowm3_eq] using
        hsched_bits (row - 3 - start) 3 (by omega) (by omega)
    · simpa [concatScheduleBitsWord, hnext_rowm3, hrowm2_eq] using
        hsched_bits (row - 2 - start) 0 (by omega) (by omega)
  have hsigma_bits :
      isBitsWord (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    have hrot7 :=
      fieldRotr_preserves_boolean (concatScheduleBitsWord air (row - 3) (slot + 1)) 7 hconcat_bits
    have hrot18 :=
      fieldRotr_preserves_boolean (concatScheduleBitsWord air (row - 3) (slot + 1)) 18 hconcat_bits
    have hshr3 :=
      fieldShr_preserves_boolean (concatScheduleBitsWord air (row - 3) (slot + 1)) 3 hconcat_bits
    intro i
    exact fieldXor_boolean_closed _ _
      (fieldXor_boolean_closed _ _ (hrot7 i) (hrot18 i))
      (hshr3 i)
  have hw_lo_lt : (concatScheduleLo16 air (row - 3) slot).val < 2 ^ 16 := by
    simpa [concatScheduleLo16, concatScheduleBitsWord, hslot] using
      composeLo16_val_lt (scheduleBitsWord air (row - 3) slot) hword_bits
  have hw_hi_lt : (concatScheduleHi16 air (row - 3) slot).val < 2 ^ 16 := by
    simpa [concatScheduleHi16, concatScheduleBitsWord, hslot] using
      composeHi16_val_lt (scheduleBitsWord air (row - 3) slot) hword_bits
  have hsig_lo_lt :
      (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val <
        2 ^ 16 := by
    exact composeLo16_val_lt _ hsigma_bits
  have hsig_hi_lt :
      (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val <
        2 ^ 16 := by
    exact composeHi16_val_lt _ hsigma_bits
  have hlo_eq :
      intermed_12 air slot 0 row =
        concatScheduleLo16 air (row - 3) slot +
          composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    exact hpipe_lo.trans h4_lo
  have hhi_eq :
      intermed_12 air slot 1 row =
        concatScheduleHi16 air (row - 3) slot +
          composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    exact hpipe_hi.trans h4_hi
  have hlo_val :
      (intermed_12 air slot 0 row).val =
        (concatScheduleLo16 air (row - 3) slot).val +
          (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val := by
    have hsum_lt :
        (concatScheduleLo16 air (row - 3) slot).val +
            (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val <
          BB_prime := by
      omega
    have h := congrArg Fin.val hlo_eq
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    exact h
  have hhi_val :
      (intermed_12 air slot 1 row).val =
        (concatScheduleHi16 air (row - 3) slot).val +
          (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val := by
    have hsum_lt :
        (concatScheduleHi16 air (row - 3) slot).val +
            (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val <
          BB_prime := by
      omega
    have h := congrArg Fin.val hhi_eq
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    exact h
  have hword :
      scheduleWordAtRow air (row - 3) slot =
        (((concatScheduleLo16 air (row - 3) slot).val +
            (concatScheduleHi16 air (row - 3) slot).val * 2 ^ 16).toUInt32) := by
    rw [scheduleWordAtRow_eq_bitsWordToUInt32]
    simpa [concatScheduleLo16, concatScheduleHi16, concatScheduleBitsWord, hslot] using
      bitsWordToUInt32_eq_compose16 (scheduleBitsWord air (row - 3) slot) hword_bits
  have hword_nat :
      (scheduleWordAtRow air (row - 3) slot).toNat =
        (concatScheduleLo16 air (row - 3) slot).val +
          (concatScheduleHi16 air (row - 3) slot).val * 2 ^ 16 := by
    have hword_lt :
        (concatScheduleLo16 air (row - 3) slot).val +
            (concatScheduleHi16 air (row - 3) slot).val * 2 ^ 16 <
          2 ^ 32 := by
      omega
    have hnat := congrArg UInt32.toNat hword
    have hnat_rhs :
        ((((concatScheduleLo16 air (row - 3) slot).val +
            (concatScheduleHi16 air (row - 3) slot).val * 2 ^ 16).toUInt32)).toNat =
          ((concatScheduleLo16 air (row - 3) slot).val +
            (concatScheduleHi16 air (row - 3) slot).val * 2 ^ 16) % 2 ^ 32 := by
      simpa using
        (UInt32.toNat_ofNat
          (n := (concatScheduleLo16 air (row - 3) slot).val +
            (concatScheduleHi16 air (row - 3) slot).val * 2 ^ 16))
    rw [Nat.mod_eq_of_lt hword_lt] at hnat_rhs
    exact hnat.trans hnat_rhs
  have hsigma_word :
      smallSigma0 (concatScheduleWord air (row - 3) (slot + 1)) =
        (((composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val +
            (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val *
              2 ^ 16).toUInt32) := by
    have hpack :
        bitsWordToUInt32 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) =
          (((composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val +
              (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val *
                2 ^ 16).toUInt32) := by
      exact
        bitsWordToUInt32_eq_compose16
          (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) hsigma_bits
    exact
      (fieldSmallSigma0_eq_smallSigma0
        (concatScheduleBitsWord air (row - 3) (slot + 1)) hconcat_bits).symm.trans hpack
  have hsigma_nat :
      (smallSigma0 (concatScheduleWord air (row - 3) (slot + 1))).toNat =
        (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val +
          (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val *
            2 ^ 16 := by
    have hsigma_lt :
        (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val +
            (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val *
              2 ^ 16 <
          2 ^ 32 := by
      omega
    have hnat := congrArg UInt32.toNat hsigma_word
    have hnat_rhs :
        ((((composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val +
            (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val *
              2 ^ 16).toUInt32)).toNat =
          ((composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val +
            (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val *
              2 ^ 16) % 2 ^ 32 := by
      simpa using
        (UInt32.toNat_ofNat
          (n := (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val +
            (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val *
              2 ^ 16))
    rw [Nat.mod_eq_of_lt hsigma_lt] at hnat_rhs
    exact hnat.trans hnat_rhs
  have hlhs :
      (intermed_12 air slot 0 row).val +
          (intermed_12 air slot 1 row).val * 2 ^ 16 =
        ((concatScheduleLo16 air (row - 3) slot).val +
            (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val) +
          ((concatScheduleHi16 air (row - 3) slot).val +
              (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val) *
            2 ^ 16 := by
    rw [hlo_val, hhi_val]
  have hsum :
      ((concatScheduleLo16 air (row - 3) slot).val +
            (composeLo16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val) +
          ((concatScheduleHi16 air (row - 3) slot).val +
              (composeHi16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).val) *
            2 ^ 16 =
        (scheduleWordAtRow air (row - 3) slot).toNat +
          (smallSigma0 (concatScheduleWord air (row - 3) (slot + 1))).toNat := by
    rw [hword_nat, hsigma_nat]
    omega
  rw [hlhs, hsum]

/-- Combined: field-level recurrence → UInt32 recurrence.
    Assembly: schedule_recurrence_lo/hi + carry-bit booleanness + carry-value bounds
    + schedule_sigma1_term + schedule_w7_from_helper + schedule_w16_sigma0_from_pipeline
    + limbed_addition. -/
theorem schedule_recurrence_uint32 (air : C FBB ExtF) (start row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row) (hnext_bound : nextRow air row ≤ start + 15) :
    let t := (nextRow air row - start) * 4 + slot
    scheduleWordAtRow air (nextRow air row) slot =
      smallSigma1 (scheduleWordAtRow air (start + (t - 2) / 4) ((t - 2) % 4)) +
      scheduleWordAtRow air (start + (t - 7) / 4) ((t - 7) % 4) +
      smallSigma0 (scheduleWordAtRow air (start + (t - 15) / 4) ((t - 15) % 4)) +
      scheduleWordAtRow air (start + (t - 16) / 4) ((t - 16) % 4) := by
  dsimp
  have hsupp : start + 16 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hnext_succ] using hnext
  have hrow_hi : row ≤ start + 14 := by
    simpa [hnext_succ] using hnext_bound
  have hnext_lo : start ≤ nextRow air row := by
    omega
  have hoffset_next : nextRow air row - start < 16 := by
    omega
  have hshape_next := hshape.2.1 (nextRow air row - start) hoffset_next
  have hnext_eq : start + (nextRow air row - start) = nextRow air row := by
    omega
  have hround_row_next : is_round_row air (nextRow air row) = 1 := by
    simpa [hnext_eq] using hshape_next.2.1
  have hround_next : next_is_round_row air row = 1 := by
    rw [next_is_round_row_eq_nextRow air hrot row hrow_lt_last.le]
    exact hround_row_next
  have hnot_first4_row_next : is_first_4_rows air (nextRow air row) = 0 := by
    rcases is_first_4_rows_boolean air (nextRow air row) (hf (nextRow air row)) with
      hfirst4 | hfirst4
    · exact hfirst4
    · rcases
        (is_first_4_iff_selector_lt_4 air (nextRow air row) (hf (nextRow air row))).1 hfirst4
          with ⟨n, hnlt, hnsel⟩
      have hsel_next :
          encoder_selector_idx air (nextRow air row) = ((nextRow air row - start : ℕ) : FBB) := by
        simpa [hnext_eq] using hshape_next.1
      have hcast :
          ((nextRow air row - start : ℕ) : FBB) = ((n : ℕ) : FBB) := hsel_next.symm.trans hnsel
      have hval := congrArg Fin.val hcast
      have hoffset_prime : nextRow air row - start < BB_prime := by
        omega
      have hn_prime : n < BB_prime := by
        omega
      simp [Nat.mod_eq_of_lt hoffset_prime, Nat.mod_eq_of_lt hn_prime] at hval
      have hge4 : 4 ≤ nextRow air row - start := by
        omega
      omega
  have hnot_first4_next : next_is_first_4_rows air row = 0 := by
    rw [next_is_first_4_rows_eq_nextRow air hrot row hrow_lt_last.le]
    exact hnot_first4_row_next
  have hconcat_bits : isBitsWord (concatScheduleBitsWord air row (slot + 2)) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start row (slot + 2) hwindow hsched_bits
        (by omega) (by omega) hrow_hi
  have ⟨hw7_lo, hw7_hi⟩ :=
    scheduleW7_bounds_from_source air start row slot hslot hwindow hrot hshape hsc hsched_bits
      hnext hnext_bound
  have ⟨hint_lo, hint_hi⟩ :=
    intermed12_u17_bounds_from_pipeline air start row slot hslot hwindow hrot hshape hf hsc
      hsched_bits hnext hnext_bound
  have hadd :=
    schedule_recurrence_addition_uint32 air row slot hslot hrow_lt_last hrot hsc hround_next
      hnot_first4_next hconcat_bits hw7_lo hw7_hi hint_lo hint_hi
  have hsigma_nat :=
    schedule_sigma1_term_nat air row slot hconcat_bits
  have hw7_mod :=
    schedule_w7_from_source air start row slot hslot hwindow hrot hshape hsc hsched_bits hnext
      hnext_bound
  have hintermed_mod :=
    schedule_w16_sigma0_from_pipeline air start row slot hslot hwindow hrot hshape hf hsc
      hsched_bits hnext hnext_bound
  have hsigma_mod :
      ((composeLo16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))).val +
          (composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))).val *
            2 ^ 16) ≡
        (smallSigma1 (concatScheduleWord air row (slot + 2))).toNat [MOD 2 ^ 32] := by
    rw [hsigma_nat]
  set recurrenceNat :=
    ((smallSigma1 (concatScheduleWord air row (slot + 2))).toNat +
        (scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + slot) - 7) / 4))
          ((((nextRow air row - start) * 4 + slot) - 7) % 4)).toNat) +
      ((scheduleWordAtRow air (row - 3) slot).toNat +
        (smallSigma0 (concatScheduleWord air (row - 3) (slot + 1))).toNat)
  have hrecurrence_mod :
      (composeLo16 (scheduleBitsWord air (nextRow air row) slot)).val +
          (composeHi16 (scheduleBitsWord air (nextRow air row) slot)).val * 2 ^ 16 ≡
        recurrenceNat [MOD 2 ^ 32] := by
    have hsum_mod :
        (((composeLo16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))).val +
              (composeHi16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))).val *
                2 ^ 16) +
            ((scheduleW7Lo16 air row slot).val +
              (scheduleW7Hi16 air row slot).val * 2 ^ 16)) +
          ((intermed_12 air slot 0 row).val +
            (intermed_12 air slot 1 row).val * 2 ^ 16) ≡
        recurrenceNat [MOD 2 ^ 32] := by
      dsimp [recurrenceNat]
      exact (hsigma_mod.add hw7_mod).add hintermed_mod
    exact hadd.symm.trans hsum_mod
  have hnext_bits :
      isBitsWord (scheduleBitsWord air (nextRow air row) slot) := by
    exact scheduleBits_isBitsWord_from_block air start (nextRow air row) slot hsched_bits hslot
      hnext_lo hnext_bound
  have hresult_nat :
      (scheduleWordAtRow air (nextRow air row) slot).toNat =
        (composeLo16 (scheduleBitsWord air (nextRow air row) slot)).val +
          (composeHi16 (scheduleBitsWord air (nextRow air row) slot)).val * 2 ^ 16 := by
    rw [scheduleWordAtRow_eq_bitsWordToUInt32]
    exact bitsWordToUInt32_toNat_eq_compose16 _ hnext_bits
  have hrowm3_lt_last : row - 3 < Circuit.last_row air := by
    omega
  have hnext_rowm3 : nextRow air (row - 3) = row - 2 := by
    simp [nextRow, hrowm3_lt_last.ne]
    omega
  have hsigma_word :
      concatScheduleWord air row (slot + 2) =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + slot) - 2) / 4))
          ((((nextRow air row - start) * 4 + slot) - 2) % 4) := by
    interval_cases slot
    · have hrow :
          start + ((((nextRow air row - start) * 4 + 0) - 2) / 4) = row := by
        rw [hnext_succ]
        omega
      have hslot' :
          ((((nextRow air row - start) * 4 + 0) - 2) % 4) = 2 := by
        rw [hnext_succ]
        omega
      rw [hrow, hslot', scheduleWordAtRow_eq_bitsWordToUInt32]
      simp [concatScheduleWord, concatScheduleBitsWord]
    · have hrow :
          start + ((((nextRow air row - start) * 4 + 1) - 2) / 4) = row := by
        rw [hnext_succ]
        omega
      have hslot' :
          ((((nextRow air row - start) * 4 + 1) - 2) % 4) = 3 := by
        rw [hnext_succ]
        omega
      rw [hrow, hslot', scheduleWordAtRow_eq_bitsWordToUInt32]
      simp [concatScheduleWord, concatScheduleBitsWord]
    · have hrow :
          start + ((((nextRow air row - start) * 4 + 2) - 2) / 4) = nextRow air row := by
        rw [hnext_succ]
        omega
      have hslot' :
          ((((nextRow air row - start) * 4 + 2) - 2) % 4) = 0 := by
        rw [hnext_succ]
        omega
      rw [hrow, hslot', scheduleWordAtRow_eq_bitsWordToUInt32]
      simp [concatScheduleWord, concatScheduleBitsWord]
    · have hrow :
          start + ((((nextRow air row - start) * 4 + 3) - 2) / 4) = nextRow air row := by
        rw [hnext_succ]
        omega
      have hslot' :
          ((((nextRow air row - start) * 4 + 3) - 2) % 4) = 1 := by
        rw [hnext_succ]
        omega
      rw [hrow, hslot', scheduleWordAtRow_eq_bitsWordToUInt32]
      simp [concatScheduleWord, concatScheduleBitsWord]
  have hsigma0_word :
      concatScheduleWord air (row - 3) (slot + 1) =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + slot) - 15) / 4))
          ((((nextRow air row - start) * 4 + slot) - 15) % 4) := by
    interval_cases slot
    · have hrow :
          start + ((((nextRow air row - start) * 4 + 0) - 15) / 4) = row - 3 := by
        rw [hnext_succ]
        omega
      have hslot' :
          ((((nextRow air row - start) * 4 + 0) - 15) % 4) = 1 := by
        rw [hnext_succ]
        omega
      rw [hrow, hslot', scheduleWordAtRow_eq_bitsWordToUInt32]
      simp [concatScheduleWord, concatScheduleBitsWord]
    · have hrow :
          start + ((((nextRow air row - start) * 4 + 1) - 15) / 4) = row - 3 := by
        rw [hnext_succ]
        omega
      have hslot' :
          ((((nextRow air row - start) * 4 + 1) - 15) % 4) = 2 := by
        rw [hnext_succ]
        omega
      rw [hrow, hslot', scheduleWordAtRow_eq_bitsWordToUInt32]
      simp [concatScheduleWord, concatScheduleBitsWord]
    · have hrow :
          start + ((((nextRow air row - start) * 4 + 2) - 15) / 4) = row - 3 := by
        rw [hnext_succ]
        omega
      have hslot' :
          ((((nextRow air row - start) * 4 + 2) - 15) % 4) = 3 := by
        rw [hnext_succ]
        omega
      rw [hrow, hslot', scheduleWordAtRow_eq_bitsWordToUInt32]
      simp [concatScheduleWord, concatScheduleBitsWord]
    · have hrow :
          start + ((((nextRow air row - start) * 4 + 3) - 15) / 4) = row - 2 := by
        rw [hnext_succ]
        omega
      have hslot' :
          ((((nextRow air row - start) * 4 + 3) - 15) % 4) = 0 := by
        rw [hnext_succ]
        omega
      rw [hrow, hslot', scheduleWordAtRow_eq_bitsWordToUInt32]
      simp [concatScheduleWord, concatScheduleBitsWord, hnext_rowm3]
  have hw16_row :
      start + ((((nextRow air row - start) * 4 + slot) - 16) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw16_slot :
      ((((nextRow air row - start) * 4 + slot) - 16) % 4) = slot := by
    rw [hnext_succ]
    omega
  have hrhs_nat :
      (smallSigma1
            (scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + slot) - 2) / 4))
              ((((nextRow air row - start) * 4 + slot) - 2) % 4)) +
          scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + slot) - 7) / 4))
            ((((nextRow air row - start) * 4 + slot) - 7) % 4) +
          smallSigma0
            (scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + slot) - 15) / 4))
              ((((nextRow air row - start) * 4 + slot) - 15) % 4)) +
          scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + slot) - 16) / 4))
            ((((nextRow air row - start) * 4 + slot) - 16) % 4)).toNat =
        recurrenceNat % 2 ^ 32 := by
    dsimp [recurrenceNat]
    rw [hsigma_word, hsigma0_word, hw16_row, hw16_slot]
    simp [UInt32.toNat_add]
    omega
  have hrhs_mod :
      recurrenceNat ≡
        (smallSigma1
              (scheduleWordAtRow air
                (start + ((((nextRow air row - start) * 4 + slot) - 2) / 4))
                ((((nextRow air row - start) * 4 + slot) - 2) % 4)) +
            scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + slot) - 7) / 4))
              ((((nextRow air row - start) * 4 + slot) - 7) % 4) +
            smallSigma0
              (scheduleWordAtRow air
                (start + ((((nextRow air row - start) * 4 + slot) - 15) / 4))
                ((((nextRow air row - start) * 4 + slot) - 15) % 4)) +
            scheduleWordAtRow air
              (start + ((((nextRow air row - start) * 4 + slot) - 16) / 4))
              ((((nextRow air row - start) * 4 + slot) - 16) % 4)).toNat [MOD 2 ^ 32] := by
    rw [hrhs_nat]
    exact (Nat.mod_modEq recurrenceNat (2 ^ 32)).symm
  have hnat_mod :
      (scheduleWordAtRow air (nextRow air row) slot).toNat ≡
        (smallSigma1
              (scheduleWordAtRow air
                (start + ((((nextRow air row - start) * 4 + slot) - 2) / 4))
                ((((nextRow air row - start) * 4 + slot) - 2) % 4)) +
            scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + slot) - 7) / 4))
              ((((nextRow air row - start) * 4 + slot) - 7) % 4) +
            smallSigma0
              (scheduleWordAtRow air
                (start + ((((nextRow air row - start) * 4 + slot) - 15) / 4))
                ((((nextRow air row - start) * 4 + slot) - 15) % 4)) +
            scheduleWordAtRow air
              (start + ((((nextRow air row - start) * 4 + slot) - 16) / 4))
              ((((nextRow air row - start) * 4 + slot) - 16) % 4)).toNat [MOD 2 ^ 32] := by
    rw [hresult_nat]
    exact hrecurrence_mod.trans hrhs_mod
  have hnat_eq :
      (scheduleWordAtRow air (nextRow air row) slot).toNat =
        (smallSigma1
              (scheduleWordAtRow air
                (start + ((((nextRow air row - start) * 4 + slot) - 2) / 4))
                ((((nextRow air row - start) * 4 + slot) - 2) % 4)) +
            scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + slot) - 7) / 4))
              ((((nextRow air row - start) * 4 + slot) - 7) % 4) +
            smallSigma0
              (scheduleWordAtRow air
                (start + ((((nextRow air row - start) * 4 + slot) - 15) / 4))
                ((((nextRow air row - start) * 4 + slot) - 15) % 4)) +
            scheduleWordAtRow air
              (start + ((((nextRow air row - start) * 4 + slot) - 16) / 4))
              ((((nextRow air row - start) * 4 + slot) - 16) % 4)).toNat := by
    rw [Nat.ModEq] at hnat_mod
    rwa [Nat.mod_eq_of_lt (UInt32.toNat_lt _), Nat.mod_eq_of_lt (UInt32.toNat_lt _)] at hnat_mod
  exact (UInt32.toNat_inj).mp hnat_eq

/-! ## B6: Full schedule correctness over a block -/

/-- Base case: for t < 16, the schedule words are the raw input words (by definition). -/
theorem expandSchedule_base (air : C FBB ExtF) (start : ℕ) (t : ℕ)
    (ht : t < 16) :
    scheduleWordAtRow air (start + t / 4) (t % 4) =
      (expandSchedule (blockInputWords air start))[t]! := by
  have hi : t < (blockInputWords air start).size := by
    simpa [blockInputWords] using ht
  have hprefix :=
    getElem!_foldl_push_preserved
      (l := List.range 48)
      (f := fun r offset =>
        smallSigma1 r[offset + 14]! +
        r[offset + 9]! +
        smallSigma0 r[offset + 1]! +
        r[offset]!)
      (xs := blockInputWords air start) (i := t) hi
  rw [expandSchedule_eq_foldl]
  rw [hprefix]
  simpa [blockInputWords, inputWord, ht]

/-- Inductive step: for 16 ≤ t < 64, if the recurrence holds for all previous words
    and schedule_recurrence_uint32 holds at this row, then
    scheduleWordAtRow at t matches expandSchedule[t]. -/
theorem expandSchedule_step (air : C FBB ExtF) (start : ℕ) (t : ℕ)
    (ht_lo : 16 ≤ t) (ht_hi : t < 64)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (ih : ∀ s, s < t →
      scheduleWordAtRow air (start + s / 4) (s % 4) =
        (expandSchedule (blockInputWords air start))[s]!) :
    scheduleWordAtRow air (start + t / 4) (t % 4) =
      (expandSchedule (blockInputWords air start))[t]! := by
  set input := blockInputWords air start
  set step : Array Word → ℕ → Word :=
    fun acc offset =>
      smallSigma1 acc[offset + 14]! +
      acc[offset + 9]! +
      smallSigma0 acc[offset + 1]! +
      acc[offset]!
  set offset := t - 16
  set schedPrefix := (List.range offset).foldl (fun acc off => acc.push (step acc off)) input
  have hoffset : offset < 48 := by
    dsimp [offset]
    omega
  have hprefix_size : schedPrefix.size = t := by
    rw [show schedPrefix =
      (List.range offset).foldl (fun acc off => acc.push (step acc off)) input by rfl]
    rw [foldl_push_size]
    simp [input, blockInputWords, List.length_range]
    dsimp [offset]
    omega
  have hoffset_le : offset + 1 ≤ 48 := by
    omega
  have hrange :
      List.range 48 =
        List.range (offset + 1) ++ (List.range (48 - (offset + 1))).map (offset + 1 + ·) := by
    have h48 : 48 = (offset + 1) + (48 - (offset + 1)) := by
      omega
    rw [h48]
    simpa [Nat.add_sub_cancel_left] using
      (List.range_add (n := offset + 1) (m := 48 - (offset + 1)))
  have hprefix_succ :
      (List.range (offset + 1)).foldl (fun acc off => acc.push (step acc off)) input =
        schedPrefix.push (step schedPrefix offset) := by
    rw [show List.range (offset + 1) = List.range offset ++ [offset] by
      simpa using (List.range_succ (n := offset))]
    rw [List.foldl_append]
    simp [schedPrefix]
  have hexpand_t :
      (expandSchedule input)[t]! = step schedPrefix offset := by
    rw [expandSchedule_eq_foldl, hrange, List.foldl_append, hprefix_succ]
    rw [getElem!_foldl_push_preserved
      (l := (List.range (48 - (offset + 1))).map (offset + 1 + ·))
      (f := step)
      (xs := schedPrefix.push (step schedPrefix offset))
      (i := t)]
    · simpa [hprefix_size] using
        (getElem!_push_size (xs := schedPrefix) (x := step schedPrefix offset))
    · simp [hprefix_size]
  have hprefix_entry :
      ∀ s, s < t → schedPrefix[s]! = (expandSchedule input)[s]! := by
    intro s hs
    have hs_prefix : s < schedPrefix.size := by
      simpa [hprefix_size] using hs
    have hs_push : s < (schedPrefix.push (step schedPrefix offset)).size := by
      simpa [hprefix_size] using Nat.lt_succ_of_lt hs
    have hpres :
        (expandSchedule input)[s]! = (schedPrefix.push (step schedPrefix offset))[s]! := by
      rw [expandSchedule_eq_foldl, hrange, List.foldl_append, hprefix_succ]
      exact getElem!_foldl_push_preserved
        (l := (List.range (48 - (offset + 1))).map (offset + 1 + ·))
        (f := step)
        (xs := schedPrefix.push (step schedPrefix offset))
        (i := s)
        hs_push
    calc
      schedPrefix[s]! = (schedPrefix.push (step schedPrefix offset))[s]! := by
        symm
        exact getElem!_push_lt hs_prefix
      _ = (expandSchedule input)[s]! := hpres.symm
  set row := start + t / 4 - 1
  have hrow_lt_last : row < Circuit.last_row air := by
    have hsupp : start + 16 ≤ Circuit.last_row air := by
      simpa [blockWindowSupported] using hwindow
    dsimp [row]
    omega
  have hrow_next : nextRow air row = start + t / 4 := by
    have hrow_succ : row + 1 = start + t / 4 := by
      dsimp [row]
      omega
    rw [nextRow, if_neg hrow_lt_last.ne]
    exact hrow_succ
  have hnext : start + 4 ≤ nextRow air row := by
    rw [hrow_next]
    omega
  have hnext_bound : nextRow air row ≤ start + 15 := by
    rw [hrow_next]
    omega
  have hrec :=
    schedule_recurrence_uint32 air start row (t % 4) (by omega) hwindow hrot hshape hf hsc
      hsched_bits hnext hnext_bound
  dsimp only at hrec
  rw [hrow_next] at hrec
  have ht_rec : (((start + t / 4) - start) * 4 + t % 4) = t := by
    omega
  rw [ht_rec] at hrec
  rw [ih (t - 2) (by omega), ih (t - 7) (by omega), ih (t - 15) (by omega),
    ih (t - 16) (by omega)] at hrec
  have hstep_eq :
      step schedPrefix offset =
        smallSigma1 ((expandSchedule input)[t - 2]!) +
        (expandSchedule input)[t - 7]! +
        smallSigma0 ((expandSchedule input)[t - 15]!) +
        (expandSchedule input)[t - 16]! := by
    dsimp [step]
    have h2 : offset + 14 = t - 2 := by
      dsimp [offset]
      omega
    have h7 : offset + 9 = t - 7 := by
      dsimp [offset]
      omega
    have h15 : offset + 1 = t - 15 := by
      dsimp [offset]
      omega
    have h16 : offset = t - 16 := by
      dsimp [offset]
    rw [h2, h7, h15, h16,
      hprefix_entry (t - 2) (by omega),
      hprefix_entry (t - 7) (by omega),
      hprefix_entry (t - 15) (by omega),
      hprefix_entry (t - 16) (by omega)]
  simpa [input] using
    (calc
      scheduleWordAtRow air (start + t / 4) (t % 4) =
          smallSigma1 ((expandSchedule input)[t - 2]!) +
          (expandSchedule input)[t - 7]! +
          smallSigma0 ((expandSchedule input)[t - 15]!) +
          (expandSchedule input)[t - 16]! := hrec
      _ = step schedPrefix offset := hstep_eq.symm
      _ = (expandSchedule input)[t]! := hexpand_t.symm)

/-- Full schedule correctness by strong induction on t. -/
theorem expandSchedule_matches_trace (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start) :
    ∀ t, t < 64 →
      scheduleWordAtRow air (start + t / 4) (t % 4) =
        (expandSchedule (blockInputWords air start))[t]! := by
  intro t
  refine Nat.strong_induction_on t ?_
  intro t ih ht
  by_cases ht16 : t < 16
  · exact expandSchedule_base air start t ht16
  · exact expandSchedule_step air start t (by omega) ht hwindow hrot hshape hf hsc hsched_bits
      (fun s hs => ih s hs (by omega))

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
