/- 
  Layer B: Message Schedule Correctness (Block Window)

  This SHA-512 correctness slice defines the block-local transport layer.
  It packages the schedule-bit boolean transport lemmas and the 3-row
  `intermed_4 -> intermed_8 -> intermed_12` delivery fact used by
  recurrence-to-word bridges.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.MessageSchedule.BitBounds
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.MessageSchedule.CarryPipeline
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.MessageSchedule.Recurrence
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.SelectorFacts

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

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
      (List.range 64).foldl
        (fun acc offset =>
          acc.push
            (smallSigma1 acc[offset + 14]! +
             acc[offset + 9]! +
             smallSigma0 acc[offset + 1]! +
             acc[offset]!))
        input := by
  simpa [expandSchedule] using
    (List.idRun_forIn_yield_eq_foldl
      (l := List.range 64)
      (f := fun offset acc =>
        pure
          (acc.push
            (smallSigma1 acc[offset + 14]! +
             acc[offset + 9]! +
             smallSigma0 acc[offset + 1]! +
             acc[offset]!)))
      (init := input))

private theorem scheduleBits_isBitsWord_from_block
    (air : C FBB ExtF) (start row slot : ℕ)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hslot : slot < 4)
    (hrow_lo : start ≤ row)
    (hrow_hi : row ≤ start + 19) :
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
    (hrow_hi : row ≤ start + 18) :
    isBitsWord (concatScheduleBitsWord air row slot) := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
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

private theorem fieldSmallSigma0_isBitsWord (x : BitsWord) (hx : isBitsWord x) :
    isBitsWord (fieldSmallSigma0 x) := by
  have hrot1 := fieldRotr_preserves_boolean x 1 hx
  have hrot8 := fieldRotr_preserves_boolean x 8 hx
  have hshr7 := fieldShr_preserves_boolean x 7 hx
  intro i
  exact fieldXor_boolean_closed _ _
    (fieldXor_boolean_closed _ _ (hrot1 i) (hrot8 i))
    (hshr7 i)

private theorem fieldSmallSigma1_isBitsWord (x : BitsWord) (hx : isBitsWord x) :
    isBitsWord (fieldSmallSigma1 x) := by
  have hrot19 := fieldRotr_preserves_boolean x 19 hx
  have hrot61 := fieldRotr_preserves_boolean x 61 hx
  have hshr6 := fieldShr_preserves_boolean x 6 hx
  intro i
  exact fieldXor_boolean_closed _ _
    (fieldXor_boolean_closed _ _ (hrot19 i) (hrot61 i))
    (hshr6 i)

/-- On every non-initial round row of a supported SHA-512 block window, the
    four local schedule words are boolean bit-vectors. -/
theorem scheduleBits_isBitsWord_at_block_row
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hrow_lo : start + 1 ≤ row)
    (hrow_hi : row ≤ start + 19) :
    isBitsWord (scheduleBitsWord air row slot) := by
  intro bit
  have hsupp : start + 20 ≤ Circuit.last_row air := by
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
  have hoffset : row - start < 20 := by
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

/-- The SHA-512 intermed pipeline carries `intermed_4[slot][limb]` forward by
    two rows into `intermed_12[slot][limb]`. -/
theorem intermed_pipeline_delivers (air : C FBB ExtF) (start row : ℕ) (slot limb : ℕ)
    (hslot : slot < 4) (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hrow : start + 3 ≤ row) (hrow_bound : row ≤ start + 18) :
    intermed_12 air slot limb row =
      intermed_4 air slot limb (row - 2) := by
  have hrow_lt_last : row < Circuit.last_row air := by
    have hsupp : start + 20 ≤ Circuit.last_row air := by
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
    have hoffset : row - start < 20 := by
      omega
    have hshape_row := hshape.2.1 (row - start) hoffset
    have hrow_eq : start + (row - start) = row := by
      omega
    simpa [hrow_eq] using hshape_row.1
  have hsel_rowm1 :
      encoder_selector_idx air (row - 1) = (((row - 1 - start : ℕ)) : FBB) := by
    have hoffset : row - 1 - start < 20 := by
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
  have hrow_offset_hi : row - start ≤ 18 := by
    omega
  have hrowm1_offset_lo : 2 ≤ row - 1 - start := by
    omega
  have hrowm1_offset_hi : row - 1 - start ≤ 17 := by
    omega
  have h12 :=
    intermed_12_carry air (row - 1) slot limb hslot hlimb (by omega) hrot
      (hsc (row - 1)) (by simpa [hnext_rowm1] using hf row)
      ⟨row - start, hrow_offset_lo, by omega, hsel_row_next⟩
  have h8 :=
    intermed_8_carry air (row - 2) slot limb hslot hlimb (by omega) hrot
      (hsc (row - 2)) (by simpa [hnext_rowm2] using hf (row - 1))
      ⟨row - 1 - start, hrowm1_offset_lo, by omega, hsel_rowm1_next⟩
  have h12' : intermed_12 air slot limb row = intermed_8 air slot limb (row - 1) := by
    simpa [hnext_rowm1] using h12
  have h8' : intermed_8 air slot limb (row - 1) = intermed_4 air slot limb (row - 2) := by
    simpa [hnext_rowm2] using h8
  exact h12'.trans h8'

/-- On the first exposed successor-word slice, the intermed pipeline packages
    the `w[t-16] + σ₀(w[t-15])` source bundle through `intermed_12[0][limb]`. -/
theorem intermed_12_word0_from_pipeline
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    intermed_12 air 0 limb row =
      concatScheduleU16Limb air (row - 3) 0 limb +
        composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1)) ⟨limb, hlimb⟩ := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hnext_succ] using hnext
  have hrow_hi : row ≤ start + 18 := by
    simpa [hnext_succ] using hnext_bound
  have hpipe :=
    intermed_pipeline_delivers air start row 0 limb (by omega) hlimb hwindow hrot hshape hf hsc
      hrow_lo hrow_hi
  have hrowm3_lt_last : row - 3 < Circuit.last_row air := by
    omega
  have hnext_rowm3 : nextRow air (row - 3) = row - 2 := by
    simp [nextRow, hrowm3_lt_last.ne]
    omega
  have h4_raw :=
    intermed_4_correct air (row - 3) 0 limb (by omega) hlimb hrowm3_lt_last hrot (hsc (row - 3))
  have h4 :
      intermed_4 air 0 limb (row - 2) =
        concatScheduleU16Limb air (row - 3) 0 limb +
          composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1)) ⟨limb, hlimb⟩ := by
    simpa [hnext_rowm3] using h4_raw
  exact hpipe.trans h4

/-- Re-index the first exposed SHA-512 `intermed_12` source bundle onto the
    block-local `w[t-16]` / `w[t-15]` coordinates. -/
theorem intermed_12_word0_from_w16_sigma0_source
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4
    intermed_12 air 0 limb row =
      concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) limb +
        composeU16Limb
          (fieldSmallSigma0
            (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨limb, hlimb⟩ := by
  dsimp
  have hbase :=
    intermed_12_word0_from_pipeline air start row limb hlimb hwindow hrot hshape hf hsc hnext
      hnext_bound
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hw16_row :
      start + ((((nextRow air row - start) * 4) - 16) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw16_slot :
      ((((nextRow air row - start) * 4) - 16) % 4) = 0 := by
    rw [hnext_succ]
    omega
  have hw15_row :
      start + ((((nextRow air row - start) * 4) - 15) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw15_slot :
      ((((nextRow air row - start) * 4) - 15) % 4) = 1 := by
    rw [hnext_succ]
    omega
  rw [hw16_row, hw16_slot, hw15_row, hw15_slot]
  exact hbase

/-- The first exposed successor-word recurrence with both `w[t-7]` and the
    `w[t-16] + σ₀(w[t-15])` term rewritten onto block-local source
    coordinates. -/
theorem next_msg_schedule_word0_recurrence_from_sources
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4
    (if limb = 0 then 0 else scheduleCarryValue air (nextRow air row) 0 (limb - 1)) +
      composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) ⟨limb, hlimb⟩ +
      concatScheduleU16Limb air (start + (t - 7) / 4) ((t - 7) % 4) limb +
      (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) limb +
        composeU16Limb
          (fieldSmallSigma0
            (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨limb, hlimb⟩) =
    composeU16Limb (scheduleBitsWord air (nextRow air row) 0) ⟨limb, hlimb⟩ +
      scheduleCarryValue air (nextRow air row) 0 limb * (2 ^ 16 : ℕ) := by
  dsimp
  rw [← intermed_12_word0_from_w16_sigma0_source air start row limb hlimb hwindow hrot hshape hf
    hsc hnext hnext_bound]
  exact next_msg_schedule_word0_recurrence_from_w7_source air start row limb hlimb hwindow hrow
    hrot hshape hsc hnext hnext_bound

private theorem word0_sigma1_u16_limb_lt
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) ⟨limb, hlimb⟩).val <
      2 ^ 16 := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start ≤ row := by
    omega
  have hrow_hi : row ≤ start + 18 := by
    simpa [hnext_succ] using hnext_bound
  have hconcat_bits : isBitsWord (concatScheduleBitsWord air row 2) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start row 2 hwindow hsched_bits (by omega)
        hrow_lo hrow_hi
  have hsigma_bits : isBitsWord (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) := by
    exact fieldSmallSigma1_isBitsWord _ hconcat_bits
  exact composeU16Limb_val_lt _ hsigma_bits ⟨limb, hlimb⟩

private theorem word0_w7_u16_limb_lt
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (scheduleW7U16Limb air row 0 limb).val < 2 ^ 16 := by
  have hw7 :=
    schedule_w7_u16_limb_from_helper air start row limb hlimb hwindow hrot hshape hsc hnext
      hnext_bound
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hnext_succ] using hnext
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hprev_lo : start ≤ prevRow air row := by
    rw [hprev_eq]
    omega
  have hprev_hi : prevRow air row ≤ start + 18 := by
    rw [hprev_eq]
    omega
  have hbits : isBitsWord (concatScheduleBitsWord air (prevRow air row) 1) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (prevRow air row) 1 hwindow hsched_bits
        (by omega) hprev_lo hprev_hi
  rw [hw7]
  simpa [concatScheduleU16Limb, hlimb] using
    (composeU16Limb_val_lt (concatScheduleBitsWord air (prevRow air row) 1) hbits ⟨limb, hlimb⟩)

private theorem word0_intermed12_u16_limb_lt
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (intermed_12 air 0 limb row).val < 2 ^ 17 := by
  have hint :=
    intermed_12_word0_from_pipeline air start row limb hlimb hwindow hrot hshape hf hsc hnext
      hnext_bound
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hnext_succ] using hnext
  have hsrc_lo : start ≤ row - 3 := by
    omega
  have hsrc_hi : row - 3 ≤ start + 15 := by
    omega
  have hword_bits : isBitsWord (scheduleBitsWord air (row - 3) 0) := by
    exact
      scheduleBits_isBitsWord_from_block air start (row - 3) 0 hsched_bits (by omega) hsrc_lo
        (by omega)
  have hconcat_bits : isBitsWord (concatScheduleBitsWord air (row - 3) 1) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (row - 3) 1 hwindow hsched_bits
        (by omega) hsrc_lo (by omega)
  have hsigma_bits :
      isBitsWord (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1)) := by
    exact fieldSmallSigma0_isBitsWord _ hconcat_bits
  have hword_lt : (concatScheduleU16Limb air (row - 3) 0 limb).val < 2 ^ 16 := by
    simpa [concatScheduleU16Limb, concatScheduleBitsWord, hlimb] using
      (composeU16Limb_val_lt (scheduleBitsWord air (row - 3) 0) hword_bits ⟨limb, hlimb⟩)
  have hsigma_lt :
      (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1)) ⟨limb, hlimb⟩).val <
        2 ^ 16 := by
    exact composeU16Limb_val_lt _ hsigma_bits ⟨limb, hlimb⟩
  have hsum_lt :
      (concatScheduleU16Limb air (row - 3) 0 limb).val +
          (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1))
            ⟨limb, hlimb⟩).val <
        BB_prime := by
    omega
  have hval :
      (intermed_12 air 0 limb row).val =
        (concatScheduleU16Limb air (row - 3) 0 limb).val +
          (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1))
            ⟨limb, hlimb⟩).val := by
    have h := congrArg Fin.val hint
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    exact h
  rw [hval]
  omega

private theorem next_row_round_and_not_first4
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    next_is_round_row air row = 1 ∧ next_is_first_4_rows air row = 0 := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hoffset_next : nextRow air row - start < 20 := by
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
        (is_first_4_iff_selector_lt_4 air (nextRow air row) (hf (nextRow air row))).1 hfirst4 with
        ⟨n, hnlt, hnsel⟩
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
  exact ⟨hround_next, hnot_first4_next⟩

private abbrev word0CarryIn (air : C FBB ExtF) (row limb : ℕ) : FBB :=
  if limb = 0 then 0 else scheduleCarryValue air (nextRow air row) 0 (limb - 1)

private abbrev word0SigmaTerm (air : C FBB ExtF) (row limb : ℕ) (hlimb : limb < 4) : FBB :=
  composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) ⟨limb, hlimb⟩

private abbrev word0W7Term (air : C FBB ExtF) (row limb : ℕ) : FBB :=
  scheduleW7U16Limb air row 0 limb

private abbrev word0IntermedTerm (air : C FBB ExtF) (row limb : ℕ) : FBB :=
  intermed_12 air 0 limb row

private abbrev word0OutputTerm (air : C FBB ExtF) (row limb : ℕ) (hlimb : limb < 4) : FBB :=
  composeU16Limb (scheduleBitsWord air (nextRow air row) 0) ⟨limb, hlimb⟩

private abbrev word0CarryOut (air : C FBB ExtF) (row limb : ℕ) : FBB :=
  scheduleCarryValue air (nextRow air row) 0 limb

private abbrev word0SigmaPack (air : C FBB ExtF) (row : ℕ) : ℕ :=
  (word0SigmaTerm air row 0 (by decide)).val +
    (word0SigmaTerm air row 1 (by decide)).val * 2 ^ 16 +
    (word0SigmaTerm air row 2 (by decide)).val * 2 ^ 32 +
    (word0SigmaTerm air row 3 (by decide)).val * 2 ^ 48

private abbrev word0W7Pack (air : C FBB ExtF) (row : ℕ) : ℕ :=
  (word0W7Term air row 0).val +
    (word0W7Term air row 1).val * 2 ^ 16 +
    (word0W7Term air row 2).val * 2 ^ 32 +
    (word0W7Term air row 3).val * 2 ^ 48

private abbrev word0IntermedPack (air : C FBB ExtF) (row : ℕ) : ℕ :=
  (word0IntermedTerm air row 0).val +
    (word0IntermedTerm air row 1).val * 2 ^ 16 +
    (word0IntermedTerm air row 2).val * 2 ^ 32 +
    (word0IntermedTerm air row 3).val * 2 ^ 48

private abbrev word0OutputPack (air : C FBB ExtF) (row : ℕ) : ℕ :=
  (word0OutputTerm air row 0 (by decide)).val +
    (word0OutputTerm air row 1 (by decide)).val * 2 ^ 16 +
    (word0OutputTerm air row 2 (by decide)).val * 2 ^ 32 +
    (word0OutputTerm air row 3 (by decide)).val * 2 ^ 48

private abbrev word0W7SourcePack (air : C FBB ExtF) (start row : ℕ) : ℕ :=
  let t := (nextRow air row - start) * 4
  (concatScheduleU16Limb air (start + (t - 7) / 4) ((t - 7) % 4) 0).val +
    (concatScheduleU16Limb air (start + (t - 7) / 4) ((t - 7) % 4) 1).val * 2 ^ 16 +
    (concatScheduleU16Limb air (start + (t - 7) / 4) ((t - 7) % 4) 2).val * 2 ^ 32 +
    (concatScheduleU16Limb air (start + (t - 7) / 4) ((t - 7) % 4) 3).val * 2 ^ 48

private abbrev word0W16SourcePack (air : C FBB ExtF) (start row : ℕ) : ℕ :=
  let t := (nextRow air row - start) * 4
  (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 0).val +
    (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 1).val * 2 ^ 16 +
    (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 2).val * 2 ^ 32 +
    (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 3).val * 2 ^ 48

private abbrev word0Sigma0SourcePack (air : C FBB ExtF) (start row : ℕ) : ℕ :=
  let t := (nextRow air row - start) * 4
  (composeU16Limb
      (fieldSmallSigma0
        (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨0, by decide⟩).val +
    (composeU16Limb
        (fieldSmallSigma0
          (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨1, by decide⟩).val *
      2 ^ 16 +
    (composeU16Limb
        (fieldSmallSigma0
          (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨2, by decide⟩).val *
      2 ^ 32 +
    (composeU16Limb
        (fieldSmallSigma0
          (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨3, by decide⟩).val *
      2 ^ 48

private theorem word0_carry_out_lt_four
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (word0CarryOut air row limb).val < 4 := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  rcases
      next_row_round_and_not_first4 air start row hwindow hrot hshape hf hnext hnext_bound with
    ⟨hround_next, hnot_first4_next⟩
  simpa [word0CarryOut] using
    next_msg_schedule_carry_value_lt_four air row limb hlimb hrow_lt_last.le hrot (hsc row)
      hround_next hnot_first4_next

private theorem word0_output_u16_limb_lt
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (word0OutputTerm air row limb hlimb).val < 2 ^ 16 := by
  have hbits : isBitsWord (scheduleBitsWord air (nextRow air row) 0) := by
    exact
      scheduleBits_isBitsWord_at_block_row air start (nextRow air row) 0 (by omega) hwindow
        hrot hshape hsc (by omega) hnext_bound
  simpa [word0OutputTerm] using
    (composeU16Limb_val_lt (scheduleBitsWord air (nextRow air row) 0) hbits ⟨limb, hlimb⟩)

private theorem word0_recurrence_u16_limb_nat
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (word0CarryIn air row limb).val +
      (word0SigmaTerm air row limb hlimb).val +
      (word0W7Term air row limb).val +
      (word0IntermedTerm air row limb).val =
    (word0OutputTerm air row limb hlimb).val +
      (word0CarryOut air row limb).val * 2 ^ 16 := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hfield :
      word0CarryIn air row limb +
          word0SigmaTerm air row limb hlimb +
          word0W7Term air row limb +
          word0IntermedTerm air row limb =
        word0OutputTerm air row limb hlimb +
          word0CarryOut air row limb * (2 ^ 16 : ℕ) := by
    simpa [word0CarryIn, word0SigmaTerm, word0W7Term, word0IntermedTerm, word0OutputTerm,
      word0CarryOut] using
      next_msg_schedule_word0_recurrence_with_w7 air row limb hlimb hrow_lt_last.le hrot
        (hsc row)
  have hsigma_lt :
      (word0SigmaTerm air row limb hlimb).val < 2 ^ 16 := by
    simpa [word0SigmaTerm] using
      word0_sigma1_u16_limb_lt air start row limb hlimb hwindow hsched_bits hnext hnext_bound
  have hw7_lt :
      (word0W7Term air row limb).val < 2 ^ 16 := by
    simpa [word0W7Term] using
      word0_w7_u16_limb_lt air start row limb hlimb hwindow hrot hshape hsc hsched_bits hnext
        hnext_bound
  have hintermed_lt :
      (word0IntermedTerm air row limb).val < 2 ^ 17 := by
    simpa [word0IntermedTerm] using
      word0_intermed12_u16_limb_lt air start row limb hlimb hwindow hrot hshape hf hsc
        hsched_bits hnext hnext_bound
  have hcarry_out_lt : (word0CarryOut air row limb).val < 4 := by
    exact
      word0_carry_out_lt_four air start row limb hlimb hwindow hrot hshape hf hsc hnext
        hnext_bound
  have houtput_lt :
      (word0OutputTerm air row limb hlimb).val < 2 ^ 16 := by
    exact word0_output_u16_limb_lt air start row limb hlimb hwindow hrot hshape hsc hnext
      hnext_bound
  have hcarry_in_lt :
      (word0CarryIn air row limb).val < 4 := by
    by_cases hzero : limb = 0
    · simp [word0CarryIn, hzero]
    · have hprev : limb - 1 < 4 := by
        omega
      simpa [word0CarryIn, hzero] using
        word0_carry_out_lt_four air start row (limb - 1) hprev hwindow hrot hshape hf hsc
          hnext hnext_bound
  have h := congrArg Fin.val hfield
  have hab :
      (word0CarryIn air row limb + word0SigmaTerm air row limb hlimb).val =
        (word0CarryIn air row limb).val + (word0SigmaTerm air row limb hlimb).val := by
    rw [babybear_add_no_wrap _ _ (by omega)]
  have habc :
      (word0CarryIn air row limb + word0SigmaTerm air row limb hlimb +
          word0W7Term air row limb).val =
        (word0CarryIn air row limb).val + (word0SigmaTerm air row limb hlimb).val +
          (word0W7Term air row limb).val := by
    have hmid :
        (word0CarryIn air row limb + word0SigmaTerm air row limb hlimb).val +
            (word0W7Term air row limb).val <
          BB_prime := by
      rw [hab]
      omega
    rw [babybear_add_no_wrap _ _ hmid, hab]
  have habcd :
      (word0CarryIn air row limb + word0SigmaTerm air row limb hlimb +
          word0W7Term air row limb + word0IntermedTerm air row limb).val =
        (word0CarryIn air row limb).val + (word0SigmaTerm air row limb hlimb).val +
          (word0W7Term air row limb).val + (word0IntermedTerm air row limb).val := by
    have hmid :
        (word0CarryIn air row limb + word0SigmaTerm air row limb hlimb +
            word0W7Term air row limb).val +
            (word0IntermedTerm air row limb).val <
          BB_prime := by
      rw [habc]
      omega
    rw [babybear_add_no_wrap _ _ hmid, habc]
  have hcarry_mul :
      (word0CarryOut air row limb * (2 ^ 16 : ℕ)).val =
        (word0CarryOut air row limb).val * 2 ^ 16 := by
    exact small_carry_mul_65536_val (word0CarryOut air row limb) hcarry_out_lt
  have hsum_r :
      (word0OutputTerm air row limb hlimb + word0CarryOut air row limb * (2 ^ 16 : ℕ)).val =
        (word0OutputTerm air row limb hlimb).val +
          (word0CarryOut air row limb * (2 ^ 16 : ℕ)).val := by
    rw [babybear_add_no_wrap _ _ (by rw [hcarry_mul]; omega)]
  rw [habcd, hsum_r, hcarry_mul] at h
  exact h

private theorem word0_recurrence_packed_nat
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    word0SigmaPack air row + word0W7Pack air row + word0IntermedPack air row =
      word0OutputPack air row + (word0CarryOut air row 3).val * 2 ^ 64 := by
  have h0 :
      (word0SigmaTerm air row 0 (by decide)).val +
          (word0W7Term air row 0).val +
          (word0IntermedTerm air row 0).val =
        (word0OutputTerm air row 0 (by decide)).val +
          (word0CarryOut air row 0).val * 2 ^ 16 := by
    simpa [word0CarryIn] using
      word0_recurrence_u16_limb_nat air start row 0 (by decide) hwindow hrot hshape hf hsc
        hsched_bits hnext hnext_bound
  have h1_base :
      (word0CarryOut air row 0).val +
          (word0SigmaTerm air row 1 (by decide)).val +
          (word0W7Term air row 1).val +
          (word0IntermedTerm air row 1).val =
        (word0OutputTerm air row 1 (by decide)).val +
          (word0CarryOut air row 1).val * 2 ^ 16 := by
    simpa [word0CarryIn] using
      word0_recurrence_u16_limb_nat air start row 1 (by decide) hwindow hrot hshape hf hsc
        hsched_bits hnext hnext_bound
  have h2_base :
      (word0CarryOut air row 1).val +
          (word0SigmaTerm air row 2 (by decide)).val +
          (word0W7Term air row 2).val +
          (word0IntermedTerm air row 2).val =
        (word0OutputTerm air row 2 (by decide)).val +
          (word0CarryOut air row 2).val * 2 ^ 16 := by
    simpa [word0CarryIn] using
      word0_recurrence_u16_limb_nat air start row 2 (by decide) hwindow hrot hshape hf hsc
        hsched_bits hnext hnext_bound
  have h3_base :
      (word0CarryOut air row 2).val +
          (word0SigmaTerm air row 3 (by decide)).val +
          (word0W7Term air row 3).val +
          (word0IntermedTerm air row 3).val =
        (word0OutputTerm air row 3 (by decide)).val +
          (word0CarryOut air row 3).val * 2 ^ 16 := by
    simpa [word0CarryIn] using
      word0_recurrence_u16_limb_nat air start row 3 (by decide) hwindow hrot hshape hf hsc
        hsched_bits hnext hnext_bound
  have h1 := congrArg (fun n : ℕ => n * 2 ^ 16) h1_base
  have h2 := congrArg (fun n : ℕ => n * 2 ^ 32) h2_base
  have h3 := congrArg (fun n : ℕ => n * 2 ^ 48) h3_base
  dsimp [word0SigmaPack, word0W7Pack, word0IntermedPack, word0OutputPack]
  norm_num at h1 h2 h3 ⊢
  omega

private theorem word0_w16_source_u16_limb_lt
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4
    (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) limb).val < 2 ^ 16 := by
  dsimp
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hsrc_lo : start ≤ row - 3 := by
    omega
  have hword_bits : isBitsWord (scheduleBitsWord air (row - 3) 0) := by
    exact
      scheduleBits_isBitsWord_from_block air start (row - 3) 0 hsched_bits (by omega) hsrc_lo
        (by omega)
  have hw16_row :
      start + ((((nextRow air row - start) * 4) - 16) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw16_slot :
      ((((nextRow air row - start) * 4) - 16) % 4) = 0 := by
    rw [hnext_succ]
    omega
  rw [hw16_row, hw16_slot]
  simpa [concatScheduleU16Limb, concatScheduleBitsWord, hlimb] using
    (composeU16Limb_val_lt (scheduleBitsWord air (row - 3) 0) hword_bits ⟨limb, hlimb⟩)

private theorem word0_sigma0_source_u16_limb_lt
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4
    (composeU16Limb
        (fieldSmallSigma0
          (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨limb, hlimb⟩).val <
      2 ^ 16 := by
  dsimp
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hsrc_lo : start ≤ row - 3 := by
    omega
  have hconcat_bits : isBitsWord (concatScheduleBitsWord air (row - 3) 1) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (row - 3) 1 hwindow hsched_bits
        (by omega) hsrc_lo (by omega)
  have hsigma_bits :
      isBitsWord (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1)) := by
    exact fieldSmallSigma0_isBitsWord _ hconcat_bits
  have hw15_row :
      start + ((((nextRow air row - start) * 4) - 15) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw15_slot :
      ((((nextRow air row - start) * 4) - 15) % 4) = 1 := by
    rw [hnext_succ]
    omega
  rw [hw15_row, hw15_slot]
  exact composeU16Limb_val_lt _ hsigma_bits ⟨limb, hlimb⟩

private theorem word0_w7_packed_from_source_nat
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    word0W7Pack air row = word0W7SourcePack air start row := by
  have h0 := congrArg Fin.val
    (schedule_w7_u16_limb_from_source air start row 0 (by decide) hwindow hrot hshape hsc hnext
      hnext_bound)
  have h1 := congrArg Fin.val
    (schedule_w7_u16_limb_from_source air start row 1 (by decide) hwindow hrot hshape hsc hnext
      hnext_bound)
  have h2 := congrArg Fin.val
    (schedule_w7_u16_limb_from_source air start row 2 (by decide) hwindow hrot hshape hsc hnext
      hnext_bound)
  have h3 := congrArg Fin.val
    (schedule_w7_u16_limb_from_source air start row 3 (by decide) hwindow hrot hshape hsc hnext
      hnext_bound)
  dsimp [word0W7Pack, word0W7SourcePack]
  rw [h0, h1, h2, h3]

private theorem word0_intermed_packed_from_sources_nat
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    word0IntermedPack air row =
      word0W16SourcePack air start row + word0Sigma0SourcePack air start row := by
  have h0_field :=
    intermed_12_word0_from_w16_sigma0_source air start row 0 (by decide) hwindow hrot hshape hf hsc
      hnext hnext_bound
  have h1_field :=
    intermed_12_word0_from_w16_sigma0_source air start row 1 (by decide) hwindow hrot hshape hf hsc
      hnext hnext_bound
  have h2_field :=
    intermed_12_word0_from_w16_sigma0_source air start row 2 (by decide) hwindow hrot hshape hf hsc
      hnext hnext_bound
  have h3_field :=
    intermed_12_word0_from_w16_sigma0_source air start row 3 (by decide) hwindow hrot hshape hf hsc
      hnext hnext_bound
  have h0 :
      (word0IntermedTerm air row 0).val =
        (let t := (nextRow air row - start) * 4
         (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 0).val +
           (composeU16Limb
               (fieldSmallSigma0
                 (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨0, by decide⟩).val) := by
    have hw16_lt :=
      word0_w16_source_u16_limb_lt air start row 0 (by decide) hwindow hsched_bits hnext
        hnext_bound
    have hsigma_lt :=
      word0_sigma0_source_u16_limb_lt air start row 0 (by decide) hwindow hsched_bits hnext
        hnext_bound
    have hsum_lt :
        (let t := (nextRow air row - start) * 4
         (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 0).val +
           (composeU16Limb
               (fieldSmallSigma0
                 (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨0, by decide⟩).val) <
          BB_prime := by
      dsimp at hw16_lt hsigma_lt ⊢
      omega
    have h := congrArg Fin.val h0_field
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    simpa [word0IntermedTerm] using h
  have h1 :
      (word0IntermedTerm air row 1).val =
        (let t := (nextRow air row - start) * 4
         (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 1).val +
           (composeU16Limb
               (fieldSmallSigma0
                 (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨1, by decide⟩).val) := by
    have hw16_lt :=
      word0_w16_source_u16_limb_lt air start row 1 (by decide) hwindow hsched_bits hnext
        hnext_bound
    have hsigma_lt :=
      word0_sigma0_source_u16_limb_lt air start row 1 (by decide) hwindow hsched_bits hnext
        hnext_bound
    have hsum_lt :
        (let t := (nextRow air row - start) * 4
         (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 1).val +
           (composeU16Limb
               (fieldSmallSigma0
                 (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨1, by decide⟩).val) <
          BB_prime := by
      dsimp at hw16_lt hsigma_lt ⊢
      omega
    have h := congrArg Fin.val h1_field
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    simpa [word0IntermedTerm] using h
  have h2 :
      (word0IntermedTerm air row 2).val =
        (let t := (nextRow air row - start) * 4
         (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 2).val +
           (composeU16Limb
               (fieldSmallSigma0
                 (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨2, by decide⟩).val) := by
    have hw16_lt :=
      word0_w16_source_u16_limb_lt air start row 2 (by decide) hwindow hsched_bits hnext
        hnext_bound
    have hsigma_lt :=
      word0_sigma0_source_u16_limb_lt air start row 2 (by decide) hwindow hsched_bits hnext
        hnext_bound
    have hsum_lt :
        (let t := (nextRow air row - start) * 4
         (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 2).val +
           (composeU16Limb
               (fieldSmallSigma0
                 (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨2, by decide⟩).val) <
          BB_prime := by
      dsimp at hw16_lt hsigma_lt ⊢
      omega
    have h := congrArg Fin.val h2_field
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    simpa [word0IntermedTerm] using h
  have h3 :
      (word0IntermedTerm air row 3).val =
        (let t := (nextRow air row - start) * 4
         (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 3).val +
           (composeU16Limb
               (fieldSmallSigma0
                 (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨3, by decide⟩).val) := by
    have hw16_lt :=
      word0_w16_source_u16_limb_lt air start row 3 (by decide) hwindow hsched_bits hnext
        hnext_bound
    have hsigma_lt :=
      word0_sigma0_source_u16_limb_lt air start row 3 (by decide) hwindow hsched_bits hnext
        hnext_bound
    have hsum_lt :
        (let t := (nextRow air row - start) * 4
         (concatScheduleU16Limb air (start + (t - 16) / 4) ((t - 16) % 4) 3).val +
           (composeU16Limb
               (fieldSmallSigma0
                 (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4))) ⟨3, by decide⟩).val) <
          BB_prime := by
      dsimp at hw16_lt hsigma_lt ⊢
      omega
    have h := congrArg Fin.val h3_field
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    simpa [word0IntermedTerm] using h
  dsimp at h0 h1 h2 h3
  have h1w := congrArg (fun n : ℕ => n * 2 ^ 16) h1
  have h2w := congrArg (fun n : ℕ => n * 2 ^ 32) h2
  have h3w := congrArg (fun n : ℕ => n * 2 ^ 48) h3
  dsimp [word0IntermedPack, word0W16SourcePack, word0Sigma0SourcePack]
  norm_num at h1w h2w h3w ⊢
  rw [h0, h1w, h2w, h3w]
  ring_nf

private theorem word0_recurrence_packed_from_sources_nat
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    word0SigmaPack air row + word0W7SourcePack air start row +
        (word0W16SourcePack air start row + word0Sigma0SourcePack air start row) =
      word0OutputPack air row + (word0CarryOut air row 3).val * 2 ^ 64 := by
  rw [← word0_w7_packed_from_source_nat air start row hwindow hrot hshape hsc hnext hnext_bound,
    ← word0_intermed_packed_from_sources_nat air start row hwindow hrot hshape hf hsc hsched_bits
      hnext hnext_bound]
  simpa [Nat.add_assoc] using
    word0_recurrence_packed_nat air start row hwindow hrot hshape hf hsc hsched_bits hnext
      hnext_bound

/-- The first exposed SHA-512 successor word reconstructs as a `UInt64` from the
    already source-indexed packed nat recurrence. -/
theorem next_msg_schedule_word0_recurrence_uint64_from_sources
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4
    scheduleWordAtRow air (nextRow air row) 0 =
      bitsWordToUInt64 (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) +
        concatScheduleWord air (start + (t - 7) / 4) ((t - 7) % 4) +
        (concatScheduleWord air (start + (t - 16) / 4) ((t - 16) % 4) +
          bitsWordToUInt64
            (fieldSmallSigma0
              (concatScheduleBitsWord air (start + (t - 15) / 4) ((t - 15) % 4)))) := by
  dsimp
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hnext_succ] using hnext
  have hrow_hi : row ≤ start + 18 := by
    simpa [hnext_succ] using hnext_bound
  have hnext_lo : start ≤ nextRow air row := by
    omega
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hw7_row :
      start + ((((nextRow air row - start) * 4) - 7) / 4) = prevRow air row := by
    rw [hprev_eq, hnext_succ]
    omega
  have hw7_slot :
      ((((nextRow air row - start) * 4) - 7) % 4) = 1 := by
    rw [hnext_succ]
    omega
  have hw16_row :
      start + ((((nextRow air row - start) * 4) - 16) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw16_slot :
      ((((nextRow air row - start) * 4) - 16) % 4) = 0 := by
    rw [hnext_succ]
    omega
  have hw15_row :
      start + ((((nextRow air row - start) * 4) - 15) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw15_slot :
      ((((nextRow air row - start) * 4) - 15) % 4) = 1 := by
    rw [hnext_succ]
    omega
  rw [hw7_row, hw7_slot, hw16_row, hw16_slot, hw15_row, hw15_slot]
  have hsigma_bits :
      isBitsWord (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) := by
    exact fieldSmallSigma1_isBitsWord _ <|
      concatScheduleBits_isBitsWord_from_block air start row 2 hwindow hsched_bits (by omega)
        (by omega) hrow_hi
  have hw7_bits : isBitsWord (concatScheduleBitsWord air (prevRow air row) 1) := by
    rw [hprev_eq]
    exact
      concatScheduleBits_isBitsWord_from_block air start (row - 1) 1 hwindow hsched_bits
        (by omega) (by omega) (by omega)
  have hw16_bits : isBitsWord (concatScheduleBitsWord air (row - 3) 0) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (row - 3) 0 hwindow hsched_bits
        (by omega) (by omega) (by omega)
  have hsigma0_bits :
      isBitsWord (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1)) := by
    exact fieldSmallSigma0_isBitsWord _ <|
      concatScheduleBits_isBitsWord_from_block air start (row - 3) 1 hwindow hsched_bits
        (by omega) (by omega) (by omega)
  have houtput_bits : isBitsWord (scheduleBitsWord air (nextRow air row) 0) := by
    exact
      scheduleBits_isBitsWord_from_block air start (nextRow air row) 0 hsched_bits (by omega)
        hnext_lo hnext_bound
  have hsigma_word :
      bitsWordToUInt64 (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) =
        (word0SigmaPack air row).toUInt64 := by
    simpa [word0SigmaPack, word0SigmaTerm] using
      bitsWordToUInt64_eq_compose16 (fieldSmallSigma1 (concatScheduleBitsWord air row 2))
        hsigma_bits
  have hw7_word :
      concatScheduleWord air (prevRow air row) 1 =
        (word0W7SourcePack air start row).toUInt64 := by
    rw [concatScheduleWord]
    dsimp [word0W7SourcePack]
    rw [hw7_row, hw7_slot]
    simpa [concatScheduleU16Limb] using
      bitsWordToUInt64_eq_compose16 (concatScheduleBitsWord air (prevRow air row) 1) hw7_bits
  have hw16_word :
      concatScheduleWord air (row - 3) 0 =
        (word0W16SourcePack air start row).toUInt64 := by
    rw [concatScheduleWord]
    dsimp [word0W16SourcePack]
    rw [hw16_row, hw16_slot]
    simpa [concatScheduleU16Limb] using
      bitsWordToUInt64_eq_compose16 (concatScheduleBitsWord air (row - 3) 0) hw16_bits
  have hsigma0_word :
      bitsWordToUInt64 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1)) =
        (word0Sigma0SourcePack air start row).toUInt64 := by
    dsimp [word0Sigma0SourcePack]
    rw [hw15_row, hw15_slot]
    simpa using
      bitsWordToUInt64_eq_compose16 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1))
        hsigma0_bits
  have houtput_word :
      scheduleWordAtRow air (nextRow air row) 0 =
        (word0OutputPack air row).toUInt64 := by
    rw [scheduleWordAtRow_eq_bitsWordToUInt64]
    simpa [word0OutputPack, word0OutputTerm] using
      bitsWordToUInt64_eq_compose16 (scheduleBitsWord air (nextRow air row) 0) houtput_bits
  have hsigma_nat :
      (bitsWordToUInt64 (fieldSmallSigma1 (concatScheduleBitsWord air row 2))).toNat =
        word0SigmaPack air row % 2 ^ 64 := by
    simpa [UInt64.toNat_ofNat] using congrArg UInt64.toNat hsigma_word
  have hw7_nat :
      (concatScheduleWord air (prevRow air row) 1).toNat =
        word0W7SourcePack air start row % 2 ^ 64 := by
    simpa [UInt64.toNat_ofNat] using congrArg UInt64.toNat hw7_word
  have hw16_nat :
      (concatScheduleWord air (row - 3) 0).toNat =
        word0W16SourcePack air start row % 2 ^ 64 := by
    simpa [UInt64.toNat_ofNat] using congrArg UInt64.toNat hw16_word
  have hsigma0_nat :
      (bitsWordToUInt64 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1))).toNat =
        word0Sigma0SourcePack air start row % 2 ^ 64 := by
    simpa [UInt64.toNat_ofNat] using congrArg UInt64.toNat hsigma0_word
  have houtput_nat :
      (scheduleWordAtRow air (nextRow air row) 0).toNat =
        word0OutputPack air row % 2 ^ 64 := by
    simpa [UInt64.toNat_ofNat] using congrArg UInt64.toNat houtput_word
  have hsum_nat :
      (bitsWordToUInt64 (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) +
          concatScheduleWord air (prevRow air row) 1 +
          (concatScheduleWord air (row - 3) 0 +
            bitsWordToUInt64 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1)))).toNat =
        (word0SigmaPack air row + word0W7SourcePack air start row +
            (word0W16SourcePack air start row + word0Sigma0SourcePack air start row)) % 2 ^ 64 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, hsigma_nat, hw7_nat, hw16_nat,
      hsigma0_nat]
    omega
  have hpacked_mod :
      (word0SigmaPack air row + word0W7SourcePack air start row +
          (word0W16SourcePack air start row + word0Sigma0SourcePack air start row)) % 2 ^ 64 =
        word0OutputPack air row % 2 ^ 64 := by
    rw [word0_recurrence_packed_from_sources_nat air start row hwindow hrot hshape hf hsc
      hsched_bits hnext hnext_bound]
    omega
  apply UInt64_eq_of_toNat_eq
  rw [houtput_nat, hsum_nat, hpacked_mod]

private theorem word0_sigma1_term_eq_smallSigma1_word
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    bitsWordToUInt64 (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) =
      smallSigma1 (concatScheduleWord air row 2) := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hbits :
      isBitsWord (concatScheduleBitsWord air row 2) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start row 2 hwindow hsched_bits
        (by omega) (by omega) (by simpa [hnext_succ] using hnext_bound)
  simpa [concatScheduleWord] using
    fieldSmallSigma1_eq_smallSigma1 (concatScheduleBitsWord air row 2) hbits

private theorem word0_sigma0_source_eq_smallSigma0_word
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    bitsWordToUInt64 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) 1)) =
      smallSigma0 (concatScheduleWord air (row - 3) 1) := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hbits :
      isBitsWord (concatScheduleBitsWord air (row - 3) 1) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (row - 3) 1 hwindow hsched_bits
        (by omega) (by omega) (by omega)
  simpa [concatScheduleWord] using
    fieldSmallSigma0_eq_smallSigma0 (concatScheduleBitsWord air (row - 3) 1) hbits

/-- The first exposed SHA-512 successor-word recurrence can now be stated
    entirely over trace words, with the leading `σ₁(w[t-2])` term and the
    remaining `σ₀(w[t-15])` source term rewritten out of the field-bit layer. -/
theorem next_msg_schedule_word0_recurrence_trace_words
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    scheduleWordAtRow air (nextRow air row) 0 =
      smallSigma1 (concatScheduleWord air row 2) +
        concatScheduleWord air (prevRow air row) 1 +
        (concatScheduleWord air (row - 3) 0 +
          smallSigma0 (concatScheduleWord air (row - 3) 1)) := by
  have hbase :=
    next_msg_schedule_word0_recurrence_uint64_from_sources air start row hwindow hrot hshape hf
      hsc hsched_bits hnext hnext_bound
  dsimp at hbase
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hw7_row :
      start + ((((nextRow air row - start) * 4) - 7) / 4) = prevRow air row := by
    rw [hprev_eq, hnext_succ]
    omega
  have hw7_slot :
      ((((nextRow air row - start) * 4) - 7) % 4) = 1 := by
    rw [hnext_succ]
    omega
  have hw16_row :
      start + ((((nextRow air row - start) * 4) - 16) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw16_slot :
      ((((nextRow air row - start) * 4) - 16) % 4) = 0 := by
    rw [hnext_succ]
    omega
  have hw15_row :
      start + ((((nextRow air row - start) * 4) - 15) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw15_slot :
      ((((nextRow air row - start) * 4) - 15) % 4) = 1 := by
    rw [hnext_succ]
    omega
  rw [hw7_row, hw7_slot, hw16_row, hw16_slot, hw15_row, hw15_slot] at hbase
  rw [word0_sigma1_term_eq_smallSigma1_word air start row hwindow hsched_bits hnext hnext_bound,
    word0_sigma0_source_eq_smallSigma0_word air start row hwindow hsched_bits hnext hnext_bound] at hbase
  exact hbase

/-- The first exposed SHA-512 successor-word recurrence packaged back into the
    block-local `t`-indexed source coordinates used by schedule-step
    assembly. -/
theorem next_msg_schedule_word0_recurrence
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4
    scheduleWordAtRow air (nextRow air row) 0 =
      smallSigma1 (scheduleWordAtRow air (start + (t - 2) / 4) ((t - 2) % 4)) +
        scheduleWordAtRow air (start + (t - 7) / 4) ((t - 7) % 4) +
        (scheduleWordAtRow air (start + (t - 16) / 4) ((t - 16) % 4) +
          smallSigma0 (scheduleWordAtRow air (start + (t - 15) / 4) ((t - 15) % 4))) := by
  dsimp
  have hbase :=
    next_msg_schedule_word0_recurrence_trace_words air start row hwindow hrot hshape hf hsc
      hsched_bits hnext hnext_bound
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hsigma_row :
      start + ((((nextRow air row - start) * 4) - 2) / 4) = row := by
    rw [hnext_succ]
    omega
  have hsigma_slot :
      ((((nextRow air row - start) * 4) - 2) % 4) = 2 := by
    rw [hnext_succ]
    omega
  have hw7_row :
      start + ((((nextRow air row - start) * 4) - 7) / 4) = prevRow air row := by
    rw [hprev_eq, hnext_succ]
    omega
  have hw7_slot :
      ((((nextRow air row - start) * 4) - 7) % 4) = 1 := by
    rw [hnext_succ]
    omega
  have hw16_row :
      start + ((((nextRow air row - start) * 4) - 16) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw16_slot :
      ((((nextRow air row - start) * 4) - 16) % 4) = 0 := by
    rw [hnext_succ]
    omega
  have hw15_row :
      start + ((((nextRow air row - start) * 4) - 15) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw15_slot :
      ((((nextRow air row - start) * 4) - 15) % 4) = 1 := by
    rw [hnext_succ]
    omega
  have hsigma_word :
      concatScheduleWord air row 2 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4) - 2) / 4))
          ((((nextRow air row - start) * 4) - 2) % 4) := by
    rw [hsigma_row, hsigma_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  have hw7_word :
      concatScheduleWord air (prevRow air row) 1 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4) - 7) / 4))
          ((((nextRow air row - start) * 4) - 7) % 4) := by
    rw [hw7_row, hw7_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  have hw16_word :
      concatScheduleWord air (row - 3) 0 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4) - 16) / 4))
          ((((nextRow air row - start) * 4) - 16) % 4) := by
    rw [hw16_row, hw16_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  have hsigma0_word :
      concatScheduleWord air (row - 3) 1 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4) - 15) / 4))
          ((((nextRow air row - start) * 4) - 15) % 4) := by
    rw [hw15_row, hw15_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  rw [hsigma_word, hw7_word, hw16_word, hsigma0_word] at hbase
  exact hbase

/-! ## B5b: Slot-parametric recurrence bridge -/

/-- On any exposed successor-word slice, the intermed pipeline packages the
    `w[t-16] + σ₀(w[t-15])` source bundle through `intermed_12[slot][limb]`. -/
theorem intermed_12_from_pipeline_at
    (air : C FBB ExtF) (start row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    intermed_12 air slot limb row =
      concatScheduleU16Limb air (row - 3) slot limb +
        composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
          ⟨limb, hlimb⟩ := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hnext_succ] using hnext
  have hrow_hi : row ≤ start + 18 := by
    simpa [hnext_succ] using hnext_bound
  have hpipe :=
    intermed_pipeline_delivers air start row slot limb hslot hlimb hwindow hrot hshape hf hsc
      hrow_lo hrow_hi
  have hrowm3_lt_last : row - 3 < Circuit.last_row air := by
    omega
  have hnext_rowm3 : nextRow air (row - 3) = row - 2 := by
    simp [nextRow, hrowm3_lt_last.ne]
    omega
  have h4_raw :=
    intermed_4_correct air (row - 3) slot limb hslot hlimb hrowm3_lt_last hrot (hsc (row - 3))
  have h4 :
      intermed_4 air slot limb (row - 2) =
        concatScheduleU16Limb air (row - 3) slot limb +
          composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
            ⟨limb, hlimb⟩ := by
    simpa [hnext_rowm3] using h4_raw
  exact hpipe.trans h4

private theorem schedule_sigma1_u16_limb_lt_at
    (air : C FBB ExtF) (start row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) ⟨limb, hlimb⟩).val <
      2 ^ 16 := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start ≤ row := by
    omega
  have hrow_hi : row ≤ start + 18 := by
    simpa [hnext_succ] using hnext_bound
  have hconcat_bits : isBitsWord (concatScheduleBitsWord air row (slot + 2)) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start row (slot + 2) hwindow hsched_bits
        (by omega) hrow_lo hrow_hi
  have hsigma_bits : isBitsWord (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) := by
    exact fieldSmallSigma1_isBitsWord _ hconcat_bits
  exact composeU16Limb_val_lt _ hsigma_bits ⟨limb, hlimb⟩

private theorem schedule_w7_u16_limb_lt_at
    (air : C FBB ExtF) (start row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (scheduleW7U16Limb air row slot limb).val < 2 ^ 16 := by
  have hw7 :=
    schedule_w7_u16_limb_from_concat_prev_at air start row slot limb hslot hlimb hwindow hrot
      hshape hsc hnext hnext_bound
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hnext_succ] using hnext
  have hrow_hi : row ≤ start + 18 := by
    simpa [hnext_succ] using hnext_bound
  have hprev_lo : start ≤ prevRow air row := by
    rw [hprev_eq]
    omega
  have hprev_hi : prevRow air row ≤ start + 17 := by
    rw [hprev_eq]
    omega
  have hbits : isBitsWord (concatScheduleBitsWord air (prevRow air row) (slot + 1)) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (prevRow air row) (slot + 1) hwindow
        hsched_bits (by omega) hprev_lo (by omega)
  rw [hw7]
  simpa [concatScheduleU16Limb, hlimb] using
    (composeU16Limb_val_lt (concatScheduleBitsWord air (prevRow air row) (slot + 1)) hbits
      ⟨limb, hlimb⟩)

private theorem schedule_intermed12_u16_limb_lt_at
    (air : C FBB ExtF) (start row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (intermed_12 air slot limb row).val < 2 ^ 17 := by
  have hint :=
    intermed_12_from_pipeline_at air start row slot limb hslot hlimb hwindow hrot hshape hf hsc
      hnext hnext_bound
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hnext_succ] using hnext
  have hsrc_lo : start ≤ row - 3 := by
    omega
  have hsrc_hi : row - 3 ≤ start + 15 := by
    omega
  have hword_bits : isBitsWord (scheduleBitsWord air (row - 3) slot) := by
    exact
      scheduleBits_isBitsWord_from_block air start (row - 3) slot hsched_bits hslot hsrc_lo
        (by omega)
  have hconcat_bits : isBitsWord (concatScheduleBitsWord air (row - 3) (slot + 1)) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (row - 3) (slot + 1) hwindow hsched_bits
        (by omega) hsrc_lo (by omega)
  have hsigma_bits :
      isBitsWord (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    exact fieldSmallSigma0_isBitsWord _ hconcat_bits
  have hword_lt : (concatScheduleU16Limb air (row - 3) slot limb).val < 2 ^ 16 := by
    simpa [concatScheduleU16Limb, hlimb, concatScheduleBitsWord, hslot] using
      (composeU16Limb_val_lt (scheduleBitsWord air (row - 3) slot) hword_bits ⟨limb, hlimb⟩)
  have hsigma_lt :
      (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
        ⟨limb, hlimb⟩).val < 2 ^ 16 := by
    exact composeU16Limb_val_lt _ hsigma_bits ⟨limb, hlimb⟩
  have hsum_lt :
      (concatScheduleU16Limb air (row - 3) slot limb).val +
          (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
            ⟨limb, hlimb⟩).val <
        BB_prime := by
    omega
  have hval :
      (intermed_12 air slot limb row).val =
        (concatScheduleU16Limb air (row - 3) slot limb).val +
          (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
            ⟨limb, hlimb⟩).val := by
    have h := congrArg Fin.val hint
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    exact h
  rw [hval]
  omega

private abbrev scheduleCarryInTerm (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  if limb = 0 then 0 else scheduleCarryValue air (nextRow air row) slot (limb - 1)

private abbrev scheduleSigmaTerm (air : C FBB ExtF) (row slot limb : ℕ) (hlimb : limb < 4) : FBB :=
  composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) ⟨limb, hlimb⟩

private abbrev scheduleW7Term (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  scheduleW7U16Limb air row slot limb

private abbrev scheduleIntermedTerm (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  intermed_12 air slot limb row

private abbrev scheduleOutputTerm
    (air : C FBB ExtF) (row slot limb : ℕ) (hlimb : limb < 4) : FBB :=
  composeU16Limb (scheduleBitsWord air (nextRow air row) slot) ⟨limb, hlimb⟩

private abbrev scheduleCarryOutTerm (air : C FBB ExtF) (row slot limb : ℕ) : FBB :=
  scheduleCarryValue air (nextRow air row) slot limb

private abbrev scheduleSigmaPack (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (scheduleSigmaTerm air row slot 0 (by decide)).val +
    (scheduleSigmaTerm air row slot 1 (by decide)).val * 2 ^ 16 +
    (scheduleSigmaTerm air row slot 2 (by decide)).val * 2 ^ 32 +
    (scheduleSigmaTerm air row slot 3 (by decide)).val * 2 ^ 48

private abbrev scheduleW7Pack (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (scheduleW7Term air row slot 0).val +
    (scheduleW7Term air row slot 1).val * 2 ^ 16 +
    (scheduleW7Term air row slot 2).val * 2 ^ 32 +
    (scheduleW7Term air row slot 3).val * 2 ^ 48

private abbrev scheduleIntermedPack (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (scheduleIntermedTerm air row slot 0).val +
    (scheduleIntermedTerm air row slot 1).val * 2 ^ 16 +
    (scheduleIntermedTerm air row slot 2).val * 2 ^ 32 +
    (scheduleIntermedTerm air row slot 3).val * 2 ^ 48

private abbrev scheduleOutputPack (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (scheduleOutputTerm air row slot 0 (by decide)).val +
    (scheduleOutputTerm air row slot 1 (by decide)).val * 2 ^ 16 +
    (scheduleOutputTerm air row slot 2 (by decide)).val * 2 ^ 32 +
    (scheduleOutputTerm air row slot 3 (by decide)).val * 2 ^ 48

private abbrev schedulePrevConcatPack (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (concatScheduleU16Limb air (prevRow air row) (slot + 1) 0).val +
    (concatScheduleU16Limb air (prevRow air row) (slot + 1) 1).val * 2 ^ 16 +
    (concatScheduleU16Limb air (prevRow air row) (slot + 1) 2).val * 2 ^ 32 +
    (concatScheduleU16Limb air (prevRow air row) (slot + 1) 3).val * 2 ^ 48

private abbrev scheduleW16Pack (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (concatScheduleU16Limb air (row - 3) slot 0).val +
    (concatScheduleU16Limb air (row - 3) slot 1).val * 2 ^ 16 +
    (concatScheduleU16Limb air (row - 3) slot 2).val * 2 ^ 32 +
    (concatScheduleU16Limb air (row - 3) slot 3).val * 2 ^ 48

private abbrev scheduleSigma0Pack (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
      ⟨0, by decide⟩).val +
  (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
      ⟨1, by decide⟩).val * 2 ^ 16 +
  (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
      ⟨2, by decide⟩).val * 2 ^ 32 +
  (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
      ⟨3, by decide⟩).val * 2 ^ 48

private theorem schedule_carry_out_lt_four_at
    (air : C FBB ExtF) (start row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (scheduleCarryOutTerm air row slot limb).val < 4 := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  rcases
      next_row_round_and_not_first4 air start row hwindow hrot hshape hf hnext hnext_bound with
    ⟨hround_next, hnot_first4_next⟩
  simpa [scheduleCarryOutTerm] using
    next_msg_schedule_carry_value_lt_four_at air row slot limb hslot hlimb hrow_lt_last.le hrot
      (hsc row) hround_next hnot_first4_next

private theorem schedule_output_u16_limb_lt_at
    (air : C FBB ExtF) (start row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (scheduleOutputTerm air row slot limb hlimb).val < 2 ^ 16 := by
  have hbits : isBitsWord (scheduleBitsWord air (nextRow air row) slot) := by
    exact
      scheduleBits_isBitsWord_at_block_row air start (nextRow air row) slot hslot hwindow hrot
        hshape hsc (by omega) hnext_bound
  simpa [scheduleOutputTerm] using
    (composeU16Limb_val_lt (scheduleBitsWord air (nextRow air row) slot) hbits ⟨limb, hlimb⟩)

private theorem schedule_recurrence_u16_limb_nat_at
    (air : C FBB ExtF) (start row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    (scheduleCarryInTerm air row slot limb).val +
      (scheduleSigmaTerm air row slot limb hlimb).val +
      (scheduleW7Term air row slot limb).val +
      (scheduleIntermedTerm air row slot limb).val =
    (scheduleOutputTerm air row slot limb hlimb).val +
      (scheduleCarryOutTerm air row slot limb).val * 2 ^ 16 := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hfield :
      scheduleCarryInTerm air row slot limb +
          scheduleSigmaTerm air row slot limb hlimb +
          scheduleW7Term air row slot limb +
          scheduleIntermedTerm air row slot limb =
        scheduleOutputTerm air row slot limb hlimb +
          scheduleCarryOutTerm air row slot limb * (2 ^ 16 : ℕ) := by
    simpa [scheduleCarryInTerm, scheduleSigmaTerm, scheduleW7Term, scheduleIntermedTerm,
      scheduleOutputTerm, scheduleCarryOutTerm] using
      next_msg_schedule_recurrence_with_w7_at air row slot limb hslot hlimb hrow_lt_last.le hrot
        (hsc row)
  have hsigma_lt :
      (scheduleSigmaTerm air row slot limb hlimb).val < 2 ^ 16 := by
    simpa [scheduleSigmaTerm] using
      schedule_sigma1_u16_limb_lt_at air start row slot limb hslot hlimb hwindow hsched_bits hnext
        hnext_bound
  have hw7_lt :
      (scheduleW7Term air row slot limb).val < 2 ^ 16 := by
    simpa [scheduleW7Term] using
      schedule_w7_u16_limb_lt_at air start row slot limb hslot hlimb hwindow hrot hshape hsc
        hsched_bits hnext hnext_bound
  have hintermed_lt :
      (scheduleIntermedTerm air row slot limb).val < 2 ^ 17 := by
    simpa [scheduleIntermedTerm] using
      schedule_intermed12_u16_limb_lt_at air start row slot limb hslot hlimb hwindow hrot hshape
        hf hsc hsched_bits hnext hnext_bound
  have hcarry_out_lt :
      (scheduleCarryOutTerm air row slot limb).val < 4 := by
    exact
      schedule_carry_out_lt_four_at air start row slot limb hslot hlimb hwindow hrot hshape hf
        hsc hnext hnext_bound
  have houtput_lt :
      (scheduleOutputTerm air row slot limb hlimb).val < 2 ^ 16 := by
    exact
      schedule_output_u16_limb_lt_at air start row slot limb hslot hlimb hwindow hrot hshape hsc
        hnext hnext_bound
  have hcarry_in_lt :
      (scheduleCarryInTerm air row slot limb).val < 4 := by
    by_cases hzero : limb = 0
    · simp [scheduleCarryInTerm, hzero]
    · have hprev : limb - 1 < 4 := by
        omega
      simpa [scheduleCarryInTerm, hzero] using
        schedule_carry_out_lt_four_at air start row slot (limb - 1) hslot hprev hwindow hrot
          hshape hf hsc hnext hnext_bound
  have h := congrArg Fin.val hfield
  have hab :
      (scheduleCarryInTerm air row slot limb + scheduleSigmaTerm air row slot limb hlimb).val =
        (scheduleCarryInTerm air row slot limb).val +
          (scheduleSigmaTerm air row slot limb hlimb).val := by
    rw [babybear_add_no_wrap _ _ (by omega)]
  have habc :
      (scheduleCarryInTerm air row slot limb + scheduleSigmaTerm air row slot limb hlimb +
          scheduleW7Term air row slot limb).val =
        (scheduleCarryInTerm air row slot limb).val +
          (scheduleSigmaTerm air row slot limb hlimb).val +
          (scheduleW7Term air row slot limb).val := by
    have hmid :
        (scheduleCarryInTerm air row slot limb + scheduleSigmaTerm air row slot limb hlimb).val +
            (scheduleW7Term air row slot limb).val <
          BB_prime := by
      rw [hab]
      omega
    rw [babybear_add_no_wrap _ _ hmid, hab]
  have habcd :
      (scheduleCarryInTerm air row slot limb + scheduleSigmaTerm air row slot limb hlimb +
          scheduleW7Term air row slot limb + scheduleIntermedTerm air row slot limb).val =
        (scheduleCarryInTerm air row slot limb).val +
          (scheduleSigmaTerm air row slot limb hlimb).val +
          (scheduleW7Term air row slot limb).val +
          (scheduleIntermedTerm air row slot limb).val := by
    have hmid :
        (scheduleCarryInTerm air row slot limb + scheduleSigmaTerm air row slot limb hlimb +
            scheduleW7Term air row slot limb).val +
            (scheduleIntermedTerm air row slot limb).val <
          BB_prime := by
      rw [habc]
      omega
    rw [babybear_add_no_wrap _ _ hmid, habc]
  have hcarry_mul :
      (scheduleCarryOutTerm air row slot limb * (2 ^ 16 : ℕ)).val =
        (scheduleCarryOutTerm air row slot limb).val * 2 ^ 16 := by
    exact small_carry_mul_65536_val (scheduleCarryOutTerm air row slot limb) hcarry_out_lt
  have hsum_r :
      (scheduleOutputTerm air row slot limb hlimb +
          scheduleCarryOutTerm air row slot limb * (2 ^ 16 : ℕ)).val =
        (scheduleOutputTerm air row slot limb hlimb).val +
          (scheduleCarryOutTerm air row slot limb * (2 ^ 16 : ℕ)).val := by
    rw [babybear_add_no_wrap _ _ (by rw [hcarry_mul]; omega)]
  rw [habcd, hsum_r, hcarry_mul] at h
  exact h

private theorem schedule_recurrence_packed_nat_at
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    scheduleSigmaPack air row slot + scheduleW7Pack air row slot + scheduleIntermedPack air row slot =
      scheduleOutputPack air row slot + (scheduleCarryOutTerm air row slot 3).val * 2 ^ 64 := by
  have h0 :
      (scheduleSigmaTerm air row slot 0 (by decide)).val +
          (scheduleW7Term air row slot 0).val +
          (scheduleIntermedTerm air row slot 0).val =
        (scheduleOutputTerm air row slot 0 (by decide)).val +
          (scheduleCarryOutTerm air row slot 0).val * 2 ^ 16 := by
    simpa [scheduleCarryInTerm] using
      schedule_recurrence_u16_limb_nat_at air start row slot 0 hslot (by decide) hwindow hrot hshape
        hf hsc hsched_bits hnext hnext_bound
  have h1_base :
      (scheduleCarryOutTerm air row slot 0).val +
          (scheduleSigmaTerm air row slot 1 (by decide)).val +
          (scheduleW7Term air row slot 1).val +
          (scheduleIntermedTerm air row slot 1).val =
        (scheduleOutputTerm air row slot 1 (by decide)).val +
          (scheduleCarryOutTerm air row slot 1).val * 2 ^ 16 := by
    simpa [scheduleCarryInTerm] using
      schedule_recurrence_u16_limb_nat_at air start row slot 1 hslot (by decide) hwindow hrot hshape
        hf hsc hsched_bits hnext hnext_bound
  have h2_base :
      (scheduleCarryOutTerm air row slot 1).val +
          (scheduleSigmaTerm air row slot 2 (by decide)).val +
          (scheduleW7Term air row slot 2).val +
          (scheduleIntermedTerm air row slot 2).val =
        (scheduleOutputTerm air row slot 2 (by decide)).val +
          (scheduleCarryOutTerm air row slot 2).val * 2 ^ 16 := by
    simpa [scheduleCarryInTerm] using
      schedule_recurrence_u16_limb_nat_at air start row slot 2 hslot (by decide) hwindow hrot hshape
        hf hsc hsched_bits hnext hnext_bound
  have h3_base :
      (scheduleCarryOutTerm air row slot 2).val +
          (scheduleSigmaTerm air row slot 3 (by decide)).val +
          (scheduleW7Term air row slot 3).val +
          (scheduleIntermedTerm air row slot 3).val =
        (scheduleOutputTerm air row slot 3 (by decide)).val +
          (scheduleCarryOutTerm air row slot 3).val * 2 ^ 16 := by
    simpa [scheduleCarryInTerm] using
      schedule_recurrence_u16_limb_nat_at air start row slot 3 hslot (by decide) hwindow hrot hshape
        hf hsc hsched_bits hnext hnext_bound
  have h1 := congrArg (fun n : ℕ => n * 2 ^ 16) h1_base
  have h2 := congrArg (fun n : ℕ => n * 2 ^ 32) h2_base
  have h3 := congrArg (fun n : ℕ => n * 2 ^ 48) h3_base
  dsimp [scheduleSigmaPack, scheduleW7Pack, scheduleIntermedPack, scheduleOutputPack]
  norm_num at h1 h2 h3 ⊢
  omega

private theorem schedule_w7_packed_from_concat_prev_nat_at
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    scheduleW7Pack air row slot = schedulePrevConcatPack air row slot := by
  have h0 := congrArg Fin.val
    (schedule_w7_u16_limb_from_concat_prev_at air start row slot 0 hslot (by decide) hwindow hrot
      hshape hsc hnext hnext_bound)
  have h1 := congrArg Fin.val
    (schedule_w7_u16_limb_from_concat_prev_at air start row slot 1 hslot (by decide) hwindow hrot
      hshape hsc hnext hnext_bound)
  have h2 := congrArg Fin.val
    (schedule_w7_u16_limb_from_concat_prev_at air start row slot 2 hslot (by decide) hwindow hrot
      hshape hsc hnext hnext_bound)
  have h3 := congrArg Fin.val
    (schedule_w7_u16_limb_from_concat_prev_at air start row slot 3 hslot (by decide) hwindow hrot
      hshape hsc hnext hnext_bound)
  dsimp [scheduleW7Pack, schedulePrevConcatPack]
  rw [h0, h1, h2, h3]

private theorem schedule_intermed_packed_from_sources_nat_at
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    scheduleIntermedPack air row slot =
      scheduleW16Pack air row slot + scheduleSigma0Pack air row slot := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hnext_succ] using hnext
  have hrow_hi : row ≤ start + 18 := by
    simpa [hnext_succ] using hnext_bound
  have hsrc_lo : start ≤ row - 3 := by
    omega
  have hsrc_hi : row - 3 ≤ start + 15 := by
    omega
  have hword_bits : isBitsWord (scheduleBitsWord air (row - 3) slot) := by
    exact
      scheduleBits_isBitsWord_from_block air start (row - 3) slot hsched_bits hslot hsrc_lo
        (by omega)
  have hconcat_bits : isBitsWord (concatScheduleBitsWord air (row - 3) (slot + 1)) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (row - 3) (slot + 1) hwindow hsched_bits
        (by omega) hsrc_lo (by omega)
  have hsigma_bits :
      isBitsWord (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    exact fieldSmallSigma0_isBitsWord _ hconcat_bits
  have h0_field :=
    intermed_12_from_pipeline_at air start row slot 0 hslot (by decide) hwindow hrot hshape hf hsc
      hnext hnext_bound
  have h1_field :=
    intermed_12_from_pipeline_at air start row slot 1 hslot (by decide) hwindow hrot hshape hf hsc
      hnext hnext_bound
  have h2_field :=
    intermed_12_from_pipeline_at air start row slot 2 hslot (by decide) hwindow hrot hshape hf hsc
      hnext hnext_bound
  have h3_field :=
    intermed_12_from_pipeline_at air start row slot 3 hslot (by decide) hwindow hrot hshape hf hsc
      hnext hnext_bound
  have h0 :
      (scheduleIntermedTerm air row slot 0).val =
        (concatScheduleU16Limb air (row - 3) slot 0).val +
          (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
            ⟨0, by decide⟩).val := by
    have hw16_src_lt :
        (concatScheduleU16Limb air (row - 3) slot 0).val < 2 ^ 16 := by
      simpa [concatScheduleU16Limb, concatScheduleBitsWord, hslot] using
        (composeU16Limb_val_lt (scheduleBitsWord air (row - 3) slot) hword_bits ⟨0, by decide⟩)
    have hsigma_lt :
        (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
          ⟨0, by decide⟩).val < 2 ^ 16 := by
      exact composeU16Limb_val_lt _ hsigma_bits ⟨0, by decide⟩
    have hsum_lt :
        (concatScheduleU16Limb air (row - 3) slot 0).val +
            (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
              ⟨0, by decide⟩).val <
          BB_prime := by
      omega
    have h := congrArg Fin.val h0_field
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    simpa [scheduleIntermedTerm] using h
  have h1 :
      (scheduleIntermedTerm air row slot 1).val =
        (concatScheduleU16Limb air (row - 3) slot 1).val +
          (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
            ⟨1, by decide⟩).val := by
    have hw16_src_lt :
        (concatScheduleU16Limb air (row - 3) slot 1).val < 2 ^ 16 := by
      simpa [concatScheduleU16Limb, concatScheduleBitsWord, hslot] using
        (composeU16Limb_val_lt (scheduleBitsWord air (row - 3) slot) hword_bits ⟨1, by decide⟩)
    have hsigma_lt :
        (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
          ⟨1, by decide⟩).val < 2 ^ 16 := by
      exact composeU16Limb_val_lt _ hsigma_bits ⟨1, by decide⟩
    have hsum_lt :
        (concatScheduleU16Limb air (row - 3) slot 1).val +
            (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
              ⟨1, by decide⟩).val <
          BB_prime := by
      omega
    have h := congrArg Fin.val h1_field
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    simpa [scheduleIntermedTerm] using h
  have h2 :
      (scheduleIntermedTerm air row slot 2).val =
        (concatScheduleU16Limb air (row - 3) slot 2).val +
          (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
            ⟨2, by decide⟩).val := by
    have hw16_src_lt :
        (concatScheduleU16Limb air (row - 3) slot 2).val < 2 ^ 16 := by
      simpa [concatScheduleU16Limb, concatScheduleBitsWord, hslot] using
        (composeU16Limb_val_lt (scheduleBitsWord air (row - 3) slot) hword_bits ⟨2, by decide⟩)
    have hsigma_lt :
        (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
          ⟨2, by decide⟩).val < 2 ^ 16 := by
      exact composeU16Limb_val_lt _ hsigma_bits ⟨2, by decide⟩
    have hsum_lt :
        (concatScheduleU16Limb air (row - 3) slot 2).val +
            (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
              ⟨2, by decide⟩).val <
          BB_prime := by
      omega
    have h := congrArg Fin.val h2_field
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    simpa [scheduleIntermedTerm] using h
  have h3 :
      (scheduleIntermedTerm air row slot 3).val =
        (concatScheduleU16Limb air (row - 3) slot 3).val +
          (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
            ⟨3, by decide⟩).val := by
    have hw16_src_lt :
        (concatScheduleU16Limb air (row - 3) slot 3).val < 2 ^ 16 := by
      simpa [concatScheduleU16Limb, concatScheduleBitsWord, hslot] using
        (composeU16Limb_val_lt (scheduleBitsWord air (row - 3) slot) hword_bits ⟨3, by decide⟩)
    have hsigma_lt :
        (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
          ⟨3, by decide⟩).val < 2 ^ 16 := by
      exact composeU16Limb_val_lt _ hsigma_bits ⟨3, by decide⟩
    have hsum_lt :
        (concatScheduleU16Limb air (row - 3) slot 3).val +
            (composeU16Limb (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))
              ⟨3, by decide⟩).val <
          BB_prime := by
      omega
    have h := congrArg Fin.val h3_field
    rw [babybear_add_no_wrap _ _ hsum_lt] at h
    simpa [scheduleIntermedTerm] using h
  dsimp at h0 h1 h2 h3
  have h1w := congrArg (fun n : ℕ => n * 2 ^ 16) h1
  have h2w := congrArg (fun n : ℕ => n * 2 ^ 32) h2
  have h3w := congrArg (fun n : ℕ => n * 2 ^ 48) h3
  dsimp [scheduleIntermedPack, scheduleW16Pack, scheduleSigma0Pack]
  norm_num at h1w h2w h3w ⊢
  rw [h0, h1w, h2w, h3w]
  ring_nf

private theorem schedule_recurrence_packed_from_sources_nat_at
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    scheduleSigmaPack air row slot + schedulePrevConcatPack air row slot +
        (scheduleW16Pack air row slot + scheduleSigma0Pack air row slot) =
      scheduleOutputPack air row slot + (scheduleCarryOutTerm air row slot 3).val * 2 ^ 64 := by
  rw [← schedule_w7_packed_from_concat_prev_nat_at air start row slot hslot hwindow hrot hshape hsc
      hnext hnext_bound,
    ← schedule_intermed_packed_from_sources_nat_at air start row slot hslot hwindow hrot hshape hf
      hsc hsched_bits hnext hnext_bound]
  simpa [Nat.add_assoc] using
    schedule_recurrence_packed_nat_at air start row slot hslot hwindow hrot hshape hf hsc
      hsched_bits hnext hnext_bound

/-- Any exposed SHA-512 successor word reconstructs as a `UInt64` from the
    slot-parametric packed nat recurrence. -/
theorem next_msg_schedule_recurrence_uint64_at
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    scheduleWordAtRow air (nextRow air row) slot =
      bitsWordToUInt64 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) +
        concatScheduleWord air (prevRow air row) (slot + 1) +
        (concatScheduleWord air (row - 3) slot +
          bitsWordToUInt64 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))) := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start ≤ row := by
    omega
  have hrow_hi : row ≤ start + 18 := by
    simpa [hnext_succ] using hnext_bound
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hprev_lo : start ≤ prevRow air row := by
    rw [hprev_eq]
    omega
  have hprev_hi : prevRow air row ≤ start + 17 := by
    rw [hprev_eq]
    omega
  have hsigma_bits :
      isBitsWord (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) := by
    exact fieldSmallSigma1_isBitsWord _ <|
      concatScheduleBits_isBitsWord_from_block air start row (slot + 2) hwindow hsched_bits
        (by omega) hrow_lo hrow_hi
  have hw7_bits :
      isBitsWord (concatScheduleBitsWord air (prevRow air row) (slot + 1)) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (prevRow air row) (slot + 1) hwindow
        hsched_bits (by omega) hprev_lo (by omega)
  have hw16_bits : isBitsWord (concatScheduleBitsWord air (row - 3) slot) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (row - 3) slot hwindow hsched_bits
        (by omega) (by omega) (by omega)
  have hsigma0_bits :
      isBitsWord (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) := by
    exact fieldSmallSigma0_isBitsWord _ <|
      concatScheduleBits_isBitsWord_from_block air start (row - 3) (slot + 1) hwindow hsched_bits
        (by omega) (by omega) (by omega)
  have houtput_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot) := by
    exact
      scheduleBits_isBitsWord_from_block air start (nextRow air row) slot hsched_bits hslot
        (by omega) hnext_bound
  have hsigma_word :
      bitsWordToUInt64 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) =
        (scheduleSigmaPack air row slot).toUInt64 := by
    simpa [scheduleSigmaPack, scheduleSigmaTerm] using
      bitsWordToUInt64_eq_compose16 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))
        hsigma_bits
  have hw7_word :
      concatScheduleWord air (prevRow air row) (slot + 1) =
        (schedulePrevConcatPack air row slot).toUInt64 := by
    rw [concatScheduleWord]
    simpa [schedulePrevConcatPack, concatScheduleU16Limb] using
      bitsWordToUInt64_eq_compose16 (concatScheduleBitsWord air (prevRow air row) (slot + 1))
        hw7_bits
  have hw16_word :
      concatScheduleWord air (row - 3) slot =
        (scheduleW16Pack air row slot).toUInt64 := by
    rw [concatScheduleWord]
    simpa [scheduleW16Pack, concatScheduleU16Limb] using
      bitsWordToUInt64_eq_compose16 (concatScheduleBitsWord air (row - 3) slot) hw16_bits
  have hsigma0_word :
      bitsWordToUInt64 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) =
        (scheduleSigma0Pack air row slot).toUInt64 := by
    simpa [scheduleSigma0Pack] using
      bitsWordToUInt64_eq_compose16
        (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) hsigma0_bits
  have houtput_word :
      scheduleWordAtRow air (nextRow air row) slot =
        (scheduleOutputPack air row slot).toUInt64 := by
    rw [scheduleWordAtRow_eq_bitsWordToUInt64]
    simpa [scheduleOutputPack, scheduleOutputTerm] using
      bitsWordToUInt64_eq_compose16 (scheduleBitsWord air (nextRow air row) slot) houtput_bits
  have hsigma_nat :
      (bitsWordToUInt64 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))).toNat =
        scheduleSigmaPack air row slot % 2 ^ 64 := by
    simpa [UInt64.toNat_ofNat] using congrArg UInt64.toNat hsigma_word
  have hw7_nat :
      (concatScheduleWord air (prevRow air row) (slot + 1)).toNat =
        schedulePrevConcatPack air row slot % 2 ^ 64 := by
    simpa [UInt64.toNat_ofNat] using congrArg UInt64.toNat hw7_word
  have hw16_nat :
      (concatScheduleWord air (row - 3) slot).toNat =
        scheduleW16Pack air row slot % 2 ^ 64 := by
    simpa [UInt64.toNat_ofNat] using congrArg UInt64.toNat hw16_word
  have hsigma0_nat :
      (bitsWordToUInt64 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)))).toNat =
        scheduleSigma0Pack air row slot % 2 ^ 64 := by
    simpa [UInt64.toNat_ofNat] using congrArg UInt64.toNat hsigma0_word
  have houtput_nat :
      (scheduleWordAtRow air (nextRow air row) slot).toNat =
        scheduleOutputPack air row slot % 2 ^ 64 := by
    simpa [UInt64.toNat_ofNat] using congrArg UInt64.toNat houtput_word
  have hsum_nat :
      (bitsWordToUInt64 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) +
          concatScheduleWord air (prevRow air row) (slot + 1) +
          (concatScheduleWord air (row - 3) slot +
            bitsWordToUInt64 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))))).toNat =
        (scheduleSigmaPack air row slot + schedulePrevConcatPack air row slot +
            (scheduleW16Pack air row slot + scheduleSigma0Pack air row slot)) % 2 ^ 64 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, hsigma_nat, hw7_nat, hw16_nat,
      hsigma0_nat]
    omega
  have hpacked_mod :
      (scheduleSigmaPack air row slot + schedulePrevConcatPack air row slot +
          (scheduleW16Pack air row slot + scheduleSigma0Pack air row slot)) % 2 ^ 64 =
        scheduleOutputPack air row slot % 2 ^ 64 := by
    rw [schedule_recurrence_packed_from_sources_nat_at air start row slot hslot hwindow hrot hshape
      hf hsc hsched_bits hnext hnext_bound]
    omega
  apply UInt64_eq_of_toNat_eq
  rw [houtput_nat, hsum_nat, hpacked_mod]

private theorem schedule_sigma1_term_eq_smallSigma1_word_at
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    bitsWordToUInt64 (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) =
      smallSigma1 (concatScheduleWord air row (slot + 2)) := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hbits :
      isBitsWord (concatScheduleBitsWord air row (slot + 2)) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start row (slot + 2) hwindow hsched_bits
        (by omega) (by omega) (by simpa [hnext_succ] using hnext_bound)
  simpa [concatScheduleWord] using
    fieldSmallSigma1_eq_smallSigma1 (concatScheduleBitsWord air row (slot + 2)) hbits

private theorem schedule_sigma0_source_eq_smallSigma0_word_at
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    bitsWordToUInt64 (fieldSmallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1))) =
      smallSigma0 (concatScheduleWord air (row - 3) (slot + 1)) := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_lo : start + 3 ≤ row := by
    simpa [hnext_succ] using hnext
  have hsrc_lo : start ≤ row - 3 := by
    omega
  have hsrc_hi : row - 3 ≤ start + 15 := by
    have hrow_hi : row ≤ start + 18 := by
      simpa [hnext_succ] using hnext_bound
    omega
  have hbits :
      isBitsWord (concatScheduleBitsWord air (row - 3) (slot + 1)) := by
    exact
      concatScheduleBits_isBitsWord_from_block air start (row - 3) (slot + 1) hwindow hsched_bits
        (by omega) hsrc_lo (by omega)
  simpa [concatScheduleWord] using
    fieldSmallSigma0_eq_smallSigma0 (concatScheduleBitsWord air (row - 3) (slot + 1)) hbits

/-- Any exposed SHA-512 successor-word recurrence can be stated entirely over
    trace words, with the `σ₁` and `σ₀` terms rewritten out of the field-bit
    layer. -/
theorem next_msg_schedule_recurrence_trace_words_at
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    scheduleWordAtRow air (nextRow air row) slot =
      smallSigma1 (concatScheduleWord air row (slot + 2)) +
        concatScheduleWord air (prevRow air row) (slot + 1) +
        (concatScheduleWord air (row - 3) slot +
          smallSigma0 (concatScheduleWord air (row - 3) (slot + 1))) := by
  have hbase :=
    next_msg_schedule_recurrence_uint64_at air start row slot hslot hwindow hrot hshape hf hsc
      hsched_bits hnext hnext_bound
  rw [schedule_sigma1_term_eq_smallSigma1_word_at air start row slot hslot hwindow hsched_bits hnext
      hnext_bound,
    schedule_sigma0_source_eq_smallSigma0_word_at air start row slot hslot hwindow hsched_bits hnext
      hnext_bound] at hbase
  exact hbase

/-- Slot-`1` transport for the SHA-512 successor-word recurrence. -/
private theorem next_msg_schedule_recurrence_slot1
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4 + 1
    scheduleWordAtRow air (nextRow air row) 1 =
      smallSigma1 (scheduleWordAtRow air (start + (t - 2) / 4) ((t - 2) % 4)) +
        scheduleWordAtRow air (start + (t - 7) / 4) ((t - 7) % 4) +
        (scheduleWordAtRow air (start + (t - 16) / 4) ((t - 16) % 4) +
          smallSigma0 (scheduleWordAtRow air (start + (t - 15) / 4) ((t - 15) % 4))) := by
  dsimp
  have hbase :=
    next_msg_schedule_recurrence_trace_words_at air start row 1 (by omega) hwindow hrot hshape
      hf hsc hsched_bits hnext hnext_bound
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hsigma_row :
      start + ((((nextRow air row - start) * 4 + 1) - 2) / 4) = row := by
    rw [hnext_succ]
    omega
  have hsigma_slot :
      ((((nextRow air row - start) * 4 + 1) - 2) % 4) = 3 := by
    rw [hnext_succ]
    omega
  have hw7_row :
      start + ((((nextRow air row - start) * 4 + 1) - 7) / 4) = prevRow air row := by
    rw [hprev_eq, hnext_succ]
    omega
  have hw7_slot :
      ((((nextRow air row - start) * 4 + 1) - 7) % 4) = 2 := by
    rw [hnext_succ]
    omega
  have hw16_row :
      start + ((((nextRow air row - start) * 4 + 1) - 16) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw16_slot :
      ((((nextRow air row - start) * 4 + 1) - 16) % 4) = 1 := by
    rw [hnext_succ]
    omega
  have hw15_row :
      start + ((((nextRow air row - start) * 4 + 1) - 15) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw15_slot :
      ((((nextRow air row - start) * 4 + 1) - 15) % 4) = 2 := by
    rw [hnext_succ]
    omega
  have hsigma_word :
      concatScheduleWord air row 3 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 1) - 2) / 4))
          ((((nextRow air row - start) * 4 + 1) - 2) % 4) := by
    rw [hsigma_row, hsigma_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  have hw7_word :
      concatScheduleWord air (prevRow air row) 2 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 1) - 7) / 4))
          ((((nextRow air row - start) * 4 + 1) - 7) % 4) := by
    rw [hw7_row, hw7_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  have hw16_word :
      concatScheduleWord air (row - 3) 1 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 1) - 16) / 4))
          ((((nextRow air row - start) * 4 + 1) - 16) % 4) := by
    rw [hw16_row, hw16_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  have hsigma0_word :
      concatScheduleWord air (row - 3) 2 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 1) - 15) / 4))
          ((((nextRow air row - start) * 4 + 1) - 15) % 4) := by
    rw [hw15_row, hw15_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  rw [hsigma_word, hw7_word, hw16_word, hsigma0_word] at hbase
  exact hbase

/-- Slot-`2` transport for the SHA-512 successor-word recurrence. -/
private theorem next_msg_schedule_recurrence_slot2
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4 + 2
    scheduleWordAtRow air (nextRow air row) 2 =
      smallSigma1 (scheduleWordAtRow air (start + (t - 2) / 4) ((t - 2) % 4)) +
        scheduleWordAtRow air (start + (t - 7) / 4) ((t - 7) % 4) +
        (scheduleWordAtRow air (start + (t - 16) / 4) ((t - 16) % 4) +
          smallSigma0 (scheduleWordAtRow air (start + (t - 15) / 4) ((t - 15) % 4))) := by
  dsimp
  have hbase :=
    next_msg_schedule_recurrence_trace_words_at air start row 2 (by omega) hwindow hrot hshape
      hf hsc hsched_bits hnext hnext_bound
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hprev_next : nextRow air (prevRow air row) = row := by
    rw [hprev_eq, nextRow]
    have hprev_lt_last : row - 1 < Circuit.last_row air := by
      omega
    simp [hprev_lt_last.ne]
    omega
  have hsigma_row :
      start + ((((nextRow air row - start) * 4 + 2) - 2) / 4) = nextRow air row := by
    rw [hnext_succ]
    omega
  have hsigma_slot :
      ((((nextRow air row - start) * 4 + 2) - 2) % 4) = 0 := by
    rw [hnext_succ]
    omega
  have hw7_row :
      start + ((((nextRow air row - start) * 4 + 2) - 7) / 4) = prevRow air row := by
    rw [hprev_eq, hnext_succ]
    omega
  have hw7_slot :
      ((((nextRow air row - start) * 4 + 2) - 7) % 4) = 3 := by
    rw [hnext_succ]
    omega
  have hw16_row :
      start + ((((nextRow air row - start) * 4 + 2) - 16) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw16_slot :
      ((((nextRow air row - start) * 4 + 2) - 16) % 4) = 2 := by
    rw [hnext_succ]
    omega
  have hw15_row :
      start + ((((nextRow air row - start) * 4 + 2) - 15) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw15_slot :
      ((((nextRow air row - start) * 4 + 2) - 15) % 4) = 3 := by
    rw [hnext_succ]
    omega
  have hsigma_word :
      concatScheduleWord air row 4 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 2) - 2) / 4))
          ((((nextRow air row - start) * 4 + 2) - 2) % 4) := by
    rw [hsigma_row, hsigma_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord, hnext_succ]
  have hw7_word :
      concatScheduleWord air (prevRow air row) 3 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 2) - 7) / 4))
          ((((nextRow air row - start) * 4 + 2) - 7) % 4) := by
    rw [hw7_row, hw7_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  have hw16_word :
      concatScheduleWord air (row - 3) 2 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 2) - 16) / 4))
          ((((nextRow air row - start) * 4 + 2) - 16) % 4) := by
    rw [hw16_row, hw16_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  have hsigma0_word :
      concatScheduleWord air (row - 3) 3 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 2) - 15) / 4))
          ((((nextRow air row - start) * 4 + 2) - 15) % 4) := by
    rw [hw15_row, hw15_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  rw [hsigma_word, hw7_word, hw16_word, hsigma0_word] at hbase
  exact hbase

/-- Slot-`3` transport for the SHA-512 successor-word recurrence. -/
private theorem next_msg_schedule_recurrence_slot3
    (air : C FBB ExtF) (start row : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4 + 3
    scheduleWordAtRow air (nextRow air row) 3 =
      smallSigma1 (scheduleWordAtRow air (start + (t - 2) / 4) ((t - 2) % 4)) +
        scheduleWordAtRow air (start + (t - 7) / 4) ((t - 7) % 4) +
        (scheduleWordAtRow air (start + (t - 16) / 4) ((t - 16) % 4) +
          smallSigma0 (scheduleWordAtRow air (start + (t - 15) / 4) ((t - 15) % 4))) := by
  dsimp
  have hbase :=
    next_msg_schedule_recurrence_trace_words_at air start row 3 (by omega) hwindow hrot hshape
      hf hsc hsched_bits hnext hnext_bound
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hprev_next : nextRow air (prevRow air row) = row := by
    rw [hprev_eq, nextRow]
    have hprev_lt_last : row - 1 < Circuit.last_row air := by
      omega
    simp [hprev_lt_last.ne]
    omega
  have hprev_next' : nextRow air (row - 1) = row := by
    simpa [hprev_eq] using hprev_next
  have hsigma_row :
      start + ((((nextRow air row - start) * 4 + 3) - 2) / 4) = nextRow air row := by
    rw [hnext_succ]
    omega
  have hsigma_slot :
      ((((nextRow air row - start) * 4 + 3) - 2) % 4) = 1 := by
    rw [hnext_succ]
    omega
  have hw7_row :
      start + ((((nextRow air row - start) * 4 + 3) - 7) / 4) = row := by
    rw [hnext_succ]
    omega
  have hw7_slot :
      ((((nextRow air row - start) * 4 + 3) - 7) % 4) = 0 := by
    rw [hnext_succ]
    omega
  have hw16_row :
      start + ((((nextRow air row - start) * 4 + 3) - 16) / 4) = row - 3 := by
    rw [hnext_succ]
    omega
  have hw16_slot :
      ((((nextRow air row - start) * 4 + 3) - 16) % 4) = 3 := by
    rw [hnext_succ]
    omega
  have hw15_row :
      start + ((((nextRow air row - start) * 4 + 3) - 15) / 4) = nextRow air (row - 3) := by
    rw [hnext_succ, nextRow]
    have hrowm3_lt_last : row - 3 < Circuit.last_row air := by
      omega
    simp [hrowm3_lt_last.ne]
    omega
  have hw15_slot :
      ((((nextRow air row - start) * 4 + 3) - 15) % 4) = 0 := by
    rw [hnext_succ]
    omega
  have hsigma_word :
      concatScheduleWord air row 5 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 3) - 2) / 4))
          ((((nextRow air row - start) * 4 + 3) - 2) % 4) := by
    rw [hsigma_row, hsigma_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord, hnext_succ]
  have hw7_word :
      concatScheduleWord air (prevRow air row) 4 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 3) - 7) / 4))
          ((((nextRow air row - start) * 4 + 3) - 7) % 4) := by
    rw [hprev_eq, hw7_row, hw7_slot, scheduleWordAtRow_eq_bitsWordToUInt64, concatScheduleWord,
      concatScheduleBitsWord]
    simp only [show ¬ 4 < 4 by decide, if_false, Nat.sub_self]
    rw [hprev_next']
  have hw16_word :
      concatScheduleWord air (row - 3) 3 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 3) - 16) / 4))
          ((((nextRow air row - start) * 4 + 3) - 16) % 4) := by
    rw [hw16_row, hw16_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    simp [concatScheduleWord, concatScheduleBitsWord]
  have hsigma0_word :
      concatScheduleWord air (row - 3) 4 =
        scheduleWordAtRow air (start + ((((nextRow air row - start) * 4 + 3) - 15) / 4))
          ((((nextRow air row - start) * 4 + 3) - 15) % 4) := by
    rw [hw15_row, hw15_slot, scheduleWordAtRow_eq_bitsWordToUInt64]
    have hrowm3_lt_last : row - 3 < Circuit.last_row air := by
      omega
    simp [concatScheduleWord, concatScheduleBitsWord, nextRow, hrowm3_lt_last.ne]
  rw [hsigma_word, hw7_word, hw16_word, hsigma0_word] at hbase
  exact hbase

/-- The slot-parametric SHA-512 successor-word recurrence packaged back into
    the block-local `t`-indexed source coordinates used by schedule-step
    assembly. -/
theorem next_msg_schedule_recurrence
    (air : C FBB ExtF) (start row slot : ℕ)
    (hslot : slot < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4 + slot
    scheduleWordAtRow air (nextRow air row) slot =
      smallSigma1 (scheduleWordAtRow air (start + (t - 2) / 4) ((t - 2) % 4)) +
        scheduleWordAtRow air (start + (t - 7) / 4) ((t - 7) % 4) +
        (scheduleWordAtRow air (start + (t - 16) / 4) ((t - 16) % 4) +
          smallSigma0 (scheduleWordAtRow air (start + (t - 15) / 4) ((t - 15) % 4))) := by
  interval_cases slot
  · simpa using
      next_msg_schedule_word0_recurrence air start row hwindow hrot hshape hf hsc hsched_bits hnext
        hnext_bound
  · simpa using
      next_msg_schedule_recurrence_slot1 air start row hwindow hrot hshape hf hsc hsched_bits hnext
        hnext_bound
  · simpa using
      next_msg_schedule_recurrence_slot2 air start row hwindow hrot hshape hf hsc hsched_bits hnext
        hnext_bound
  · simpa using
      next_msg_schedule_recurrence_slot3 air start row hwindow hrot hshape hf hsc hsched_bits hnext
        hnext_bound

/-! ## B6: Slot-0 `expandSchedule` consumers -/

/-- Base case: for `t < 16`, the schedule words are the raw input words. -/
theorem expandSchedule_base (air : C FBB ExtF) (start : ℕ) (t : ℕ)
    (ht : t < 16) :
    scheduleWordAtRow air (start + t / 4) (t % 4) =
      (expandSchedule (blockInputWords air start))[t]! := by
  have hi : t < (blockInputWords air start).size := by
    simpa [blockInputWords] using ht
  have hprefix :=
    getElem!_foldl_push_preserved
      (l := List.range 64)
      (f := fun acc offset =>
        smallSigma1 acc[offset + 14]! +
        acc[offset + 9]! +
        smallSigma0 acc[offset + 1]! +
        acc[offset]!)
      (xs := blockInputWords air start) (i := t) hi
  rw [expandSchedule_eq_foldl]
  rw [hprefix]
  simpa [blockInputWords, inputWord, ht]

/-- Inductive slot-`0` transport step: when all earlier schedule words already
    match `TraceSpec.expandSchedule` and the abstract schedule is known to
    satisfy its recurrence at index `t`, the next slot-`0` word produced by the
    block window matches `expandSchedule[t]`. -/
theorem expandSchedule_step_word0 (air : C FBB ExtF) (start : ℕ) (t : ℕ)
    (ht_lo : 16 ≤ t) (ht_hi : t < 80) (ht_slot0 : t % 4 = 0)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hexpand_t :
      (expandSchedule (blockInputWords air start))[t]! =
        smallSigma1 ((expandSchedule (blockInputWords air start))[t - 2]!) +
          (expandSchedule (blockInputWords air start))[t - 7]! +
          ((expandSchedule (blockInputWords air start))[t - 16]! +
            smallSigma0 ((expandSchedule (blockInputWords air start))[t - 15]!)))
    (ih : ∀ s, s < t →
      scheduleWordAtRow air (start + s / 4) (s % 4) =
        (expandSchedule (blockInputWords air start))[s]!) :
    scheduleWordAtRow air (start + t / 4) 0 =
      (expandSchedule (blockInputWords air start))[t]! := by
  set row := start + t / 4 - 1
  have hrow_lt_last : row < Circuit.last_row air := by
    have hsupp : start + 20 ≤ Circuit.last_row air := by
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
  have hnext_bound : nextRow air row ≤ start + 19 := by
    rw [hrow_next]
    omega
  have hrec :=
    next_msg_schedule_word0_recurrence air start row hwindow hrot hshape hf hsc hsched_bits hnext
      hnext_bound
  rw [hrow_next] at hrec
  dsimp only at hrec
  have ht_rec : (((start + t / 4) - start) * 4) = t := by
    omega
  rw [ht_rec] at hrec
  rw [ih (t - 2) (by omega), ih (t - 7) (by omega), ih (t - 15) (by omega),
    ih (t - 16) (by omega)] at hrec
  calc
    scheduleWordAtRow air (start + t / 4) 0 =
        smallSigma1 ((expandSchedule (blockInputWords air start))[t - 2]!) +
          (expandSchedule (blockInputWords air start))[t - 7]! +
          ((expandSchedule (blockInputWords air start))[t - 16]! +
            smallSigma0 ((expandSchedule (blockInputWords air start))[t - 15]!)) := by
          simpa [add_assoc, add_left_comm, add_comm] using hrec
    _ = (expandSchedule (blockInputWords air start))[t]! := hexpand_t.symm

private theorem expandSchedule_word16_from_input (input : Array Word)
    (hsize : input.size = 16) :
    (expandSchedule input)[16]! =
      smallSigma1 input[14]! + input[9]! + (input[0]! + smallSigma0 input[1]!) := by
  set step : Array Word → ℕ → Word :=
    fun acc offset =>
      smallSigma1 acc[offset + 14]! +
      acc[offset + 9]! +
      smallSigma0 acc[offset + 1]! +
      acc[offset]!
  set schedPrefix := input
  have hprefix_size : schedPrefix.size = 16 := by
    simpa [schedPrefix] using hsize
  have hrange :
      List.range 64 =
        List.range (0 + 1) ++ (List.range (64 - (0 + 1))).map (0 + 1 + ·) := by
    have h64 : 64 = (0 + 1) + (64 - (0 + 1)) := by
      omega
    rw [h64]
    simpa [Nat.add_sub_cancel_left] using
      (List.range_add (n := 0 + 1) (m := 64 - (0 + 1)))
  have hprefix_succ :
      (List.range (0 + 1)).foldl (fun acc off => acc.push (step acc off)) input =
        schedPrefix.push (step schedPrefix 0) := by
    rw [show List.range (0 + 1) = List.range 0 ++ [0] by
      simpa using (List.range_succ (n := 0))]
    simp [schedPrefix]
  have hexpand16 :
      (expandSchedule input)[16]! = step schedPrefix 0 := by
    rw [expandSchedule_eq_foldl, hrange, List.foldl_append, hprefix_succ]
    rw [getElem!_foldl_push_preserved
      (l := (List.range (64 - (0 + 1))).map (0 + 1 + ·))
      (f := step)
      (xs := schedPrefix.push (step schedPrefix 0))
      (i := 16)]
    · simpa [hprefix_size] using
        (getElem!_push_size (xs := schedPrefix) (x := step schedPrefix 0))
    · simp [hprefix_size]
  simpa [step, schedPrefix, add_assoc, add_left_comm, add_comm] using hexpand16

/-- The first expanded SHA-512 schedule word produced on the block window,
    `w[16]`, matches the abstract `TraceSpec.expandSchedule` recurrence. -/
theorem expandSchedule_word16
    (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start) :
    scheduleWordAtRow air (start + 4) 0 =
      (expandSchedule (blockInputWords air start))[16]! := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : start + 3 < Circuit.last_row air := by
    omega
  have hnext_row : nextRow air (start + 3) = start + 4 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrec :=
    next_msg_schedule_word0_recurrence air start (start + 3) hwindow hrot hshape hf hsc
      hsched_bits (by simpa [hnext_row]) (by simpa [hnext_row])
  have ht :
      ((nextRow air (start + 3) - start) * 4) = 16 := by
    rw [hnext_row]
    omega
  rw [hnext_row] at hrec
  dsimp only at hrec
  have ht' : ((start + 4 - start) * 4) = 16 := by
    omega
  rw [ht'] at hrec
  norm_num at hrec
  have hinput_size : (blockInputWords air start).size = 16 := by
    simp [blockInputWords]
  have hexpand16 :=
    expandSchedule_word16_from_input (blockInputWords air start) hinput_size
  have hexpand16_trace :
      (expandSchedule (blockInputWords air start))[16]! =
        smallSigma1 (scheduleWordAtRow air (start + 3) 2) +
          scheduleWordAtRow air (start + 2) 1 +
          (scheduleWordAtRow air start 0 + smallSigma0 (scheduleWordAtRow air start 1)) := by
    simpa [blockInputWords, inputWord, add_assoc, add_left_comm, add_comm] using hexpand16
  rw [hexpand16_trace]
  exact hrec

private theorem expandSchedule_word20_from_input (input : Array Word)
    (hsize : input.size = 16) :
    (expandSchedule input)[20]! =
      smallSigma1 ((expandSchedule input)[18]!) + input[13]! +
        (input[4]! + smallSigma0 input[5]!) := by
  set step : Array Word → ℕ → Word :=
    fun acc offset =>
      smallSigma1 acc[offset + 14]! +
      acc[offset + 9]! +
      smallSigma0 acc[offset + 1]! +
      acc[offset]!
  set schedPrefix :=
    (List.range 4).foldl (fun acc off => acc.push (step acc off)) input
  have hprefix_size : schedPrefix.size = 20 := by
    rw [show schedPrefix =
      (List.range 4).foldl (fun acc off => acc.push (step acc off)) input by rfl]
    rw [foldl_push_size]
    simp [hsize, List.length_range]
  have hrange :
      List.range 64 =
        List.range (4 + 1) ++ (List.range (64 - (4 + 1))).map (4 + 1 + ·) := by
    have h64 : 64 = (4 + 1) + (64 - (4 + 1)) := by
      omega
    rw [h64]
    simpa [Nat.add_sub_cancel_left] using
      (List.range_add (n := 4 + 1) (m := 64 - (4 + 1)))
  have hprefix_succ :
      (List.range (4 + 1)).foldl (fun acc off => acc.push (step acc off)) input =
        schedPrefix.push (step schedPrefix 4) := by
    rw [show List.range (4 + 1) = List.range 4 ++ [4] by
      simpa using (List.range_succ (n := 4))]
    simp [schedPrefix]
  have hexpand20 :
      (expandSchedule input)[20]! = step schedPrefix 4 := by
    rw [expandSchedule_eq_foldl, hrange, List.foldl_append, hprefix_succ]
    rw [getElem!_foldl_push_preserved
      (l := (List.range (64 - (4 + 1))).map (4 + 1 + ·))
      (f := step)
      (xs := schedPrefix.push (step schedPrefix 4))
      (i := 20)]
    · simpa [hprefix_size] using
        (getElem!_push_size (xs := schedPrefix) (x := step schedPrefix 4))
    · simp [hprefix_size]
  have hprefix18 :
      (expandSchedule input)[18]! = schedPrefix[18]! := by
    rw [expandSchedule_eq_foldl, hrange, List.foldl_append, hprefix_succ]
    rw [getElem!_foldl_push_preserved
      (l := (List.range (64 - (4 + 1))).map (4 + 1 + ·))
      (f := step)
      (xs := schedPrefix.push (step schedPrefix 4))
      (i := 18)]
    · have hlt : 18 < schedPrefix.size := by
        simpa [hprefix_size]
      simpa using (getElem!_push_lt (xs := schedPrefix) (x := step schedPrefix 4) hlt)
    · simp [hprefix_size]
  have hpres13 :
      schedPrefix[13]! = input[13]! := by
    rw [show schedPrefix =
      (List.range 4).foldl (fun acc off => acc.push (step acc off)) input by rfl]
    exact getElem!_foldl_push_preserved (l := List.range 4) (f := step) (xs := input)
      (i := 13) (by simpa [hsize])
  have hpres4 :
      schedPrefix[4]! = input[4]! := by
    rw [show schedPrefix =
      (List.range 4).foldl (fun acc off => acc.push (step acc off)) input by rfl]
    exact getElem!_foldl_push_preserved (l := List.range 4) (f := step) (xs := input)
      (i := 4) (by simpa [hsize])
  have hpres5 :
      schedPrefix[5]! = input[5]! := by
    rw [show schedPrefix =
      (List.range 4).foldl (fun acc off => acc.push (step acc off)) input by rfl]
    exact getElem!_foldl_push_preserved (l := List.range 4) (f := step) (xs := input)
      (i := 5) (by simpa [hsize])
  calc
    (expandSchedule input)[20]! = step schedPrefix 4 := hexpand20
    _ = smallSigma1 (schedPrefix[18]!) + input[13]! + (input[4]! + smallSigma0 input[5]!) := by
      simp [step, hpres13, hpres4, hpres5, add_assoc, add_left_comm, add_comm]
    _ = smallSigma1 ((expandSchedule input)[18]!) + input[13]! + (input[4]! + smallSigma0 input[5]!) := by
      rw [← hprefix18]

/-- The next slot-`0` schedule consumer, `w[20]`, follows once the non-input
    dependency `w[18]` agrees with `TraceSpec.expandSchedule`. -/
theorem expandSchedule_word20_of_word18
    (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start)
    (hword18 :
      scheduleWordAtRow air (start + 4) 2 =
        (expandSchedule (blockInputWords air start))[18]!) :
    scheduleWordAtRow air (start + 5) 0 =
      (expandSchedule (blockInputWords air start))[20]! := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : start + 4 < Circuit.last_row air := by
    omega
  have hnext_row : nextRow air (start + 4) = start + 5 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrec :=
    next_msg_schedule_word0_recurrence air start (start + 4) hwindow hrot hshape hf hsc
      hsched_bits (by simpa [hnext_row]) (by simpa [hnext_row])
  rw [hnext_row] at hrec
  dsimp only at hrec
  have ht : ((start + 5 - start) * 4) = 20 := by
    omega
  rw [ht] at hrec
  norm_num at hrec
  have hinput_size : (blockInputWords air start).size = 16 := by
    simp [blockInputWords]
  have hexpand20 :=
    expandSchedule_word20_from_input (blockInputWords air start) hinput_size
  rw [← hword18] at hexpand20
  have hexpand20_trace :
      (expandSchedule (blockInputWords air start))[20]! =
        smallSigma1 (scheduleWordAtRow air (start + 4) 2) +
          scheduleWordAtRow air (start + 3) 1 +
          (scheduleWordAtRow air (start + 1) 0 + smallSigma0 (scheduleWordAtRow air (start + 1) 1)) := by
    simpa [blockInputWords, inputWord, add_assoc, add_left_comm, add_comm] using hexpand20
  rw [hexpand20_trace]
  exact hrec

/-! ## B7: Full `expandSchedule` induction -/

/-- Inductive step: for `16 ≤ t < 80`, if all previous schedule words already
    match `TraceSpec.expandSchedule`, then the slot-parametric SHA-512
    recurrence transports the next trace word onto `expandSchedule[t]`. -/
theorem expandSchedule_step (air : C FBB ExtF) (start : ℕ) (t : ℕ)
    (ht_lo : 16 ≤ t) (ht_hi : t < 80)
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
  have hoffset : offset < 64 := by
    dsimp [offset]
    omega
  have hprefix_size : schedPrefix.size = t := by
    rw [show schedPrefix =
      (List.range offset).foldl (fun acc off => acc.push (step acc off)) input by rfl]
    rw [foldl_push_size]
    simp [input, blockInputWords, List.length_range]
    dsimp [offset]
    omega
  have hrange :
      List.range 64 =
        List.range (offset + 1) ++ (List.range (64 - (offset + 1))).map (offset + 1 + ·) := by
    have h64 : 64 = (offset + 1) + (64 - (offset + 1)) := by
      omega
    rw [h64]
    simpa [Nat.add_sub_cancel_left] using
      (List.range_add (n := offset + 1) (m := 64 - (offset + 1)))
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
      (l := (List.range (64 - (offset + 1))).map (offset + 1 + ·))
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
        (l := (List.range (64 - (offset + 1))).map (offset + 1 + ·))
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
    have hsupp : start + 20 ≤ Circuit.last_row air := by
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
  have hnext_bound : nextRow air row ≤ start + 19 := by
    rw [hrow_next]
    omega
  have hrec :=
    next_msg_schedule_recurrence air start row (t % 4) (by omega) hwindow hrot hshape hf hsc
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
          ((expandSchedule input)[t - 16]! +
            smallSigma0 ((expandSchedule input)[t - 15]!)) := by
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
    simp [add_assoc, add_left_comm, add_comm]
  simpa [input, add_assoc, add_left_comm, add_comm] using
    (calc
      scheduleWordAtRow air (start + t / 4) (t % 4) =
          smallSigma1 ((expandSchedule input)[t - 2]!) +
            (expandSchedule input)[t - 7]! +
            ((expandSchedule input)[t - 16]! +
              smallSigma0 ((expandSchedule input)[t - 15]!)) := hrec
      _ = step schedPrefix offset := hstep_eq.symm
      _ = (expandSchedule input)[t]! := hexpand_t.symm)

/-- Full SHA-512 schedule correctness by strong induction on `t`. -/
theorem expandSchedule_matches_trace (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hf : ∀ r, flag_constraints air r)
    (hsc : ∀ r, schedule_constraints air r)
    (hsched_bits : scheduleBitsBooleanOnBlock air start) :
    ∀ t, t < 80 →
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

end Sha2BlockHasherVmAir_sha512.BlockSpec
