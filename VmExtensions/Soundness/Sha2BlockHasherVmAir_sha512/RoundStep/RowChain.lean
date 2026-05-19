/- 
  Layer C: Round Step (Per-Row Chain)

  Covers the iteration of 4 rounds per row and the full compression trace.

  Depends on: StateBridge, MessageSchedule.Correctness
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Block.Window
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.MessageSchedule.Correctness
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.RoundStep.ConstraintBridge
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.RoundStep.StateBridge

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## C4: Four rounds per row -> carried state update

One round row processes 4 consecutive SHA-512 rounds (slots 0-3).

Key insight: the shift-register structure means:
- slot 0's input state = carriedState air row
- slot i's input state = slotInputState air row i (which mixes local/next)
- After all 4 slots, the carried state at the wrap-aware successor row matches
  the result of 4 roundStep applications.

The proof chains single_round_a_correct/single_round_e_correct for each slot. -/

/-- Slot 0's input state equals the carried state from the local row.
    This is because slot 0 reads all inputs from the local row (slot+3 = 3 < 4). -/
theorem slot0_input_eq_carried (air : C FBB ExtF) (row : ℕ) :
    slotInputState air row 0 = carriedState air row := by
  rfl

/-- After slot 0, the result feeds into slot 1's input. Specifically,
    slotInputState air row 1 matches the state after one roundStep
    (shifted so that b = old_a, c = old_b, etc.), reading the new
    a[0]@next and e[0]@next from the constraint outputs. -/
theorem slot1_input_after_slot0 (air : C FBB ExtF) (row : ℕ)
    (state0 : WorkingVars)
    (ha0 : aWord air (nextRow air row) 0 = state0.a)
    (he0 : eWord air (nextRow air row) 0 = state0.e) :
    slotInputState air row 1 =
      { a := state0.a
        b := aWord air row 3
        c := aWord air row 2
        d := aWord air row 1
        e := state0.e
        f := eWord air row 3
        g := eWord air row 2
        h := eWord air row 1 } := by
  cases state0
  simp [slotInputState, concatAWord, concatEWord, ha0, he0]

/-- After slots 0-1, slot 2's input reads a[0]@next and a[1]@next. -/
theorem slot2_input_after_slots01 (air : C FBB ExtF) (row : ℕ) :
    slotInputState air row 2 =
      { a := aWord air (nextRow air row) 1
        b := aWord air (nextRow air row) 0
        c := aWord air row 3
        d := aWord air row 2
        e := eWord air (nextRow air row) 1
        f := eWord air (nextRow air row) 0
        g := eWord air row 3
        h := eWord air row 2 } := by
  rfl

/-- After slots 0-2, slot 3's input reads a[0..2]@next. -/
theorem slot3_input_after_slots012 (air : C FBB ExtF) (row : ℕ) :
    slotInputState air row 3 =
      { a := aWord air (nextRow air row) 2
        b := aWord air (nextRow air row) 1
        c := aWord air (nextRow air row) 0
        d := aWord air row 3
        e := eWord air (nextRow air row) 2
        f := eWord air (nextRow air row) 1
        g := eWord air (nextRow air row) 0
        h := eWord air row 3 } := by
  rfl

/-- The carried state exported by a round row is exactly that row's 4 slot outputs,
    ordered as `(a3,a2,a1,a0,e3,e2,e1,e0)`. -/
theorem carriedState_from_slot_outputs (air : C FBB ExtF) (row : ℕ) :
    carriedState air row =
      { a := aWord air row 3
        b := aWord air row 2
        c := aWord air row 1
        d := aWord air row 0
        e := eWord air row 3
        f := eWord air row 2
        g := eWord air row 1
        h := eWord air row 0 } := by
  rfl

private theorem schedule_constraints_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    schedule_constraints air row :=
  Sha2BlockHasherVmAir_sha512.constraints.schedule_constraints_of_blockHasherConstraints air hc row

private theorem workvar_bits_of_blockHasherConstraints
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ) :
    allWorkVarBitsBoolean air row :=
  allWorkVarBitsBoolean_of_constraints air row
    (workvar_bit_boolean_constraints_of_blockHasherConstraints air hc row)

private theorem round_step_constraints_from_bridge
    (air : C FBB ExtF) (hc : blockHasherConstraints air) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row)) :
    round_step_constraints air row := by
  simpa using
    Sha2BlockHasherVmAir_sha512.BlockSpec.round_step_constraints_of_blockHasherConstraints
      air hc row hrow hrot hbb hbb_next

private theorem blockStateRow_le_last
    (air : C FBB ExtF) (start offset : ℕ)
    (hwindow : blockWindowSupported air start)
    (hoffset : offset < 20) :
    blockStateRow air start offset ≤ Circuit.last_row air := by
  by_cases hstart : start = 0
  · subst hstart
    cases offset with
    | zero =>
        simp [blockStateRow]
    | succ k =>
        have hlast : 20 ≤ Circuit.last_row air := by
          simpa [blockWindowSupported] using hwindow
        simp [blockStateRow]
        omega
  · cases offset with
    | zero =>
        have hlast : start + 20 ≤ Circuit.last_row air := by
          simpa [blockWindowSupported] using hwindow
        simp [blockStateRow, hstart]
        omega
    | succ k =>
        have hlast : start + (k + 1) ≤ Circuit.last_row air := by
          have hsupp : start + 20 ≤ Circuit.last_row air := by
            simpa [blockWindowSupported] using hwindow
          omega
        simp [blockStateRow, hstart]
        omega

private theorem next_blockStateRow_eq
    (air : C FBB ExtF) (start offset : ℕ)
    (hwindow : blockWindowSupported air start)
    (hoffset : offset < 20) :
    nextRow air (blockStateRow air start offset) = start + offset := by
  by_cases hstart : start = 0
  · subst hstart
    cases offset with
    | zero =>
        simp [blockStateRow, nextRow]
    | succ k =>
        have hlast : 20 ≤ Circuit.last_row air := by
          simpa [blockWindowSupported] using hwindow
        have hk : k < Circuit.last_row air := by
          omega
        simp [blockStateRow, nextRow, hk.ne]
  · cases offset with
    | zero =>
        have hlast : start + 20 ≤ Circuit.last_row air := by
          simpa [blockWindowSupported] using hwindow
        have hprev : start - 1 < Circuit.last_row air := by
          omega
        have hstart_pos : 0 < start := Nat.pos_of_ne_zero hstart
        rw [show start = start - 1 + 1 by omega]
        simp [blockStateRow, nextRow, hprev.ne]
    | succ k =>
        have hcurr : start + k < Circuit.last_row air := by
          have hlast : start + (k + 1) ≤ Circuit.last_row air := by
            have hsupp : start + 20 ≤ Circuit.last_row air := by
              simpa [blockWindowSupported] using hwindow
            omega
          omega
        simp [blockStateRow, nextRow, hstart, hcurr.ne, Nat.add_assoc]

private theorem scheduleBitsBooleanOnBlock_of_constraints
    (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air) :
    scheduleBitsBooleanOnBlock air start := by
  intro offset slot hoffset hslot bit
  let srcRow := blockStateRow air start offset
  have hnextlocal : nextRow air srcRow = start + offset := by
    simpa [srcRow] using next_blockStateRow_eq air start offset hwindow hoffset
  have hlocal_le : srcRow ≤ Circuit.last_row air := by
    simpa [srcRow] using blockStateRow_le_last air start offset hwindow hoffset
  have hshape_row := hshape.2.1 offset hoffset
  have hround_next : next_is_round_row air srcRow = 1 := by
    rw [next_is_round_row_eq_nextRow air hrot srcRow hlocal_le, hnextlocal]
    exact hshape_row.2.1
  have hs :=
    schedule_bits_boolean air srcRow hlocal_le hrot
      (schedule_constraints_of_blockHasherConstraints air hc srcRow) hround_next
  simpa [scheduleBitsWord, hnextlocal] using hs slot bit hslot bit.isLt

/-- The schedule bits on a full SHA-512 block window are derivable from the
standard block-start assumptions, so callers do not need to provide them as
an extra theorem input. -/
theorem scheduleBitsBooleanOnBlock_of_start
    (air : C FBB ExtF) (start : ℕ)
    (hstart : start ≤ Circuit.last_row air)
    (hsel : encoder_selector_idx air start = 0)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    scheduleBitsBooleanOnBlock air start := by
  have hwindow := blockWindowSupported_of_start_le air start hstart hsel hrot hc
  have hshape := blockWindowHasShape_of_constraints air start hwindow hsel hrot hc
  exact scheduleBitsBooleanOnBlock_of_constraints air start hwindow hrot hshape hc

/-- After slot 0: the new a[0] and e[0] match the first roundStep.
    Uses single_round_a_correct/single_round_e_correct for slot 0
    plus slot0_input_eq_carried. -/
theorem slot0_result (air : C FBB ExtF) (start offset : ℕ)
    (hoffset : offset < 20)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (hcarry : roundCarryBoundsAt air (start + offset))
    (prevState : WorkingVars)
    (hprev : carriedState air (blockStateRow air start offset) = prevState) :
    let row := start + offset
    let baseRound := offset * 4
    let schedule := expandSchedule (blockInputWords air start)
    let s1 := roundStep prevState (sha512K[baseRound]!) (schedule[baseRound]!)
    aWord air row 0 = s1.a ∧ eWord air row 0 = s1.e := by
  dsimp
  let srcRow := blockStateRow air start offset
  have hnextlocal : nextRow air srcRow = start + offset := by
    simpa [srcRow] using next_blockStateRow_eq air start offset hwindow hoffset
  have hlocal_le : srcRow ≤ Circuit.last_row air := by
    simpa [srcRow] using blockStateRow_le_last air start offset hwindow hoffset
  have hshape_row := hshape.2.1 offset hoffset
  have hround_next : next_is_round_row air srcRow = 1 := by
    rw [next_is_round_row_eq_nextRow air hrot srcRow hlocal_le, hnextlocal]
    exact hshape_row.2.1
  have hidx :
      encoder_selector_idx air (nextRow air srcRow) = (offset : FBB) := by
    simpa [hnextlocal] using hshape_row.1
  have hbb_local := workvar_bits_of_blockHasherConstraints air hc srcRow
  have hbb_next : allWorkVarBitsBoolean air (nextRow air srcRow) := by
    simpa [hnextlocal] using workvar_bits_of_blockHasherConstraints air hc (start + offset)
  have hrs_local :=
    round_step_constraints_from_bridge air hc srcRow
      hlocal_le hrot hbb_local hbb_next
  have hcarry_next : roundCarryBoundsAt air (nextRow air srcRow) := by
    simpa [hnextlocal] using hcarry
  have hflags_next : flag_constraints air (nextRow air srcRow) := by
    simpa [hnextlocal] using (hc (start + offset)).1
  have hsched_bits :
      isBitsWord (scheduleBitsWord air (nextRow air srcRow) 0) := by
    have hs :=
      schedule_bits_boolean air srcRow hlocal_le hrot
        (schedule_constraints_of_blockHasherConstraints air hc srcRow) hround_next
    intro bit
    exact hs 0 bit (by omega) bit.isLt
  have hsched_trace :
      scheduleWordAtRow air (nextRow air srcRow) 0 =
        (expandSchedule (blockInputWords air start))[offset * 4]! := by
    simpa [hnextlocal] using
      expandSchedule_matches_trace air start hwindow hrot hshape
        (fun r => (hc r).1)
        (schedule_constraints_of_blockHasherConstraints air hc)
        (scheduleBitsBooleanOnBlock_of_constraints air start hwindow hrot hshape hc)
        (offset * 4) (by omega)
  have ha :=
    single_round_a_correct air srcRow 0 (by omega) hlocal_le hrot hrs_local hbb_local hbb_next
      hround_next hflags_next offset hidx hoffset hcarry_next hsched_bits
  have he :=
    single_round_e_correct air srcRow 0 (by omega) hlocal_le hrot hrs_local hbb_local hbb_next
      hround_next hflags_next offset hidx hoffset hcarry_next hsched_bits
  have hinput : slotInputState air srcRow 0 = prevState :=
    (slot0_input_eq_carried air srcRow).trans hprev
  constructor
  · calc
      aWord air (start + offset) 0 = aWord air (nextRow air srcRow) 0 := by
        simp [hnextlocal]
      _ = (roundStep (slotInputState air srcRow 0)
            (sha512K[offset * 4]!) (scheduleWordAtRow air (nextRow air srcRow) 0)).a := by
            simpa using ha
      _ = (roundStep prevState (sha512K[offset * 4]!)
            ((expandSchedule (blockInputWords air start))[offset * 4]!)).a := by
            rw [hinput, hsched_trace]
  · calc
      eWord air (start + offset) 0 = eWord air (nextRow air srcRow) 0 := by
        simp [hnextlocal]
      _ = (roundStep (slotInputState air srcRow 0)
            (sha512K[offset * 4]!) (scheduleWordAtRow air (nextRow air srcRow) 0)).e := by
            simpa using he
      _ = (roundStep prevState (sha512K[offset * 4]!)
            ((expandSchedule (blockInputWords air start))[offset * 4]!)).e := by
            rw [hinput, hsched_trace]

/-- After slot 1: the new a[1] and e[1] match the second roundStep.
    Uses slot1_input_after_slot0 to establish the input state for slot 1. -/
theorem slot1_result (air : C FBB ExtF) (start offset : ℕ)
    (hoffset : offset < 20)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (hcarry : roundCarryBoundsAt air (start + offset))
    (prevState : WorkingVars)
    (hprev : carriedState air (blockStateRow air start offset) = prevState) :
    let row := start + offset
    let baseRound := offset * 4
    let schedule := expandSchedule (blockInputWords air start)
    let s1 := roundStep prevState (sha512K[baseRound]!) (schedule[baseRound]!)
    let s2 := roundStep s1 (sha512K[baseRound + 1]!) (schedule[baseRound + 1]!)
    aWord air row 1 = s2.a ∧ eWord air row 1 = s2.e := by
  dsimp
  let srcRow := blockStateRow air start offset
  let schedule := expandSchedule (blockInputWords air start)
  let s1 := roundStep prevState (sha512K[offset * 4]!) (schedule[offset * 4]!)
  let s2 := roundStep s1 (sha512K[offset * 4 + 1]!) (schedule[offset * 4 + 1]!)
  have hnextlocal : nextRow air srcRow = start + offset := by
    simpa [srcRow] using next_blockStateRow_eq air start offset hwindow hoffset
  have hlocal_le : srcRow ≤ Circuit.last_row air := by
    simpa [srcRow] using blockStateRow_le_last air start offset hwindow hoffset
  have hshape_row := hshape.2.1 offset hoffset
  have hround_next : next_is_round_row air srcRow = 1 := by
    rw [next_is_round_row_eq_nextRow air hrot srcRow hlocal_le, hnextlocal]
    exact hshape_row.2.1
  have hidx :
      encoder_selector_idx air (nextRow air srcRow) = (offset : FBB) := by
    simpa [hnextlocal] using hshape_row.1
  have hbb_local := workvar_bits_of_blockHasherConstraints air hc srcRow
  have hbb_next : allWorkVarBitsBoolean air (nextRow air srcRow) := by
    simpa [hnextlocal] using workvar_bits_of_blockHasherConstraints air hc (start + offset)
  have hrs_local :=
    round_step_constraints_from_bridge air hc srcRow
      hlocal_le hrot hbb_local hbb_next
  have hcarry_next : roundCarryBoundsAt air (nextRow air srcRow) := by
    simpa [hnextlocal] using hcarry
  have hflags_next : flag_constraints air (nextRow air srcRow) := by
    simpa [hnextlocal] using (hc (start + offset)).1
  have hsched_bits :
      isBitsWord (scheduleBitsWord air (nextRow air srcRow) 1) := by
    have hs :=
      schedule_bits_boolean air srcRow hlocal_le hrot
        (schedule_constraints_of_blockHasherConstraints air hc srcRow) hround_next
    intro bit
    exact hs 1 bit (by omega) bit.isLt
  have hsched_trace0 :=
    expandSchedule_matches_trace air start hwindow hrot hshape
      (fun r => (hc r).1)
      (schedule_constraints_of_blockHasherConstraints air hc)
      (scheduleBitsBooleanOnBlock_of_constraints air start hwindow hrot hshape hc)
      (offset * 4 + 1) (by omega)
  have hdiv : (offset * 4 + 1) / 4 = offset := by omega
  have hmod : (offset * 4 + 1) % 4 = 1 := by omega
  have hsched_trace :
      scheduleWordAtRow air (nextRow air srcRow) 1 =
        schedule[offset * 4 + 1]! := by
    simpa [schedule, hnextlocal, hdiv, hmod] using hsched_trace0
  have h0 :=
    slot0_result air start offset hoffset hwindow hrot hshape hc hcarry prevState hprev
  rcases h0 with ⟨ha0, he0⟩
  have hprev_fields := hprev
  rw [carriedState_from_slot_outputs, WorkingVars.mk.injEq] at hprev_fields
  rcases hprev_fields with
    ⟨ha3_prev, ha2_prev, ha1_prev, _, he3_prev, he2_prev, he1_prev, _⟩
  have hinput :
      slotInputState air srcRow 1 = s1 := by
    calc
      slotInputState air srcRow 1 =
          { a := s1.a
            b := aWord air srcRow 3
            c := aWord air srcRow 2
            d := aWord air srcRow 1
            e := s1.e
            f := eWord air srcRow 3
            g := eWord air srcRow 2
            h := eWord air srcRow 1 } := by
              refine slot1_input_after_slot0 air srcRow s1 ?_ ?_
              · simpa [s1, hnextlocal] using ha0
              · simpa [s1, hnextlocal] using he0
      _ = { a := s1.a
            b := prevState.a
            c := prevState.b
            d := prevState.c
            e := s1.e
            f := prevState.e
            g := prevState.f
            h := prevState.g } := by
          rw [WorkingVars.mk.injEq]
          exact ⟨rfl, ha3_prev, ha2_prev, ha1_prev, rfl, he3_prev, he2_prev, he1_prev⟩
      _ = s1 := by
          cases prevState
          simp [schedule, s1, roundStep]
  have ha :=
    single_round_a_correct air srcRow 1 (by omega) hlocal_le hrot hrs_local hbb_local hbb_next
      hround_next hflags_next offset hidx hoffset hcarry_next hsched_bits
  have he :=
    single_round_e_correct air srcRow 1 (by omega) hlocal_le hrot hrs_local hbb_local hbb_next
      hround_next hflags_next offset hidx hoffset hcarry_next hsched_bits
  constructor
  · calc
      aWord air (start + offset) 1 = aWord air (nextRow air srcRow) 1 := by
        simp [hnextlocal]
      _ = (roundStep (slotInputState air srcRow 1)
            (sha512K[offset * 4 + 1]!) (scheduleWordAtRow air (nextRow air srcRow) 1)).a := by
            simpa using ha
      _ = s2.a := by
            rw [hinput, hsched_trace]
  · calc
      eWord air (start + offset) 1 = eWord air (nextRow air srcRow) 1 := by
        simp [hnextlocal]
      _ = (roundStep (slotInputState air srcRow 1)
            (sha512K[offset * 4 + 1]!) (scheduleWordAtRow air (nextRow air srcRow) 1)).e := by
            simpa using he
      _ = s2.e := by
            rw [hinput, hsched_trace]

/-- After slot 2: the new a[2] and e[2] match the third roundStep. -/
theorem slot2_result (air : C FBB ExtF) (start offset : ℕ)
    (hoffset : offset < 20)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (hcarry : roundCarryBoundsAt air (start + offset))
    (prevState : WorkingVars)
    (hprev : carriedState air (blockStateRow air start offset) = prevState) :
    let row := start + offset
    let baseRound := offset * 4
    let schedule := expandSchedule (blockInputWords air start)
    let s1 := roundStep prevState (sha512K[baseRound]!) (schedule[baseRound]!)
    let s2 := roundStep s1 (sha512K[baseRound + 1]!) (schedule[baseRound + 1]!)
    let s3 := roundStep s2 (sha512K[baseRound + 2]!) (schedule[baseRound + 2]!)
    aWord air row 2 = s3.a ∧ eWord air row 2 = s3.e := by
  dsimp
  let srcRow := blockStateRow air start offset
  let schedule := expandSchedule (blockInputWords air start)
  let s1 := roundStep prevState (sha512K[offset * 4]!) (schedule[offset * 4]!)
  let s2 := roundStep s1 (sha512K[offset * 4 + 1]!) (schedule[offset * 4 + 1]!)
  let s3 := roundStep s2 (sha512K[offset * 4 + 2]!) (schedule[offset * 4 + 2]!)
  have hnextlocal : nextRow air srcRow = start + offset := by
    simpa [srcRow] using next_blockStateRow_eq air start offset hwindow hoffset
  have hlocal_le : srcRow ≤ Circuit.last_row air := by
    simpa [srcRow] using blockStateRow_le_last air start offset hwindow hoffset
  have hshape_row := hshape.2.1 offset hoffset
  have hround_next : next_is_round_row air srcRow = 1 := by
    rw [next_is_round_row_eq_nextRow air hrot srcRow hlocal_le, hnextlocal]
    exact hshape_row.2.1
  have hidx :
      encoder_selector_idx air (nextRow air srcRow) = (offset : FBB) := by
    simpa [hnextlocal] using hshape_row.1
  have hbb_local := workvar_bits_of_blockHasherConstraints air hc srcRow
  have hbb_next : allWorkVarBitsBoolean air (nextRow air srcRow) := by
    simpa [hnextlocal] using workvar_bits_of_blockHasherConstraints air hc (start + offset)
  have hrs_local :=
    round_step_constraints_from_bridge air hc srcRow
      hlocal_le hrot hbb_local hbb_next
  have hcarry_next : roundCarryBoundsAt air (nextRow air srcRow) := by
    simpa [hnextlocal] using hcarry
  have hflags_next : flag_constraints air (nextRow air srcRow) := by
    simpa [hnextlocal] using (hc (start + offset)).1
  have hsched_bits :
      isBitsWord (scheduleBitsWord air (nextRow air srcRow) 2) := by
    have hs :=
      schedule_bits_boolean air srcRow hlocal_le hrot
        (schedule_constraints_of_blockHasherConstraints air hc srcRow) hround_next
    intro bit
    exact hs 2 bit (by omega) bit.isLt
  have hsched_trace0 :=
    expandSchedule_matches_trace air start hwindow hrot hshape
      (fun r => (hc r).1)
      (schedule_constraints_of_blockHasherConstraints air hc)
      (scheduleBitsBooleanOnBlock_of_constraints air start hwindow hrot hshape hc)
      (offset * 4 + 2) (by omega)
  have hdiv : (offset * 4 + 2) / 4 = offset := by omega
  have hmod : (offset * 4 + 2) % 4 = 2 := by omega
  have hsched_trace :
      scheduleWordAtRow air (nextRow air srcRow) 2 =
        schedule[offset * 4 + 2]! := by
    simpa [schedule, hnextlocal, hdiv, hmod] using hsched_trace0
  have h0 :=
    slot0_result air start offset hoffset hwindow hrot hshape hc hcarry prevState hprev
  have h1 :=
    slot1_result air start offset hoffset hwindow hrot hshape hc hcarry prevState hprev
  rcases h0 with ⟨ha0, he0⟩
  rcases h1 with ⟨ha1, he1⟩
  have hprev_fields := hprev
  rw [carriedState_from_slot_outputs, WorkingVars.mk.injEq] at hprev_fields
  rcases hprev_fields with
    ⟨ha3_prev, ha2_prev, _, _, he3_prev, he2_prev, _, _⟩
  have hinput :
      slotInputState air srcRow 2 = s2 := by
    calc
      slotInputState air srcRow 2 =
          { a := aWord air (nextRow air srcRow) 1
            b := aWord air (nextRow air srcRow) 0
            c := aWord air srcRow 3
            d := aWord air srcRow 2
            e := eWord air (nextRow air srcRow) 1
            f := eWord air (nextRow air srcRow) 0
            g := eWord air srcRow 3
            h := eWord air srcRow 2 } := slot2_input_after_slots01 air srcRow
      _ = { a := s2.a
            b := s1.a
            c := prevState.a
            d := prevState.b
            e := s2.e
            f := s1.e
            g := prevState.e
            h := prevState.f } := by
              rw [WorkingVars.mk.injEq]
              exact ⟨by simpa [hnextlocal, schedule, s1, s2] using ha1,
                by simpa [hnextlocal, schedule, s1] using ha0,
                ha3_prev, ha2_prev,
                by simpa [hnextlocal, schedule, s1, s2] using he1,
                by simpa [hnextlocal, schedule, s1] using he0,
                he3_prev, he2_prev⟩
      _ = s2 := by
          cases prevState
          simp [schedule, s1, s2, roundStep]
  have ha :=
    single_round_a_correct air srcRow 2 (by omega) hlocal_le hrot hrs_local hbb_local hbb_next
      hround_next hflags_next offset hidx hoffset hcarry_next hsched_bits
  have he :=
    single_round_e_correct air srcRow 2 (by omega) hlocal_le hrot hrs_local hbb_local hbb_next
      hround_next hflags_next offset hidx hoffset hcarry_next hsched_bits
  constructor
  · calc
      aWord air (start + offset) 2 = aWord air (nextRow air srcRow) 2 := by
        simp [hnextlocal]
      _ = (roundStep (slotInputState air srcRow 2)
            (sha512K[offset * 4 + 2]!) (scheduleWordAtRow air (nextRow air srcRow) 2)).a := by
            simpa using ha
      _ = s3.a := by
            rw [hinput, hsched_trace]
  · calc
      eWord air (start + offset) 2 = eWord air (nextRow air srcRow) 2 := by
        simp [hnextlocal]
      _ = (roundStep (slotInputState air srcRow 2)
            (sha512K[offset * 4 + 2]!) (scheduleWordAtRow air (nextRow air srcRow) 2)).e := by
            simpa using he
      _ = s3.e := by
            rw [hinput, hsched_trace]

/-- After slot 3: the new a[3] and e[3] match the fourth roundStep. -/
theorem slot3_result (air : C FBB ExtF) (start offset : ℕ)
    (hoffset : offset < 20)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (hcarry : roundCarryBoundsAt air (start + offset))
    (prevState : WorkingVars)
    (hprev : carriedState air (blockStateRow air start offset) = prevState) :
    let row := start + offset
    let baseRound := offset * 4
    let schedule := expandSchedule (blockInputWords air start)
    let s1 := roundStep prevState (sha512K[baseRound]!) (schedule[baseRound]!)
    let s2 := roundStep s1 (sha512K[baseRound + 1]!) (schedule[baseRound + 1]!)
    let s3 := roundStep s2 (sha512K[baseRound + 2]!) (schedule[baseRound + 2]!)
    let s4 := roundStep s3 (sha512K[baseRound + 3]!) (schedule[baseRound + 3]!)
    aWord air row 3 = s4.a ∧ eWord air row 3 = s4.e := by
  dsimp
  let srcRow := blockStateRow air start offset
  let schedule := expandSchedule (blockInputWords air start)
  let s1 := roundStep prevState (sha512K[offset * 4]!) (schedule[offset * 4]!)
  let s2 := roundStep s1 (sha512K[offset * 4 + 1]!) (schedule[offset * 4 + 1]!)
  let s3 := roundStep s2 (sha512K[offset * 4 + 2]!) (schedule[offset * 4 + 2]!)
  let s4 := roundStep s3 (sha512K[offset * 4 + 3]!) (schedule[offset * 4 + 3]!)
  have hnextlocal : nextRow air srcRow = start + offset := by
    simpa [srcRow] using next_blockStateRow_eq air start offset hwindow hoffset
  have hlocal_le : srcRow ≤ Circuit.last_row air := by
    simpa [srcRow] using blockStateRow_le_last air start offset hwindow hoffset
  have hshape_row := hshape.2.1 offset hoffset
  have hround_next : next_is_round_row air srcRow = 1 := by
    rw [next_is_round_row_eq_nextRow air hrot srcRow hlocal_le, hnextlocal]
    exact hshape_row.2.1
  have hidx :
      encoder_selector_idx air (nextRow air srcRow) = (offset : FBB) := by
    simpa [hnextlocal] using hshape_row.1
  have hbb_local := workvar_bits_of_blockHasherConstraints air hc srcRow
  have hbb_next : allWorkVarBitsBoolean air (nextRow air srcRow) := by
    simpa [hnextlocal] using workvar_bits_of_blockHasherConstraints air hc (start + offset)
  have hrs_local :=
    round_step_constraints_from_bridge air hc srcRow
      hlocal_le hrot hbb_local hbb_next
  have hcarry_next : roundCarryBoundsAt air (nextRow air srcRow) := by
    simpa [hnextlocal] using hcarry
  have hflags_next : flag_constraints air (nextRow air srcRow) := by
    simpa [hnextlocal] using (hc (start + offset)).1
  have hsched_bits :
      isBitsWord (scheduleBitsWord air (nextRow air srcRow) 3) := by
    have hs :=
      schedule_bits_boolean air srcRow hlocal_le hrot
        (schedule_constraints_of_blockHasherConstraints air hc srcRow) hround_next
    intro bit
    exact hs 3 bit (by omega) bit.isLt
  have hsched_trace0 :=
    expandSchedule_matches_trace air start hwindow hrot hshape
      (fun r => (hc r).1)
      (schedule_constraints_of_blockHasherConstraints air hc)
      (scheduleBitsBooleanOnBlock_of_constraints air start hwindow hrot hshape hc)
      (offset * 4 + 3) (by omega)
  have hdiv : (offset * 4 + 3) / 4 = offset := by omega
  have hmod : (offset * 4 + 3) % 4 = 3 := by omega
  have hsched_trace :
      scheduleWordAtRow air (nextRow air srcRow) 3 =
        schedule[offset * 4 + 3]! := by
    simpa [schedule, hnextlocal, hdiv, hmod] using hsched_trace0
  have h0 :=
    slot0_result air start offset hoffset hwindow hrot hshape hc hcarry prevState hprev
  have h1 :=
    slot1_result air start offset hoffset hwindow hrot hshape hc hcarry prevState hprev
  have h2 :=
    slot2_result air start offset hoffset hwindow hrot hshape hc hcarry prevState hprev
  rcases h0 with ⟨ha0, he0⟩
  rcases h1 with ⟨ha1, he1⟩
  rcases h2 with ⟨ha2, he2⟩
  have hprev_fields := hprev
  rw [carriedState_from_slot_outputs, WorkingVars.mk.injEq] at hprev_fields
  rcases hprev_fields with
    ⟨ha3_prev, _, _, _, he3_prev, _, _, _⟩
  have hinput :
      slotInputState air srcRow 3 = s3 := by
    calc
      slotInputState air srcRow 3 =
          { a := aWord air (nextRow air srcRow) 2
            b := aWord air (nextRow air srcRow) 1
            c := aWord air (nextRow air srcRow) 0
            d := aWord air srcRow 3
            e := eWord air (nextRow air srcRow) 2
            f := eWord air (nextRow air srcRow) 1
            g := eWord air (nextRow air srcRow) 0
            h := eWord air srcRow 3 } := slot3_input_after_slots012 air srcRow
      _ = { a := s3.a
            b := s2.a
            c := s1.a
            d := prevState.a
            e := s3.e
            f := s2.e
            g := s1.e
            h := prevState.e } := by
              rw [WorkingVars.mk.injEq]
              exact ⟨by simpa [hnextlocal, schedule, s1, s2, s3] using ha2,
                by simpa [hnextlocal, schedule, s1, s2] using ha1,
                by simpa [hnextlocal, schedule, s1] using ha0,
                ha3_prev,
                by simpa [hnextlocal, schedule, s1, s2, s3] using he2,
                by simpa [hnextlocal, schedule, s1, s2] using he1,
                by simpa [hnextlocal, schedule, s1] using he0,
                he3_prev⟩
      _ = s3 := by
          cases prevState
          simp [schedule, s1, s2, s3, roundStep]
  have ha :=
    single_round_a_correct air srcRow 3 (by omega) hlocal_le hrot hrs_local hbb_local hbb_next
      hround_next hflags_next offset hidx hoffset hcarry_next hsched_bits
  have he :=
    single_round_e_correct air srcRow 3 (by omega) hlocal_le hrot hrs_local hbb_local hbb_next
      hround_next hflags_next offset hidx hoffset hcarry_next hsched_bits
  constructor
  · calc
      aWord air (start + offset) 3 = aWord air (nextRow air srcRow) 3 := by
        simp [hnextlocal]
      _ = (roundStep (slotInputState air srcRow 3)
            (sha512K[offset * 4 + 3]!) (scheduleWordAtRow air (nextRow air srcRow) 3)).a := by
            simpa using ha
      _ = s4.a := by
            rw [hinput, hsched_trace]
  · calc
      eWord air (start + offset) 3 = eWord air (nextRow air srcRow) 3 := by
        simp [hnextlocal]
      _ = (roundStep (slotInputState air srcRow 3)
            (sha512K[offset * 4 + 3]!) (scheduleWordAtRow air (nextRow air srcRow) 3)).e := by
            simpa using he
      _ = s4.e := by
            rw [hinput, hsched_trace]

/-- Processing all 4 slots produces 4 consecutive roundStep applications.
    Assembly: slot0_result through slot3_result + carriedState_from_slot_outputs
    + roundStep shift-register structure (new_b = old_a, etc.). -/
theorem four_rounds_per_row (air : C FBB ExtF) (start offset : ℕ)
    (hoffset : offset < 20)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (hcarry : roundCarryBoundsAt air (start + offset))
    (prevState : WorkingVars)
    (hprev : carriedState air (blockStateRow air start offset) = prevState) :
    let row := start + offset
    let baseRound := offset * 4
    let schedule := expandSchedule (blockInputWords air start)
    let s1 := roundStep prevState (sha512K[baseRound]!) (schedule[baseRound]!)
    let s2 := roundStep s1 (sha512K[baseRound + 1]!) (schedule[baseRound + 1]!)
    let s3 := roundStep s2 (sha512K[baseRound + 2]!) (schedule[baseRound + 2]!)
    let s4 := roundStep s3 (sha512K[baseRound + 3]!) (schedule[baseRound + 3]!)
    carriedState air row = s4 := by
  dsimp
  have h0 :=
    slot0_result air start offset hoffset hwindow hrot hshape hc hcarry prevState hprev
  have h1 :=
    slot1_result air start offset hoffset hwindow hrot hshape hc hcarry prevState hprev
  have h2 :=
    slot2_result air start offset hoffset hwindow hrot hshape hc hcarry prevState hprev
  have h3 :=
    slot3_result air start offset hoffset hwindow hrot hshape hc hcarry prevState hprev
  rcases h0 with ⟨ha0, he0⟩
  rcases h1 with ⟨ha1, he1⟩
  rcases h2 with ⟨ha2, he2⟩
  rcases h3 with ⟨ha3, he3⟩
  rw [carriedState_from_slot_outputs, WorkingVars.mk.injEq]
  exact ⟨by simpa [roundStep] using ha3,
    by simpa [roundStep] using ha2,
    by simpa [roundStep] using ha1,
    by simpa [roundStep] using ha0,
    by simpa [roundStep] using he3,
    by simpa [roundStep] using he2,
    by simpa [roundStep] using he1,
    by simpa [roundStep] using he0⟩

/-! ## Compression trace (formerly CompressionTrace) -/

private def compressionPrefixStep (schedule : Array Word)
    (acc : WorkingVars × Array WorkingVars) (t : ℕ) :
    WorkingVars × Array WorkingVars :=
  let state := roundStep acc.1 (sha512K[t]!) (schedule[t]!)
  (state, acc.2.push state)

private def compressionPrefix (startState : WorkingVars) (schedule : Array Word) (n : ℕ) :
    WorkingVars × Array WorkingVars :=
  (List.range n).foldl (compressionPrefixStep schedule) (startState, #[startState])

private theorem compressionPrefix_succ
    (startState : WorkingVars) (schedule : Array Word) (n : ℕ) :
    compressionPrefix startState schedule (n + 1) =
      compressionPrefixStep schedule (compressionPrefix startState schedule n) n := by
  simp [compressionPrefix, List.range_succ, List.foldl_append, compressionPrefixStep]

private theorem compressionPrefix_size
    (startState : WorkingVars) (schedule : Array Word) :
    ∀ n, (compressionPrefix startState schedule n).2.size = n + 1 := by
  intro n
  induction n with
  | zero =>
      simp [compressionPrefix]
  | succ n ih =>
      rw [compressionPrefix_succ]
      simp [compressionPrefixStep, ih]

private theorem compressionPrefix_get_last
    (startState : WorkingVars) (schedule : Array Word) :
    ∀ n, (compressionPrefix startState schedule n).2[n]! =
      (compressionPrefix startState schedule n).1 := by
  intro n
  induction n with
  | zero =>
      simp [compressionPrefix]
  | succ n ih =>
      rw [compressionPrefix_succ]
      let state :=
        roundStep (compressionPrefix startState schedule n).1 (sha512K[n]!) (schedule[n]!)
      have hsize : (compressionPrefix startState schedule n).2.size = n + 1 :=
        compressionPrefix_size startState schedule n
      simpa [compressionPrefixStep, state, hsize] using
        (getElem!_push_size (xs := (compressionPrefix startState schedule n).2) (x := state))

private theorem compressionPrefix_get
    (startState : WorkingVars) (schedule : Array Word) :
    ∀ {n m}, n ≤ m →
      (compressionPrefix startState schedule m).2[n]! =
        (compressionPrefix startState schedule n).1 := by
  intro n m hnm
  induction m generalizing n with
  | zero =>
      have : n = 0 := by omega
      subst this
      simpa using compressionPrefix_get_last startState schedule 0
  | succ m ih =>
      by_cases hEq : n = m + 1
      · subst hEq
        simpa using compressionPrefix_get_last startState schedule (m + 1)
      · have hnm' : n ≤ m := by omega
        have hlt : n < (compressionPrefix startState schedule m).2.size := by
          simpa [compressionPrefix_size] using (show n < m + 1 by omega)
        rw [compressionPrefix_succ]
        simpa [compressionPrefixStep, getElem!_push_lt hlt] using ih hnm'

private theorem compressionPrefix_four
    (startState : WorkingVars) (schedule : Array Word) (n : ℕ) :
    (compressionPrefix startState schedule (n + 4)).1 =
      let s0 := (compressionPrefix startState schedule n).1
      let s1 := roundStep s0 (sha512K[n]!) (schedule[n]!)
      let s2 := roundStep s1 (sha512K[n + 1]!) (schedule[n + 1]!)
      let s3 := roundStep s2 (sha512K[n + 2]!) (schedule[n + 2]!)
      let s4 := roundStep s3 (sha512K[n + 3]!) (schedule[n + 3]!)
      s4 := by
  rw [show n + 4 = ((n + 3) + 1) by omega]
  rw [compressionPrefix_succ]
  rw [show n + 3 = ((n + 2) + 1) by omega]
  rw [compressionPrefix_succ]
  rw [show n + 2 = ((n + 1) + 1) by omega]
  rw [compressionPrefix_succ]
  rw [show n + 1 = (n + 1) by rfl]
  rw [compressionPrefix_succ]
  simp [compressionPrefixStep]

private theorem compressionTrace_eq_prefix
    (startState : WorkingVars) (schedule : Array Word) :
    compressionTrace startState schedule = (compressionPrefix startState schedule 80).2 := by
  have hpair :
      (Id.run do
        let mut acc := (startState, #[startState])
        for t in List.range 80 do
          acc := compressionPrefixStep schedule acc t
        pure acc) = compressionPrefix startState schedule 80 := by
    dsimp [compressionPrefix]
    exact List.idRun_forIn_yield_eq_foldl
      (l := List.range 80)
      (f := fun t acc => pure (compressionPrefixStep schedule acc t))
      (init := (startState, #[startState]))
  simpa [compressionTrace] using congrArg Prod.snd hpair

private theorem compressionTrace_get
    (startState : WorkingVars) (schedule : Array Word) {n : ℕ} (hn : n ≤ 80) :
    (compressionTrace startState schedule)[n]! = (compressionPrefix startState schedule n).1 := by
  rw [compressionTrace_eq_prefix]
  exact compressionPrefix_get startState schedule hn

/-! ## C5: Full compression trace -/

/-- Base case: the carried state at the previous row is the initial state. -/
theorem compression_trace_base (air : C FBB ExtF) (start : ℕ) :
    carriedState air (blockStateRow air start 0) = blockStartState air start := by
  simp [blockStartState]

/-- Inductive step: applies four_rounds_per_row at the current offset
    to advance from compressionTrace[offset*4] to [(offset+1)*4]. -/
theorem compression_trace_step (air : C FBB ExtF) (start : ℕ) (offset : ℕ)
    (hoffset : offset < 20)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (hcarry : roundCarryBoundsAt air (start + offset))
    (ih : carriedState air (blockStateRow air start offset) =
      (compressionTrace (blockStartState air start)
        (expandSchedule (blockInputWords air start)))[offset * 4]!) :
    carriedState air (blockStateRow air start (offset + 1)) =
      (compressionTrace (blockStartState air start)
        (expandSchedule (blockInputWords air start)))[(offset + 1) * 4]! := by
  let initialState := blockStartState air start
  let schedule := expandSchedule (blockInputWords air start)
  let baseRound := offset * 4
  have hEq : (offset + 1) * 4 = baseRound + 4 := by
    dsimp [baseRound]
    omega
  have htrace_next :
      (compressionTrace initialState schedule)[baseRound + 4]! =
        let s0 := (compressionPrefix initialState schedule baseRound).1
        let s1 := roundStep s0 (sha512K[baseRound]!) (schedule[baseRound]!)
        let s2 := roundStep s1 (sha512K[baseRound + 1]!) (schedule[baseRound + 1]!)
        let s3 := roundStep s2 (sha512K[baseRound + 2]!) (schedule[baseRound + 2]!)
        let s4 := roundStep s3 (sha512K[baseRound + 3]!) (schedule[baseRound + 3]!)
        s4 := by
    have h := compressionTrace_get initialState schedule (n := baseRound + 4) (by
      dsimp [baseRound]
      omega)
    rw [compressionPrefix_four] at h
    exact h
  have hprev_prefix :
      (compressionTrace initialState schedule)[baseRound]! =
        (compressionPrefix initialState schedule baseRound).1 :=
    compressionTrace_get initialState schedule (n := baseRound) (by
      dsimp [baseRound]
      omega)
  have hrow : blockStateRow air start (offset + 1) = start + offset :=
    blockStateRow_succ air start offset
  have hround :=
    four_rounds_per_row air start offset hoffset hwindow hrot hshape hc hcarry
      ((compressionTrace initialState schedule)[baseRound]!) ih
  dsimp [initialState, schedule, baseRound] at hround
  rw [hprev_prefix] at hround
  have hfinal :
      carriedState air (start + offset) =
        (compressionTrace initialState schedule)[baseRound + 4]! :=
    hround.trans htrace_next.symm
  rw [← hEq] at hfinal
  exact hrow.symm ▸ hfinal

/-- Full compression trace by induction on offset. -/
theorem compression_trace_per_row (air : C FBB ExtF) (start : ℕ) (offset : ℕ)
    (hoffset : offset ≤ 20)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (hcarry : roundCarryRangeOnBlock air start) :
    let initialState := blockStartState air start
    let schedule := expandSchedule (blockInputWords air start)
    carriedState air (blockStateRow air start offset) =
      (compressionTrace initialState schedule)[offset * 4]! := by
  dsimp
  induction offset with
  | zero =>
      have hzero :=
        compressionTrace_get (blockStartState air start)
          (expandSchedule (blockInputWords air start)) (n := 0) (by omega)
      exact (compression_trace_base air start).trans hzero.symm
  | succ offset ih =>
      have hoffset' : offset < 20 := by omega
      exact compression_trace_step air start offset hoffset' hwindow hrot hshape hc
        (hcarry offset hoffset') (ih (by omega))

/-- The carried state at the last round row is the final compression output. -/
theorem compression_trace_final (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (hcarry : roundCarryRangeOnBlock air start) :
    carriedState air (blockStateRow air start 20) =
      (compressionTrace (blockStartState air start)
        (expandSchedule (blockInputWords air start)))[80]! := by
  simpa using compression_trace_per_row air start 20 (by omega) hwindow hrot hshape hc hcarry

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
