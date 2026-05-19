/-
  Layer A: Per-Row Facts (Trace Facts)

  Covers trace-shape consequences.

  Depends on: SelectorFacts
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.FieldArithmetic
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.SelectorFacts

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## Trace Shape (constraints 272–282)

These constrain the row-to-row sequencing of the AIR trace. -/

/-- Padding row implies next row is also padding (constraint 274). -/
theorem padding_implies_next_padding (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (ht : trace_shape_constraints air row)
    (hf_next : flag_constraints air (nextRow air row)) :
    is_round_row air row = 0 → is_digest_row air row = 0 →
    is_round_row air (nextRow air row) = 0 ∧ is_digest_row air (nextRow air row) = 0 := by
  intro hround hdigest
  rcases ht with ⟨_, _, _, h274, _, _, _, _, _, _, _⟩
  have hnext_pad_sub : next_padding_flag air row - 1 = 0 := by
    have h274c : constraint_274 air row := (constraint_274_of_extraction air row).mp h274
    simpa [constraint_274, Circuit.isTransitionRow, hrow.ne, padding_flag, hround, hdigest] using h274c
  have hnext_pad : next_padding_flag air row = 1 := sub_eq_zero.mp hnext_pad_sub
  have hnext_sum : is_round_row air (nextRow air row) + is_digest_row air (nextRow air row) = 0 := by
    have hpad_as_eq : 1 - (is_round_row air (nextRow air row) + is_digest_row air (nextRow air row)) = 1 := by
      simpa [next_padding_flag, next_is_round_row_eq air hrot row hrow,
        next_is_digest_row_eq air hrot row hrow, nextRow, hrow.ne] using hnext_pad
    exact sub_eq_self.mp hpad_as_eq
  have hnext_round_bool := is_round_row_boolean air (nextRow air row) hf_next
  have hnext_digest_bool := is_digest_row_boolean air (nextRow air row) hf_next
  rcases hnext_round_bool with hnext_round0 | hnext_round1
  · refine ⟨hnext_round0, ?_⟩
    rcases hnext_digest_bool with hnext_digest0 | hnext_digest1
    · exact hnext_digest0
    · have hfalse : False := by
        have : (1 : FBB) = 0 := by simpa [hnext_round0, hnext_digest1] using hnext_sum
        exact (by decide : (1 : FBB) ≠ 0) this
      exact False.elim hfalse
  · rcases hnext_digest_bool with hnext_digest0 | hnext_digest1
    · have hfalse : False := by
        have : (1 : FBB) = 0 := by simpa [hnext_round1, hnext_digest0] using hnext_sum
        exact (by decide : (1 : FBB) ≠ 0) this
      exact False.elim hfalse
    · have hfalse : False := by
        have : (2 : FBB) = 0 := by simpa [hnext_round1, hnext_digest1] using hnext_sum
        exact (by decide : (2 : FBB) ≠ 0) this
      exact False.elim hfalse

/-- Digest row implies next row is not digest (constraint 275). -/
theorem digest_implies_next_not_digest (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (ht : trace_shape_constraints air row) :
    is_digest_row air row = 1 →
    is_digest_row air (nextRow air row) = 0 := by
  intro hdigest
  rcases ht with ⟨_, _, _, _, h275, _, _, _, _, _, _⟩
  have hnext : next_is_digest_row air row = 0 := by
    have h275c : constraint_275 air row := (constraint_275_of_extraction air row).mp h275
    simpa [constraint_275, hdigest] using h275c
  simpa [next_is_digest_row_eq_nextRow air hrot row hrow] using hnext

/-- On round rows, row index increments by 1 (constraint 276, round→round). -/
theorem round_row_idx_increments (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (ht : trace_shape_constraints air row)
    (hf : flag_constraints air row)
    (hround : is_round_row air row = 1) :
    encoder_selector_idx air (nextRow air row) = encoder_selector_idx air row + 1 := by
  rcases ht with ⟨_, _, _, _, _, h276, _, _, _, _, _⟩
  have hdigest0 : is_digest_row air row = 0 := by
    rcases is_digest_row_boolean air row hf with hdigest0 | hdigest1
    · exact hdigest0
    · rcases round_plus_digest_boolean air row hf with hsum0 | hsum1
      · have : (2 : FBB) = 0 := by simpa [hround, hdigest1] using hsum0
        exact False.elim ((by decide : (2 : FBB) ≠ 0) this)
      · have : (2 : FBB) = 1 := by simpa [hround, hdigest1] using hsum1
        exact False.elim ((by decide : (2 : FBB) ≠ 1) this)
  have hstep : encoder_selector_idx air row + 1 - next_encoder_selector_idx air row = 0 := by
    have h276c : constraint_276 air row := (constraint_276_of_extraction air row).mp h276
    have := (constraint_276_eq_selector_transition air row).mp h276c
    simpa [Circuit.isTransitionRow, hrow.ne, hround, hdigest0] using this
  have hstep' : next_encoder_selector_idx air row = encoder_selector_idx air row + 1 := by
    exact (sub_eq_zero.mp hstep).symm
  simpa [next_encoder_selector_idx_eq_nextRow air hrot row hrow.le] using hstep'

/-- Block index increments at digest→round transitions (constraints 280–282). -/
theorem block_idx_transition (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (ht : trace_shape_constraints air row)
    (hdigest : is_digest_row air row = 1)
    (hround_next : is_round_row air (nextRow air row) = 1) :
    global_block_idx air (nextRow air row) = global_block_idx air row + 1 := by
  rcases ht with ⟨_, _, _, _, _, _, _, _, _, h281, _⟩
  have hnext_round : next_is_round_row air row = 1 := by
    simpa [nextRow, hrow.ne, next_is_round_row_eq air hrot row hrow] using hround_next
  dsimp [constraint_281] at h281
  have hstep : global_block_idx air row + 1 - global_block_idx air (nextRow air row) = 0 := by
    simpa [nextRow, hrow.ne, Circuit.isTransitionRow, hrow.ne, hdigest, hnext_round,
      next_global_block_idx_eq air hrot row hrow] using h281
  exact (sub_eq_zero.mp hstep).symm

/-- Block index is preserved on round rows (constraint 280). -/
theorem block_idx_preserved_on_round (air : C FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (ht : trace_shape_constraints air row)
    (hround : is_round_row air row = 1) :
    global_block_idx air (nextRow air row) = global_block_idx air row := by
  rcases ht with ⟨_, _, _, _, _, _, _, _, h280, _, _⟩
  dsimp [constraint_280] at h280
  have hsame : global_block_idx air row - global_block_idx air (nextRow air row) = 0 := by
    simpa [nextRow, hrow.ne, hround, next_global_block_idx_eq air hrot row hrow] using h280
  exact (sub_eq_zero.mp hsame).symm

/-! ## Last-row and boundary facts -/

theorem last_row_padding
    (air : C FBB ExtF)
    (hc : blockHasherConstraints air) :
    padding_flag air (Circuit.last_row air) = 1 := by
  rcases hc (Circuit.last_row air) with ⟨_, _, ht_last, _, _, _, _, _⟩
  rcases ht_last with ⟨_, _, h279, _, _, _, _, _, _, _, _⟩
  have hpad_sub : padding_flag air (Circuit.last_row air) - 1 = 0 := by
    have h279c : constraint_279 air (Circuit.last_row air) :=
      (constraint_279_of_extraction air (Circuit.last_row air)).mp h279
    simpa [constraint_279, Circuit.isLastRow] using h279c
  exact sub_eq_zero.mp hpad_sub

theorem last_row_not_digest
    (air : C FBB ExtF)
    (hc : blockHasherConstraints air) :
    is_digest_row air (Circuit.last_row air) = 0 := by
  rcases hc (Circuit.last_row air) with ⟨hf_last, _, _, _, _, _, _, _⟩
  have hpad : padding_flag air (Circuit.last_row air) = 1 := last_row_padding air hc
  have hsum : is_round_row air (Circuit.last_row air) +
      is_digest_row air (Circuit.last_row air) = 0 := by
    have : 1 - (is_round_row air (Circuit.last_row air) +
        is_digest_row air (Circuit.last_row air)) = 1 := by
      simpa [padding_flag] using hpad
    exact sub_eq_self.mp this
  rcases is_digest_row_boolean air (Circuit.last_row air) hf_last with hdigest0 | hdigest1
  · exact hdigest0
  · rcases is_round_row_boolean air (Circuit.last_row air) hf_last with hround0 | hround1
    · have : (1 : FBB) = 0 := by simpa [hround0, hdigest1] using hsum
      exact False.elim ((by decide : (1 : FBB) ≠ 0) this)
    · have : (2 : FBB) = 0 := by simpa [hround1, hdigest1] using hsum
      exact False.elim ((by decide : (2 : FBB) ≠ 0) this)

theorem digest_row_lt_last_row
    (air : C FBB ExtF) (row : ℕ)
    (hc : blockHasherConstraints air)
    (hrow : row ≤ Circuit.last_row air)
    (hdigest : is_digest_row air row = 1) :
    row < Circuit.last_row air := by
  by_contra hnot_lt
  have hrow_eq : row = Circuit.last_row air := by omega
  have : is_digest_row air (Circuit.last_row air) = 1 := by simpa [hrow_eq] using hdigest
  exact False.elim ((by decide : (0 : FBB) ≠ 1) ((last_row_not_digest air hc) ▸ this))

/-! ## Global block index structure -/

theorem supported_real_row_global_block_idx_nat
    (air : C FBB ExtF)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    ∀ row, row ≤ Circuit.last_row air →
      (is_round_row air row = 1 ∨ is_digest_row air row = 1) →
      ∃ n : ℕ, n < row + 1 ∧ global_block_idx air row = (((n + 1 : ℕ) : FBB)) := by
  intro row hrow hreal
  induction row with
  | zero =>
      refine ⟨0, by omega, ?_⟩
      rcases hc 0 with ⟨_, _, ht0, _, _, _, _, _⟩
      rcases ht0 with ⟨_, _, _, _, _, _, _, h278, _, _, _⟩
      have hgbi0_sub : global_block_idx air 0 - 1 = 0 := by
        have h278c : constraint_278 air 0 := (constraint_278_of_extraction air 0).mp h278
        simpa [constraint_278, Circuit.isFirstRow] using h278c
      exact sub_eq_zero.mp hgbi0_sub
  | succ row ih =>
      have hrow_lt : row < Circuit.last_row air := by omega
      rcases hc row with ⟨hf, _, ht, _, _, _, _, _⟩
      rcases is_round_row_boolean air row hf with hround0 | hround1
      · rcases is_digest_row_boolean air row hf with hdigest0 | hdigest1
        · have hf_next : flag_constraints air (nextRow air row) := (hc (nextRow air row)).1
          have hpad_next := padding_implies_next_padding air row hrow_lt hrot ht hf_next hround0 hdigest0
          have : False := by
            rcases hreal with hreal_round | hreal_digest
            · have hround_zero : is_round_row air (row + 1) = 0 := by
                simpa [nextRow, hrow_lt.ne] using hpad_next.1
              have : (1 : FBB) = 0 := by simpa [hround_zero] using hreal_round
              exact (by decide : (1 : FBB) ≠ 0) this
            · have hdigest_zero : is_digest_row air (row + 1) = 0 := by
                simpa [nextRow, hrow_lt.ne] using hpad_next.2
              have : (1 : FBB) = 0 := by simpa [hdigest_zero] using hreal_digest
              exact (by decide : (1 : FBB) ≠ 0) this
          exact False.elim this
        · rcases hreal with hreal_round | hreal_digest
          · have hround_next : is_round_row air (nextRow air row) = 1 := by
              simpa [nextRow, hrow_lt.ne] using hreal_round
            rcases ih hrow_lt.le (Or.inr hdigest1) with ⟨n, hn_lt, hgbi⟩
            refine ⟨n + 1, by omega, ?_⟩
            calc
              global_block_idx air (row + 1) = global_block_idx air (nextRow air row) := by
                simp [nextRow, hrow_lt.ne]
              _ = global_block_idx air row + 1 := by
                simpa using block_idx_transition air row hrow_lt hrot ht hdigest1 hround_next
              _ = (((n + 1 : ℕ) : FBB)) + 1 := by simpa [hgbi]
              _ = (((n + 1 + 1 : ℕ) : FBB)) := by simp [Nat.cast_add]
          · have : is_digest_row air (row + 1) = 0 := by
              simpa [nextRow, hrow_lt.ne] using
                digest_implies_next_not_digest air row hrow_lt.le hrot ht hdigest1
            have : (0 : FBB) = 1 := by simpa [this] using hreal_digest
            exact False.elim ((by decide : (0 : FBB) ≠ 1) this)
      · rcases ih hrow_lt.le (Or.inl hround1) with ⟨n, hn_lt, hgbi⟩
        refine ⟨n, by omega, ?_⟩
        calc
          global_block_idx air (row + 1) = global_block_idx air (nextRow air row) := by
            simp [nextRow, hrow_lt.ne]
          _ = global_block_idx air row := by
            simpa using block_idx_preserved_on_round air row hrow_lt hrot ht hround1
          _ = (((n + 1 : ℕ) : FBB)) := hgbi

theorem supported_real_row_global_block_idx_ne_zero
    (air : C FBB ExtF)
    (htrace_fit : traceLengthFitsField air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hreal : is_round_row air row = 1 ∨ is_digest_row air row = 1) :
    global_block_idx air row ≠ 0 := by
  rcases supported_real_row_global_block_idx_nat air hrot hc row hrow hreal with ⟨n, hn_lt_row, hgbi⟩
  have hn_succ_lt : n + 1 < BB_prime := by
    have hrow_lt_prime : row + 1 < BB_prime := by
      exact lt_of_le_of_lt (Nat.succ_le_succ hrow) htrace_fit
    omega
  intro hgbi_zero
  have hcast_zero : (((n + 1 : ℕ) : FBB)) = 0 := by simpa [hgbi] using hgbi_zero
  exact natCast_ne_zero_of_lt_BB_prime hn_succ_lt (by omega) hcast_zero

/-! ## Padding propagation -/

theorem row_before_supported_real_row_is_real
    (air : C FBB ExtF) (row target : ℕ)
    (hrow_lt_target : row < target)
    (htarget_valid : target ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (htarget_real : is_round_row air target = 1 ∨ is_digest_row air target = 1) :
    is_round_row air row = 1 ∨ is_digest_row air row = 1 := by
  generalize hd : target - row = d
  induction d generalizing row with
  | zero =>
      omega
  | succ d ih =>
      rcases hc row with ⟨hf_row, _, ht_row, _, _, _, _, _⟩
      rcases is_round_row_boolean air row hf_row with hround0 | hround1
      · rcases is_digest_row_boolean air row hf_row with hdigest0 | hdigest1
        · have hrow_lt_last : row < Circuit.last_row air := by omega
          have hf_next : flag_constraints air (nextRow air row) := (hc (nextRow air row)).1
          have hnext_pad :=
            padding_implies_next_padding air row hrow_lt_last hrot ht_row hf_next hround0 hdigest0
          have hround_zero : is_round_row air (row + 1) = 0 := by
            simpa [nextRow, hrow_lt_last.ne] using hnext_pad.1
          have hdigest_zero : is_digest_row air (row + 1) = 0 := by
            simpa [nextRow, hrow_lt_last.ne] using hnext_pad.2
          by_cases hsucc : row + 1 = target
          · rcases htarget_real with hround_target | hdigest_target
            · have hround_target' : is_round_row air (row + 1) = 1 := by
                simpa [hsucc] using hround_target
              have : (0 : FBB) = 1 := by simpa [hround_zero] using hround_target'
              exact False.elim ((by decide : (0 : FBB) ≠ 1) this)
            · have hdigest_target' : is_digest_row air (row + 1) = 1 := by
                simpa [hsucc] using hdigest_target
              have : (0 : FBB) = 1 := by simpa [hdigest_zero] using hdigest_target'
              exact False.elim ((by decide : (0 : FBB) ≠ 1) this)
          · have hrow1_lt_target : row + 1 < target := by omega
            have hd' : target - (row + 1) = d := by omega
            have hreal_next := ih (row + 1) hrow1_lt_target hd'
            rcases hreal_next with hround_next | hdigest_next
            · have : (0 : FBB) = 1 := by simpa [hround_zero] using hround_next
              exact False.elim ((by decide : (0 : FBB) ≠ 1) this)
            · have : (0 : FBB) = 1 := by simpa [hdigest_zero] using hdigest_next
              exact False.elim ((by decide : (0 : FBB) ≠ 1) this)
        · exact Or.inr hdigest1
      · exact Or.inl hround1

private theorem later_real_row_after_digest_has_positive_gbi_offset
    (air : C FBB ExtF) (start target : ℕ)
    (hstart_valid : start ≤ Circuit.last_row air)
    (hstart_dig : is_digest_row air start = 1)
    (hstart_lt_target : start < target)
    (htarget_valid : target ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (htarget_real : is_round_row air target = 1 ∨ is_digest_row air target = 1) :
    ∃ k : ℕ, 0 < k ∧ k < target + 1 ∧
      global_block_idx air target = global_block_idx air start + (((k : ℕ) : FBB)) := by
  generalize hd : target - (start + 1) = d
  induction d generalizing target with
  | zero =>
      have htarget_eq : target = start + 1 := by omega
      have hstart_lt_last : start < Circuit.last_row air := by omega
      rcases hc start with ⟨_, _, ht_start, _, _, _, _, _⟩
      have hnext_digest0 : is_digest_row air target = 0 := by
        simpa [htarget_eq, nextRow, hstart_lt_last.ne] using
          digest_implies_next_not_digest air start hstart_valid hrot ht_start hstart_dig
      have htarget_round : is_round_row air target = 1 := by
        rcases htarget_real with hround_target | hdigest_target
        · exact hround_target
        · have : (0 : FBB) = 1 := by simpa [hnext_digest0] using hdigest_target
          exact False.elim ((by decide : (0 : FBB) ≠ 1) this)
      refine ⟨1, by omega, by omega, ?_⟩
      calc
        global_block_idx air target = global_block_idx air (nextRow air start) := by
          simpa [htarget_eq, nextRow, hstart_lt_last.ne]
        _ = global_block_idx air start + 1 := by
          have hnext_round : is_round_row air (nextRow air start) = 1 := by
            simpa [htarget_eq, nextRow, hstart_lt_last.ne] using htarget_round
          simpa using block_idx_transition air start hstart_lt_last hrot ht_start hstart_dig hnext_round
        _ = global_block_idx air start + (((1 : ℕ) : FBB)) := by simp
  | succ d ih =>
      have hstart_lt_target1 : start + 1 < target := by omega
      let prev := target - 1
      have hprev_lt_target : prev < target := by
        dsimp [prev]
        omega
      have hprev_valid : prev ≤ Circuit.last_row air := by
        dsimp [prev]
        omega
      have hprev_real :=
        row_before_supported_real_row_is_real air prev target hprev_lt_target htarget_valid hrot hc htarget_real
      have hstart_lt_prev : start < prev := by
        dsimp [prev]
        omega
      have hd' : prev - (start + 1) = d := by
        dsimp [prev]
        omega
      rcases ih prev hstart_lt_prev hprev_valid hprev_real hd' with ⟨k, hk_pos, hk_lt_prev, hgbi_prev⟩
      rcases hc prev with ⟨_, _, ht_prev, _, _, _, _, _⟩
      have hprev_lt_last : prev < Circuit.last_row air := by
        dsimp [prev]
        omega
      have hprev_succ : prev + 1 = target := by
        dsimp [prev]
        omega
      rcases hprev_real with hprev_round | hprev_dig
      · refine ⟨k, hk_pos, by omega, ?_⟩
        calc
          global_block_idx air target = global_block_idx air (nextRow air prev) := by
            simpa [nextRow, hprev_lt_last.ne, hprev_succ]
          _ = global_block_idx air prev := by
            exact block_idx_preserved_on_round air prev hprev_lt_last hrot ht_prev hprev_round
          _ = global_block_idx air start + (((k : ℕ) : FBB)) := hgbi_prev
      · have htarget_digest0 : is_digest_row air target = 0 := by
          calc
            is_digest_row air target = is_digest_row air (nextRow air prev) := by
              simpa [nextRow, hprev_lt_last.ne, hprev_succ]
            _ = 0 := digest_implies_next_not_digest air prev hprev_valid hrot ht_prev hprev_dig
        have htarget_round : is_round_row air target = 1 := by
          rcases htarget_real with hround_target | hdigest_target
          · exact hround_target
          · have : (0 : FBB) = 1 := by simpa [htarget_digest0] using hdigest_target
            exact False.elim ((by decide : (0 : FBB) ≠ 1) this)
        refine ⟨k + 1, by omega, by omega, ?_⟩
        calc
          global_block_idx air target = global_block_idx air (nextRow air prev) := by
            simpa [nextRow, hprev_lt_last.ne, hprev_succ]
          _ = global_block_idx air prev + 1 := by
            have hnext_round : is_round_row air (nextRow air prev) = 1 := by
              simpa [nextRow, hprev_lt_last.ne, hprev_succ] using htarget_round
            exact block_idx_transition air prev hprev_lt_last hrot ht_prev hprev_dig hnext_round
          _ = (global_block_idx air start + (((k : ℕ) : FBB))) + 1 := by rw [hgbi_prev]
          _ = global_block_idx air start + ((((k + 1 : ℕ) : FBB))) := by
            simp [Nat.cast_add, add_assoc]

theorem digest_row_same_gbi_impossible_of_lt
    (air : C FBB ExtF)
    (htrace_fit : traceLengthFitsField air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    ∀ r1 r2,
      r1 < r2 →
      r1 ≤ Circuit.last_row air →
      r2 ≤ Circuit.last_row air →
      is_digest_row air r1 = 1 →
      is_digest_row air r2 = 1 →
      global_block_idx air r1 = global_block_idx air r2 →
      False := by
  intro r1 r2 hlt hr1 hr2 hd1 hd2 hgbi
  rcases later_real_row_after_digest_has_positive_gbi_offset
      air r1 r2 hr1 hd1 hlt hr2 hrot hc (Or.inr hd2) with
      ⟨k, hk_pos, hk_lt_row, hgbi_off⟩
  have hk_lt_prime : k < BB_prime := by
    have hrow_lt_prime : r2 + 1 < BB_prime := by
      exact lt_of_le_of_lt (Nat.succ_le_succ hr2) htrace_fit
    omega
  have hcast_zero : (((k : ℕ) : FBB)) = 0 := by
    have heq : global_block_idx air r1 + (((k : ℕ) : FBB)) = global_block_idx air r1 := by
      calc
        global_block_idx air r1 + (((k : ℕ) : FBB)) = global_block_idx air r2 := hgbi_off.symm
        _ = global_block_idx air r1 := hgbi.symm
    have : global_block_idx air r1 + (((k : ℕ) : FBB)) = global_block_idx air r1 + 0 := by
      simpa using heq
    exact add_left_cancel this
  exact natCast_ne_zero_of_lt_BB_prime hk_lt_prime (by omega) hcast_zero

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
