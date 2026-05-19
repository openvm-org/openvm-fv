/-
  Layer E0: Block Window Shape

  Block-window shape lemmas for SHA-256 block proofs.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.TraceFacts

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## E1: Block window shape from encoder_selector_idx = 0

When blockHasherConstraints holds and encoder_selector_idx = 0 at some row x,
the trace has the correct block window shape at x. -/

/-- encoder_selector_idx = 0 implies is_round_row = 1 and is_first_4_rows = 1. -/
theorem selector_zero_implies_round (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row)
    (hsel : encoder_selector_idx air row = 0) :
    is_round_row air row = 1 ∧ is_first_4_rows air row = 1 := by
  refine ⟨?_, ?_⟩
  · exact (is_round_iff_selector_lt_16 air row hf).2 ⟨0, by omega, hsel⟩
  · exact (is_first_4_iff_selector_lt_4 air row hf).2 ⟨0, by omega, hsel⟩

/-- If a row is neither round nor digest, its selector must be the padding code `17`. -/
private theorem selector_eq_17_of_not_round_or_digest (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row)
    (hround0 : is_round_row air row = 0)
    (hdigest0 : is_digest_row air row = 0) :
    encoder_selector_idx air row = 17 := by
  rcases encoder_selector_valid air row hf with ⟨n, hn, hsel⟩
  have hn_ge_16 : 16 ≤ n := by
    by_contra hn_lt_16
    have hround1 : is_round_row air row = 1 :=
      (is_round_iff_selector_lt_16 air row hf).2 ⟨n, by omega, hsel⟩
    have : (0 : FBB) = 1 := by simpa [hround0] using hround1
    exact (by decide : (0 : FBB) ≠ 1) this
  have hn_ne_16 : n ≠ 16 := by
    intro hn16
    have hsel16 : encoder_selector_idx air row = 16 := by
      simpa [hn16] using hsel
    have hdigest1 : is_digest_row air row = 1 :=
      (is_digest_iff_selector_eq_16 air row hf).2 hsel16
    have : (0 : FBB) = 1 := by simpa [hdigest0] using hdigest1
    exact (by decide : (0 : FBB) ≠ 1) this
  have hn17 : n = 17 := by
    omega
  simpa [hn17] using hsel

private theorem last_row_not_round
    (air : C FBB ExtF)
    (hc : blockHasherConstraints air) :
    is_round_row air (Circuit.last_row air) = 0 := by
  rcases hc (Circuit.last_row air) with ⟨hf_last, _, _, _, _, _, _, _⟩
  have hpad : padding_flag air (Circuit.last_row air) = 1 := last_row_padding air hc
  have hsum : is_round_row air (Circuit.last_row air) + is_digest_row air (Circuit.last_row air) = 0 := by
    have : 1 - (is_round_row air (Circuit.last_row air) +
        is_digest_row air (Circuit.last_row air)) = 1 := by
      simpa [padding_flag] using hpad
    exact sub_eq_self.mp this
  rcases is_round_row_boolean air (Circuit.last_row air) hf_last with hround0 | hround1
  · exact hround0
  · rcases is_digest_row_boolean air (Circuit.last_row air) hf_last with hdigest0 | hdigest1
    · have : (1 : FBB) = 0 := by simpa [hround1, hdigest0] using hsum
      exact False.elim ((by decide : (1 : FBB) ≠ 0) this)
    · have : (2 : FBB) = 0 := by simpa [hround1, hdigest1] using hsum
      exact False.elim ((by decide : (2 : FBB) ≠ 0) this)

private theorem real_row_lt_last_row
    (air : C FBB ExtF) (row : ℕ)
    (hc : blockHasherConstraints air)
    (hrow : row ≤ Circuit.last_row air)
    (hreal : is_round_row air row = 1 ∨ is_digest_row air row = 1) :
    row < Circuit.last_row air := by
  by_contra hnot
  have hrow_eq : row = Circuit.last_row air := by omega
  rcases hreal with hround | hdigest
  · have : is_round_row air (Circuit.last_row air) = 1 := by simpa [hrow_eq] using hround
    exact False.elim ((by decide : (0 : FBB) ≠ 1) ((last_row_not_round air hc) ▸ this))
  · have : is_digest_row air (Circuit.last_row air) = 1 := by simpa [hrow_eq] using hdigest
    exact False.elim ((by decide : (0 : FBB) ≠ 1) ((last_row_not_digest air hc) ▸ this))

/-- Base case: row x has selector_idx = 0 and is a round row. -/
theorem block_round_rows_base (air : C FBB ExtF) (x : ℕ)
    (hf : flag_constraints air x)
    (hsel : encoder_selector_idx air x = 0) :
    encoder_selector_idx air x = 0 ∧
    is_round_row air x = 1 ∧
    is_digest_row air x = 0 := by
  have hround : is_round_row air x = 1 := (selector_zero_implies_round air x hf hsel).1
  have hdigest_not_one : is_digest_row air x ≠ 1 := by
    intro hdigest
    have : encoder_selector_idx air x = 16 := (is_digest_iff_selector_eq_16 air x hf).mp hdigest
    have : (0 : FBB) = 16 := by simpa [hsel] using this.symm
    exact (by decide : (0 : FBB) ≠ 16) this
  have hdigest_bool := is_digest_row_boolean air x hf
  rcases hdigest_bool with hdigest | hdigest
  · exact ⟨hsel, hround, hdigest⟩
  · exact False.elim (hdigest_not_one hdigest)

/-- Inductive step: row `x + offset` is supported and round, so the next row
    advances the selector to `offset + 1` and stays in the round region. -/
theorem block_round_rows_step_of_lt_last_row (air : C FBB ExtF) (x offset : ℕ)
    (hoffset : offset < 15)
    (hrow : x + offset < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hf_curr : flag_constraints air (x + offset))
    (hf_next : flag_constraints air (x + offset + 1))
    (ht : trace_shape_constraints air (x + offset))
    (ih_sel : encoder_selector_idx air (x + offset) = (offset : FBB))
    (ih_round : is_round_row air (x + offset) = 1) :
    encoder_selector_idx air (x + offset + 1) = ((offset + 1 : ℕ) : FBB) ∧
    is_round_row air (x + offset + 1) = 1 ∧
    is_digest_row air (x + offset + 1) = 0 := by
  have hsel_next : encoder_selector_idx air (x + offset + 1) = ((offset + 1 : ℕ) : FBB) := by
    have hstep := round_row_idx_increments air (x + offset) hrow hrot ht hf_curr ih_round
    simpa [nextRow, hrow.ne, ih_sel, Nat.cast_add] using hstep
  have hround_next : is_round_row air (x + offset + 1) = 1 :=
    (is_round_iff_selector_lt_16 air (x + offset + 1) hf_next).2
      ⟨offset + 1, by omega, hsel_next⟩
  have hdigest_next : is_digest_row air (x + offset + 1) = 0 := by
    rcases is_digest_row_boolean air (x + offset + 1) hf_next with hdigest0 | hdigest1
    · exact hdigest0
    · rcases round_plus_digest_boolean air (x + offset + 1) hf_next with hsum0 | hsum1
      · have : (2 : FBB) = 0 := by simpa [hround_next, hdigest1] using hsum0
        exact False.elim ((by decide : (2 : FBB) ≠ 0) this)
      · have : (2 : FBB) = 1 := by simpa [hround_next, hdigest1] using hsum1
        exact False.elim ((by decide : (2 : FBB) ≠ 1) this)
  exact ⟨hsel_next, hround_next, hdigest_next⟩

/-- Inductive step specialized from block-window support. -/
theorem block_round_rows_step (air : C FBB ExtF) (x offset : ℕ)
    (hoffset : offset < 15)
    (hwindow : blockWindowSupported air x)
    (hrot : rotation_consistent air)
    (hf_curr : flag_constraints air (x + offset))
    (hf_next : flag_constraints air (x + offset + 1))
    (ht : trace_shape_constraints air (x + offset))
    (ih_sel : encoder_selector_idx air (x + offset) = (offset : FBB))
    (ih_round : is_round_row air (x + offset) = 1) :
    encoder_selector_idx air (x + offset + 1) = ((offset + 1 : ℕ) : FBB) ∧
    is_round_row air (x + offset + 1) = 1 ∧
    is_digest_row air (x + offset + 1) = 0 := by
  have hrow : x + offset < Circuit.last_row air := by
    dsimp [blockWindowSupported] at hwindow
    omega
  exact block_round_rows_step_of_lt_last_row air x offset hoffset hrow hrot hf_curr hf_next ht ih_sel ih_round

/-- By induction: rows x..x+15 are round rows with selector_idx = offset. -/
theorem block_round_rows (air : C FBB ExtF) (x : ℕ) (offset : ℕ)
    (hoffset : offset < 16)
    (hwindow : blockWindowSupported air x)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hsel : encoder_selector_idx air x = 0) :
    encoder_selector_idx air (x + offset) = (offset : FBB) ∧
    is_round_row air (x + offset) = 1 ∧
    is_digest_row air (x + offset) = 0 := by
  induction offset with
  | zero =>
      rcases hc x with ⟨hf, _, _, _, _, _, _, _⟩
      simpa using block_round_rows_base air x hf hsel
  | succ offset ih =>
      have hoffset_prev : offset < 16 := by
        omega
      have hoffset_step : offset < 15 := by
        omega
      rcases ih hoffset_prev with ⟨ih_sel, ih_round, _⟩
      rcases hc (x + offset) with ⟨hf_curr, _, ht, _, _, _, _, _⟩
      rcases hc (x + offset + 1) with ⟨hf_next, _, _, _, _, _, _, _⟩
      simpa [Nat.add_assoc] using
        block_round_rows_step air x offset hoffset_step hwindow hrot hf_curr hf_next ht ih_sel ih_round

/-- Starting from any supported row with `encoder_selector_idx = 0`, the constraints
    force the first 16 rows of the block window to be real round rows. -/
theorem block_round_rows_of_start_le (air : C FBB ExtF) (x : ℕ) (offset : ℕ)
    (hoffset : offset < 16)
    (hx : x ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hsel : encoder_selector_idx air x = 0) :
    encoder_selector_idx air (x + offset) = (offset : FBB) ∧
    is_round_row air (x + offset) = 1 ∧
    is_digest_row air (x + offset) = 0 ∧
    x + offset ≤ Circuit.last_row air := by
  induction offset with
  | zero =>
      rcases hc x with ⟨hf, _, _, _, _, _, _, _⟩
      rcases block_round_rows_base air x hf hsel with ⟨hsel0, hround, hdigest⟩
      exact ⟨hsel0, hround, hdigest, hx⟩
  | succ offset ih =>
      have hoffset_prev : offset < 16 := by omega
      have hoffset_step : offset < 15 := by omega
      rcases ih hoffset_prev with ⟨ih_sel, ih_round, ih_digest, ih_valid⟩
      rcases hc (x + offset) with ⟨hf_curr, _, ht, _, _, _, _, _⟩
      rcases hc (x + offset + 1) with ⟨hf_next, _, _, _, _, _, _, _⟩
      have hcurr_lt : x + offset < Circuit.last_row air :=
        real_row_lt_last_row air (x + offset) hc ih_valid (Or.inl ih_round)
      rcases block_round_rows_step_of_lt_last_row air x offset hoffset_step hcurr_lt hrot
          hf_curr hf_next ht ih_sel ih_round with ⟨hsel_next, hround_next, hdigest_next⟩
      exact ⟨hsel_next, hround_next, hdigest_next, by omega⟩

/-- Once `start` is known to be an actual trace row, `encoder_selector_idx = 0`
    forces the full 17-row SHA-256 block window to fit before `last_row`. -/
theorem blockWindowSupported_of_start_le (air : C FBB ExtF) (x : ℕ)
    (hx : x ≤ Circuit.last_row air)
    (hsel : encoder_selector_idx air x = 0)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    blockWindowSupported air x := by
  rcases block_round_rows_of_start_le air x 15 (by omega) hx hrot hc hsel with
    ⟨_, hround15, _, hvalid15⟩
  have hlt15 : x + 15 < Circuit.last_row air :=
    real_row_lt_last_row air (x + 15) hc hvalid15 (Or.inl hround15)
  dsimp [blockWindowSupported]
  omega

/-- Row x + 16 is a digest row. -/
theorem block_digest_row (air : C FBB ExtF) (x : ℕ)
    (hwindow : blockWindowSupported air x)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hsel : encoder_selector_idx air x = 0) :
    encoder_selector_idx air (x + 16) = 16 ∧
    is_round_row air (x + 16) = 0 ∧
    is_digest_row air (x + 16) = 1 := by
  have hrow : x + 15 < Circuit.last_row air := by
    dsimp [blockWindowSupported] at hwindow
    omega
  rcases block_round_rows air x 15 (by omega) hwindow hrot hc hsel with
    ⟨hsel15, hround15, _⟩
  rcases hc (x + 15) with ⟨hf15, _, ht15, _, _, _, _, _⟩
  rcases hc (x + 16) with ⟨hf16, _, _, _, _, _, _, _⟩
  have hsel16 : encoder_selector_idx air (x + 16) = 16 := by
    have hstep := round_row_idx_increments air (x + 15) hrow hrot ht15 hf15 hround15
    simpa [nextRow, hrow.ne, hsel15, Nat.cast_add] using hstep
  have hdigest16 : is_digest_row air (x + 16) = 1 :=
    (is_digest_iff_selector_eq_16 air (x + 16) hf16).2 hsel16
  have hround16 : is_round_row air (x + 16) = 0 := by
    rcases is_round_row_boolean air (x + 16) hf16 with hround0 | hround1
    · exact hround0
    · rcases round_plus_digest_boolean air (x + 16) hf16 with hsum0 | hsum1
      · have : (2 : FBB) = 0 := by simpa [hround1, hdigest16] using hsum0
        exact False.elim ((by decide : (2 : FBB) ≠ 0) this)
      · have : (2 : FBB) = 1 := by simpa [hround1, hdigest16] using hsum1
        exact False.elim ((by decide : (2 : FBB) ≠ 1) this)
  exact ⟨hsel16, hround16, hdigest16⟩

/-- The previous row (with wrap-around) is a digest or padding row. -/
theorem block_prev_row (air : C FBB ExtF) (x : ℕ)
    (hwindow : blockWindowSupported air x)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hsel : encoder_selector_idx air x = 0) :
    encoder_selector_idx air (prevRow air x) = 16 ∨
    encoder_selector_idx air (prevRow air x) = 17 := by
  by_cases hx0 : x = 0
  · subst hx0
    rcases hc (Circuit.last_row air) with ⟨hf_last, _, ht_last, _, _, _, _, _⟩
    rcases ht_last with ⟨_, _, h279, _, _, _, _, _, _, _, _⟩
    have hpad_sub : padding_flag air (Circuit.last_row air) - 1 = 0 := by
      have h279c : constraint_279 air (Circuit.last_row air) :=
        (constraint_279_of_extraction air (Circuit.last_row air)).mp h279
      simpa [constraint_279, Circuit.isLastRow] using h279c
    have hpad : padding_flag air (Circuit.last_row air) = 1 := sub_eq_zero.mp hpad_sub
    have hsum : is_round_row air (Circuit.last_row air) + is_digest_row air (Circuit.last_row air) = 0 := by
      have : 1 - (is_round_row air (Circuit.last_row air) +
          is_digest_row air (Circuit.last_row air)) = 1 := by
        simpa [padding_flag] using hpad
      exact sub_eq_self.mp this
    have hround0 : is_round_row air (Circuit.last_row air) = 0 := by
      rcases is_round_row_boolean air (Circuit.last_row air) hf_last with hround0 | hround1
      · exact hround0
      · rcases is_digest_row_boolean air (Circuit.last_row air) hf_last with hdigest0 | hdigest1
        · have : (1 : FBB) = 0 := by simpa [hround1, hdigest0] using hsum
          exact False.elim ((by decide : (1 : FBB) ≠ 0) this)
        · have : (2 : FBB) = 0 := by simpa [hround1, hdigest1] using hsum
          exact False.elim ((by decide : (2 : FBB) ≠ 0) this)
    have hdigest0 : is_digest_row air (Circuit.last_row air) = 0 := by
      rcases is_digest_row_boolean air (Circuit.last_row air) hf_last with hdigest0 | hdigest1
      · exact hdigest0
      · have : (1 : FBB) = 0 := by simpa [hround0, hdigest1] using hsum
        exact False.elim ((by decide : (1 : FBB) ≠ 0) this)
    have hsel17 : encoder_selector_idx air (Circuit.last_row air) = 17 :=
      selector_eq_17_of_not_round_or_digest air (Circuit.last_row air) hf_last hround0 hdigest0
    exact Or.inr (by simpa [prevRow] using hsel17)
  · have hx_pos : 0 < x := Nat.pos_of_ne_zero hx0
    have hprev : x - 1 < Circuit.last_row air := by
      dsimp [blockWindowSupported] at hwindow
      omega
    have hnextrow : nextRow air (x - 1) = x := by
      have hsub : x - 1 + 1 = x := Nat.sub_add_cancel (Nat.succ_le_of_lt hx_pos)
      simp [nextRow, hprev.ne, hsub]
    rcases hc (x - 1) with ⟨hf_prev, _, ht_prev, _, _, _, _, _⟩
    rcases hc x with ⟨hf_x, _, _, _, _, _, _, _⟩
    rcases block_round_rows_base air x hf_x hsel with ⟨hsel_x, hround_x, hdigest_x⟩
    rcases ht_prev with ⟨_, _, _, _, _, h276, _, _, _, _, _⟩
    have hnext_round : next_is_round_row air (x - 1) = 1 := by
      calc
        next_is_round_row air (x - 1) = is_round_row air (nextRow air (x - 1)) :=
          next_is_round_row_eq_nextRow air hrot (x - 1) hprev.le
        _ = is_round_row air x := by simp [hnextrow]
        _ = 1 := hround_x
    have hnext_digest : next_is_digest_row air (x - 1) = 0 := by
      calc
        next_is_digest_row air (x - 1) = is_digest_row air (nextRow air (x - 1)) :=
          next_is_digest_row_eq_nextRow air hrot (x - 1) hprev.le
        _ = is_digest_row air x := by simp [hnextrow]
        _ = 0 := hdigest_x
    have hnext_pad : next_padding_flag air (x - 1) = 0 := by
      simp [next_padding_flag, hnext_round, hnext_digest]
    have hnext_sel : next_encoder_selector_idx air (x - 1) = 0 := by
      calc
        next_encoder_selector_idx air (x - 1) = encoder_selector_idx air (nextRow air (x - 1)) :=
          next_encoder_selector_idx_eq_nextRow air hrot (x - 1) hprev.le
        _ = encoder_selector_idx air x := by simp [hnextrow]
        _ = 0 := hsel_x
    have htrans :
        encoder_selector_idx air (x - 1) +
          (is_round_row air (x - 1) +
            ((((is_digest_row air (x - 1)) * (next_is_round_row air (x - 1))) * 16) * 2013265920) +
            ((is_digest_row air (x - 1)) * (next_padding_flag air (x - 1)))) -
          next_encoder_selector_idx air (x - 1) = 0 := by
      have h276c : constraint_276 air (x - 1) :=
        (constraint_276_of_extraction air (x - 1)).mp h276
      have := (constraint_276_eq_selector_transition air (x - 1)).mp h276c
      simpa [Circuit.isTransitionRow, hprev.ne] using this
    rcases is_digest_row_boolean air (x - 1) hf_prev with hdigest_prev0 | hdigest_prev1
    · rcases is_round_row_boolean air (x - 1) hf_prev with hround_prev0 | hround_prev1
      · have hsel17 :=
          selector_eq_17_of_not_round_or_digest air (x - 1) hf_prev hround_prev0 hdigest_prev0
        have : (17 : FBB) = 0 := by
          rw [hround_prev0, hdigest_prev0, hnext_pad, hnext_sel] at htrans
          simpa [hsel17] using htrans
        exact False.elim ((by decide : (17 : FBB) ≠ 0) this)
      · have hbad : encoder_selector_idx air (x - 1) + 1 = 0 := by
          rw [hround_prev1, hdigest_prev0, hnext_pad, hnext_sel] at htrans
          simpa [hnext_round, add_assoc, add_left_comm, add_comm] using htrans
        rcases (is_round_iff_selector_lt_16 air (x - 1) hf_prev).mp hround_prev1 with
          ⟨n, hn, hseln⟩
        have hnat : (((n + 1 : ℕ)) : FBB) = 0 := by
          simpa [hseln, Nat.cast_add] using hbad
        have hneq_zero : (((n + 1 : ℕ)) : FBB) ≠ 0 := by
          intro hzero
          revert hzero
          interval_cases n <;> intro hzero <;> norm_num at hzero <;> contradiction
        exact False.elim (hneq_zero hnat)
    · have hsel16 : encoder_selector_idx air (x - 1) = 16 :=
        (is_digest_iff_selector_eq_16 air (x - 1) hf_prev).mp hdigest_prev1
      exact Or.inl (by simpa [prevRow, hx0] using hsel16)

/-- Full block window shape, assembled from the preceding lemmas. -/
theorem blockWindowHasShape_of_constraints (air : C FBB ExtF) (x : ℕ)
    (hwindow : blockWindowSupported air x)
    (hsel : encoder_selector_idx air x = 0)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    blockWindowHasShape air x := by
  dsimp [blockWindowHasShape]
  have hdig := block_digest_row air x hwindow hrot hc hsel
  refine ⟨block_prev_row air x hwindow hrot hc hsel, ?_, hdig.1, hdig.2.1, hdig.2.2⟩
  intro offset hoffset
  exact block_round_rows air x offset hoffset hwindow hrot hc hsel

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
