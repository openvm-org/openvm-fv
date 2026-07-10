/- 
  Layer E0: Block Window Shape

  Block-window shape lemmas for SHA-512 block proofs.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.TraceFacts

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

private theorem constraint_533_eq_selector_transition
    (air : C FBB ExtF) (row : ℕ) :
    constraint_533 air row ↔
      Circuit.isTransitionRow air row *
        (encoder_selector_idx air row +
          is_round_row air row +
          (((is_digest_row air row * next_is_round_row air row) * 20) * 2013265920) +
          is_digest_row air row * next_padding_flag air row -
          next_encoder_selector_idx air row) = 0 := by
  have hcur :
      Sha2BlockHasherVmAir_sha512.constraints.selector_value_from (fun i => encoder_idx air i row) =
        encoder_selector_idx air row := by
    simp [Sha2BlockHasherVmAir_sha512.constraints.selector_value_from, encoder_selector_idx,
      Sha2BlockHasherVmAir_sha512.constraints.selector_digit_sum_from, encoder_selector_from,
      Sha2BlockHasherVmAir_sha512.constraints.encoder_choose2, encoder_choose2,
      encoder_digit_sum_from]
  have hnext :
      Sha2BlockHasherVmAir_sha512.constraints.selector_value_from (fun i => encoder_idx_next air i row) =
        next_encoder_selector_idx air row := by
    simp [Sha2BlockHasherVmAir_sha512.constraints.selector_value_from, next_encoder_selector_idx,
      Sha2BlockHasherVmAir_sha512.constraints.selector_digit_sum_from, encoder_selector_from,
      Sha2BlockHasherVmAir_sha512.constraints.encoder_choose2, encoder_choose2,
      encoder_digit_sum_from]
  constructor <;> intro h <;>
    simpa [constraint_533, hcur, hnext] using h

/-! ## E1: Block window shape from `encoder_selector_idx = 0`

When `blockHasherConstraints` holds and `encoder_selector_idx = 0` at some row
`x`, the trace has the correct 21-row SHA-512 block-window shape at `x`.
-/

/-- `encoder_selector_idx = 0` implies both the round and first-four flags. -/
theorem selector_zero_implies_round (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row)
    (hsel : encoder_selector_idx air row = 0) :
    is_round_row air row = 1 ∧ is_first_4_rows air row = 1 := by
  refine ⟨?_, ?_⟩
  · exact (is_round_iff_selector_lt_20 air row hf).2 ⟨0, by omega, hsel⟩
  · exact (is_first_4_iff_selector_lt_4 air row hf).2 ⟨0, by omega, hsel⟩

/-- If a row is neither round nor digest, its selector must be the padding code
    `21`. -/
private theorem selector_eq_21_of_not_round_or_digest (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row)
    (hround0 : is_round_row air row = 0)
    (hdigest0 : is_digest_row air row = 0) :
    encoder_selector_idx air row = 21 := by
  rcases encoder_selector_valid air row hf with ⟨n, hn, hsel⟩
  have hn_ge_20 : 20 ≤ n := by
    by_contra hn_lt_20
    have hround1 : is_round_row air row = 1 :=
      (is_round_iff_selector_lt_20 air row hf).2 ⟨n, by omega, hsel⟩
    have : (0 : FBB) = 1 := by simpa [hround0] using hround1
    exact (by decide : (0 : FBB) ≠ 1) this
  have hn_ne_20 : n ≠ 20 := by
    intro hn20
    have hsel20 : encoder_selector_idx air row = 20 := by
      simpa [hn20] using hsel
    have hdigest1 : is_digest_row air row = 1 :=
      (is_digest_iff_selector_eq_20 air row hf).2 hsel20
    have : (0 : FBB) = 1 := by simpa [hdigest0] using hdigest1
    exact (by decide : (0 : FBB) ≠ 1) this
  have hn21 : n = 21 := by
    omega
  simpa [hn21] using hsel

private theorem last_row_not_round
    (air : C FBB ExtF)
    (hc : blockHasherConstraints air) :
    is_round_row air (Circuit.last_row air) = 0 := by
  rcases hc (Circuit.last_row air) with ⟨hf_last, _, _, _, _, _, _⟩
  have hpad : padding_flag air (Circuit.last_row air) = 1 := last_row_padding air hc
  have hsum : is_round_row air (Circuit.last_row air) +
      is_digest_row air (Circuit.last_row air) = 0 := by
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

/-- Base case: row `x` has selector `0` and is a round row. -/
theorem block_round_rows_base (air : C FBB ExtF) (x : ℕ)
    (hf : flag_constraints air x)
    (hsel : encoder_selector_idx air x = 0) :
    encoder_selector_idx air x = 0 ∧
    is_round_row air x = 1 ∧
    is_digest_row air x = 0 := by
  have hround : is_round_row air x = 1 := (selector_zero_implies_round air x hf hsel).1
  have hdigest_not_one : is_digest_row air x ≠ 1 := by
    intro hdigest
    have : encoder_selector_idx air x = 20 := (is_digest_iff_selector_eq_20 air x hf).mp hdigest
    have : (0 : FBB) = 20 := by simpa [hsel] using this.symm
    exact (by decide : (0 : FBB) ≠ 20) this
  rcases is_digest_row_boolean air x hf with hdigest0 | hdigest1
  · exact ⟨hsel, hround, hdigest0⟩
  · exact False.elim (hdigest_not_one hdigest1)

/-- Inductive step: a supported round row advances the selector by one and
    stays in the round region. -/
theorem block_round_rows_step_of_lt_last_row (air : C FBB ExtF) (x offset : ℕ)
    (hoffset : offset < 19)
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
    (is_round_iff_selector_lt_20 air (x + offset + 1) hf_next).2
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
    (hoffset : offset < 19)
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
  exact block_round_rows_step_of_lt_last_row air x offset hoffset hrow hrot
    hf_curr hf_next ht ih_sel ih_round

/-- By induction: rows `x .. x + 19` are round rows with selector `offset`. -/
theorem block_round_rows (air : C FBB ExtF) (x : ℕ) (offset : ℕ)
    (hoffset : offset < 20)
    (hwindow : blockWindowSupported air x)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hsel : encoder_selector_idx air x = 0) :
    encoder_selector_idx air (x + offset) = (offset : FBB) ∧
    is_round_row air (x + offset) = 1 ∧
    is_digest_row air (x + offset) = 0 := by
  induction offset with
  | zero =>
      rcases hc x with ⟨hf, _, _, _, _, _, _⟩
      simpa using block_round_rows_base air x hf hsel
  | succ offset ih =>
      have hoffset_prev : offset < 20 := by
        omega
      have hoffset_step : offset < 19 := by
        omega
      rcases ih hoffset_prev with ⟨ih_sel, ih_round, _⟩
      rcases hc (x + offset) with ⟨hf_curr, _, ht, _, _, _, _⟩
      rcases hc (x + offset + 1) with ⟨hf_next, _, _, _, _, _, _⟩
      simpa [Nat.add_assoc] using
        block_round_rows_step air x offset hoffset_step hwindow hrot hf_curr hf_next ht
          ih_sel ih_round

/-- Starting from any supported row with `encoder_selector_idx = 0`, the
    constraints force the first 20 rows of the block window to be round rows. -/
theorem block_round_rows_of_start_le (air : C FBB ExtF) (x : ℕ) (offset : ℕ)
    (hoffset : offset < 20)
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
      rcases hc x with ⟨hf, _, _, _, _, _, _⟩
      rcases block_round_rows_base air x hf hsel with ⟨hsel0, hround, hdigest⟩
      exact ⟨hsel0, hround, hdigest, hx⟩
  | succ offset ih =>
      have hoffset_prev : offset < 20 := by omega
      have hoffset_step : offset < 19 := by omega
      rcases ih hoffset_prev with ⟨ih_sel, ih_round, _, ih_valid⟩
      rcases hc (x + offset) with ⟨hf_curr, _, ht, _, _, _, _⟩
      rcases hc (x + offset + 1) with ⟨hf_next, _, _, _, _, _, _⟩
      have hcurr_lt : x + offset < Circuit.last_row air :=
        real_row_lt_last_row air (x + offset) hc ih_valid (Or.inl ih_round)
      rcases block_round_rows_step_of_lt_last_row air x offset hoffset_step hcurr_lt hrot
          hf_curr hf_next ht ih_sel ih_round with ⟨hsel_next, hround_next, hdigest_next⟩
      exact ⟨hsel_next, hround_next, hdigest_next, by omega⟩

/-- Once `start` is known to be an actual trace row, `encoder_selector_idx = 0`
    forces the full 21-row SHA-512 block window to fit before `last_row`. -/
theorem blockWindowSupported_of_start_le (air : C FBB ExtF) (x : ℕ)
    (hx : x ≤ Circuit.last_row air)
    (hsel : encoder_selector_idx air x = 0)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    blockWindowSupported air x := by
  rcases block_round_rows_of_start_le air x 19 (by omega) hx hrot hc hsel with
    ⟨_, hround19, _, hvalid19⟩
  have hlt19 : x + 19 < Circuit.last_row air :=
    real_row_lt_last_row air (x + 19) hc hvalid19 (Or.inl hround19)
  dsimp [blockWindowSupported]
  omega

/-- Row `x + 20` is the digest row of the block window. -/
theorem block_digest_row (air : C FBB ExtF) (x : ℕ)
    (hwindow : blockWindowSupported air x)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hsel : encoder_selector_idx air x = 0) :
    encoder_selector_idx air (x + 20) = 20 ∧
    is_round_row air (x + 20) = 0 ∧
    is_digest_row air (x + 20) = 1 := by
  have hrow : x + 19 < Circuit.last_row air := by
    dsimp [blockWindowSupported] at hwindow
    omega
  rcases block_round_rows air x 19 (by omega) hwindow hrot hc hsel with
    ⟨hsel19, hround19, _⟩
  rcases hc (x + 19) with ⟨hf19, _, ht19, _, _, _, _⟩
  rcases hc (x + 20) with ⟨hf20, _, _, _, _, _, _⟩
  have hsel20 : encoder_selector_idx air (x + 20) = 20 := by
    have hstep := round_row_idx_increments air (x + 19) hrow hrot ht19 hf19 hround19
    simpa [nextRow, hrow.ne, hsel19, Nat.cast_add] using hstep
  have hdigest20 : is_digest_row air (x + 20) = 1 :=
    (is_digest_iff_selector_eq_20 air (x + 20) hf20).2 hsel20
  have hround20 : is_round_row air (x + 20) = 0 := by
    rcases is_round_row_boolean air (x + 20) hf20 with hround0 | hround1
    · exact hround0
    · rcases round_plus_digest_boolean air (x + 20) hf20 with hsum0 | hsum1
      · have : (2 : FBB) = 0 := by simpa [hround1, hdigest20] using hsum0
        exact False.elim ((by decide : (2 : FBB) ≠ 0) this)
      · have : (2 : FBB) = 1 := by simpa [hround1, hdigest20] using hsum1
        exact False.elim ((by decide : (2 : FBB) ≠ 1) this)
  exact ⟨hsel20, hround20, hdigest20⟩

/-- The previous row (with wrap-around) is a digest or padding row. -/
theorem block_prev_row (air : C FBB ExtF) (x : ℕ)
    (hwindow : blockWindowSupported air x)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hsel : encoder_selector_idx air x = 0) :
    encoder_selector_idx air (prevRow air x) = 20 ∨
    encoder_selector_idx air (prevRow air x) = 21 := by
  by_cases hx0 : x = 0
  · rcases hc (Circuit.last_row air) with ⟨hf_last, _, _, _, _, _, _⟩
    have hround_last0 := last_row_not_round air hc
    have hdigest_last0 := last_row_not_digest air hc
    have hsel21 :=
      selector_eq_21_of_not_round_or_digest air (Circuit.last_row air) hf_last
        hround_last0 hdigest_last0
    exact Or.inr (by simpa [prevRow, hx0] using hsel21)
  · have hx_pos : 0 < x := Nat.pos_of_ne_zero hx0
    have hprev : x - 1 < Circuit.last_row air := by
      dsimp [blockWindowSupported] at hwindow
      omega
    have hnextrow : nextRow air (x - 1) = x := by
      have hsub : x - 1 + 1 = x := Nat.sub_add_cancel (Nat.succ_le_of_lt hx_pos)
      simp [nextRow, hprev.ne, hsub]
    rcases hc (x - 1) with ⟨hf_prev, _, ht_prev, _, _, _, _⟩
    rcases hc x with ⟨hf_x, _, _, _, _, _, _⟩
    rcases block_round_rows_base air x hf_x hsel with ⟨hsel_x, hround_x, hdigest_x⟩
    rcases ht_prev with ⟨_, _, _, _, h533, _, _, _, _, _, _⟩
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
          is_round_row air (x - 1) +
          (((is_digest_row air (x - 1) * next_is_round_row air (x - 1)) * 20) * 2013265920) +
          is_digest_row air (x - 1) * next_padding_flag air (x - 1) -
          next_encoder_selector_idx air (x - 1) = 0 := by
      have := (constraint_533_eq_selector_transition air (x - 1)).mp h533
      simpa [Circuit.isTransitionRow, hprev.ne] using this
    rcases is_digest_row_boolean air (x - 1) hf_prev with hdigest_prev0 | hdigest_prev1
    · rcases is_round_row_boolean air (x - 1) hf_prev with hround_prev0 | hround_prev1
      · have hsel21 :=
          selector_eq_21_of_not_round_or_digest air (x - 1) hf_prev hround_prev0 hdigest_prev0
        exact Or.inr (by simpa [prevRow, hx0] using hsel21)
      · have hbad : encoder_selector_idx air (x - 1) + 1 = 0 := by
          rw [hround_prev1, hdigest_prev0, hnext_pad, hnext_sel] at htrans
          simpa [hnext_round, add_assoc, add_left_comm, add_comm] using htrans
        rcases (is_round_iff_selector_lt_20 air (x - 1) hf_prev).mp hround_prev1 with
          ⟨n, hn, hseln⟩
        have hnat : (((n + 1 : ℕ)) : FBB) = 0 := by
          simpa [hseln, Nat.cast_add] using hbad
        have hneq_zero : (((n + 1 : ℕ)) : FBB) ≠ 0 := by
          intro hzero
          revert hzero
          interval_cases n <;> intro hzero <;> norm_num at hzero <;> contradiction
        exact False.elim (hneq_zero hnat)
    · have hsel20 : encoder_selector_idx air (x - 1) = 20 :=
        (is_digest_iff_selector_eq_20 air (x - 1) hf_prev).mp hdigest_prev1
      exact Or.inl (by simpa [prevRow, hx0] using hsel20)

/-- Full block-window shape, assembled from the preceding lemmas. -/
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

end Sha2BlockHasherVmAir_sha512.BlockSpec
