/-
  Chi state equality and exported lane theorems for the KeccakfPermAir
  single-round correctness proof.

  Imports ChiFacts (helpers, definitions) and ChiBridge (constraint bridges)
  to prove the main theorem: chiOutputState = χ(ρπ(aPrimeState)).

  Exports:
  • `chi_preiota_lane_zero` — pre-iota lane [0][0]
  • `chi_nonzero_lanes` — all nonzero output lanes
-/
import VmExtensions.Soundness.KeccakfPermAir.Round.ChiHelpers
import VmExtensions.Soundness.KeccakfPermAir.Round.ChiBridge

set_option autoImplicit false
set_option linter.all false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints
open KeccakfPermAir.StepLimbs
open Keccak

/-! ## Main chi state equality -/

-- Chi output state identity: a_prime_prime columns = χ(ρπ(aPrimeState)).
-- Both sides are determined by their bits. For each bit, the chi
-- constraint (bridged via chi_canonical_of_chi) gives the recomposition,
-- fieldToU16_getLsbD_fbbToBool extracts the bit, fbbToBool_chi converts
-- to boolean chi, and the column mapping matches rho_pi_bits via chiIdx.
set_option maxHeartbeats 6400000 in
theorem chi_output_state_eq
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) :
    chiOutputState air row = χ (ρπ (aPrimeState air row)) := by
  -- Rewrite RHS to bitsToState form
  rw [chi_rho_pi_aPrime]
  -- Both sides are Arr25, equal iff all 25 elements match
  apply Subtype.ext; apply Array.ext
  · simp [chiOutputState, bitsToState]
  · intro i h1 h2
    simp only [chiOutputState, bitsToState, Array.getElem_ofFn]
    -- Both sides are UInt64, equal iff all 64 bits match.
    have hi : i < 25 := by simp [chiOutputState] at h1; exact h1
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro k hk
    -- Convert to getBit form
    rw [show (laneOfLimbs _ _ _ _).toBitVec.getLsbD k =
        getBit (laneOfLimbs _ _ _ _) ⟨k, hk⟩ from rfl,
        show (bitsToU64 _).toBitVec.getLsbD k =
        getBit (bitsToU64 _) ⟨k, hk⟩ from rfl]
    -- RHS: getBit(bitsToU64(f), k) = f(k) by getBit_bitsToU64
    rw [getBit_bitsToU64]
    -- LHS: getBit(laneOfLimbs(...), k) decomposes by limb
    rw [getBit_laneOfLimbs]
    -- Determine which limb (n = 4*i + k/16) and bit position (j = k%16) within that limb.
    -- Get the chi constraint for limb n from the bridge.
    -- The a_prime_bit values are boolean (from h_round).
    have hbool : ∀ idx, idx < 1600 →
        a_prime_bit air idx row = 0 ∨ a_prime_bit air idx row = 1 :=
      fun idx hidx => a_prime_bit_is_bool h_round idx hidx
    -- Helper: for each limb L, prove the bit identity
    suffices hLimb : ∀ (L : Fin 4) (j : Fin 16),
        (fieldToU16 (a_prime_prime air (4 * i + L.val) row)).toUInt64.toBitVec.getLsbD j.val =
        chi_bits (rho_pi_bits (aPrimeStateBits air row))
          ⟨i % 5, by omega⟩ ⟨i / 5, by omega⟩ ⟨16 * L.val + j.val, by omega⟩ by
      -- Dispatch the 4-way if to the right limb
      by_cases h16 : k < 16
      · simp only [h16, ite_true, show k < 32 from by omega, show k < 48 from by omega]
        rw [u16_toBitVec_eq_toU64_toBitVec _ k h16]
        have := hLimb ⟨0, by omega⟩ ⟨k, h16⟩
        simp only [show 4 * i + 0 = 4 * i from by omega, show 16 * 0 + k = k from by omega] at this
        exact this
      · by_cases h32 : k < 32
        · simp only [h16, ite_false, h32, ite_true, show k < 48 from by omega]
          rw [u16_toBitVec_eq_toU64_toBitVec _ (k - 16) (by omega)]
          have := hLimb ⟨1, by omega⟩ ⟨k - 16, by omega⟩
          simp only [show 16 * 1 + (k - 16) = k from by omega] at this; exact this
        · by_cases h48 : k < 48
          · simp only [h16, ite_false, h32, h48, ite_true]
            rw [u16_toBitVec_eq_toU64_toBitVec _ (k - 32) (by omega)]
            have := hLimb ⟨2, by omega⟩ ⟨k - 32, by omega⟩
            simp only [show 16 * 2 + (k - 32) = k from by omega] at this; exact this
          · simp only [h16, ite_false, h32, h48]
            rw [u16_toBitVec_eq_toU64_toBitVec _ (k - 48) (by omega)]
            have := hLimb ⟨3, by omega⟩ ⟨k - 48, by omega⟩
            simp only [show 16 * 3 + (k - 48) = k from by omega] at this; exact this
    -- Prove hLimb: for each limb L and bit j within it
    intro L j
    have hn : 4 * i + L.val < 100 := by omega
    -- Get the chi constraint for this limb
    have hc := chi_canonical_of_chi h_round.chi ⟨4 * i + L.val, hn⟩
    -- chiIdx bounds for boolean hypotheses
    have hab : ∀ jj, jj < 16 → chiIdx (4 * i + L.val) jj 0 < 1600 := by
      intro jj hjj; rw [chiIdx_eq_chiAPrimeIdx ⟨4*i+L.val, hn⟩ ⟨jj, hjj⟩ ⟨0, by omega⟩]
      simp only [chiAPrimeIdx, rotNat]; omega
    have hbb : ∀ jj, jj < 16 → chiIdx (4 * i + L.val) jj 1 < 1600 := by
      intro jj hjj; rw [chiIdx_eq_chiAPrimeIdx ⟨4*i+L.val, hn⟩ ⟨jj, hjj⟩ ⟨1, by omega⟩]
      simp only [chiAPrimeIdx, rotNat]; omega
    have hdb : ∀ jj, jj < 16 → chiIdx (4 * i + L.val) jj 2 < 1600 := by
      intro jj hjj; rw [chiIdx_eq_chiAPrimeIdx ⟨4*i+L.val, hn⟩ ⟨jj, hjj⟩ ⟨2, by omega⟩]
      simp only [chiAPrimeIdx, rotNat]; omega
    -- Extract per-bit from constraint
    rw [chi_bit_extraction hc hbool j.val j.isLt hab hbb hdb]
    -- Convert field chi to bool chi
    rw [fbbToBool_chi (hbool _ (hab j.val j.isLt)) (hbool _ (hbb j.val j.isLt))
        (hbool _ (hdb j.val j.isLt))]
    -- Unfold chi_bits on the RHS
    simp only [chi_bits]
    -- Match the three fbbToBool(a_prime_bit[chiIdx...]) with rho_pi_bits(S)
    rw [fbbToBool_a_prime_bit_chiIdx_eq_rho_pi_bits air row i hi L j ⟨0, by omega⟩ hn,
        fbbToBool_a_prime_bit_chiIdx_eq_rho_pi_bits air row i hi L j ⟨1, by omega⟩ hn,
        fbbToBool_a_prime_bit_chiIdx_eq_rho_pi_bits air row i hi L j ⟨2, by omega⟩ hn]
    -- Both sides now have the same structure
    -- Simplify i%5%5 → i%5
    congr 2 <;> ext <;> simp <;> omega

/-! ## Exported lane theorems -/

/-- Pre-iota lane [0][0]: the first lane of the chi output equals
    the corresponding lane of `χ(ρπ(θ(rowInputState)))`. -/
theorem chi_preiota_lane_zero
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) :
    (chiOutputState air row)[0]'(by omega) =
    (χ (ρπ (θ (rowInputState air row))))[0]'(by omega) := by
  have h1 := chi_output_state_eq h_round
  have h2 := theta_output_state h_round
  rw [← h2]
  exact congrArg (fun st => st[0]'(by omega)) h1

/-- All nonzero lanes: for `i ≠ 0`, `rowOutputState[i] = (χ(ρπ(θ(input))))[i]`. -/
theorem chi_nonzero_lanes
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row)
    (i : Fin 25) (hi : i.val ≠ 0) :
    (rowOutputState air row)[i.val]'(by omega) =
    (χ (ρπ (θ (rowInputState air row))))[i.val]'(by omega) := by
  rw [rowOutputState_lane_nonzero air row i hi]
  have h1 := chi_output_state_eq h_round
  have h2 := theta_output_state h_round
  rw [← h2]
  rw [← congrArg (fun st => st[i.val]'(by omega)) h1]
  exact (chiOutputState_lane air row i).symm

end KeccakfPermAir.Soundness
