/-
  Layer C: Round Step State Bridge

  Combines the A-state and E-state semantic bridges into a single file.
  Proves that field-level A and E updates match the UInt32 SHA-256 roundStep spec.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.RoundStep.AUpdate
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.RoundStep.EUpdate

set_option autoImplicit false

set_option maxHeartbeats 10000000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

def roundStepA_hNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (concatEBitsWord air row slot)).val +
    (composeHi16 (concatEBitsWord air row slot)).val * 2 ^ 16

def roundStepA_sigma1Nat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))).val +
    (composeHi16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))).val * 2 ^ 16

def roundStepA_chNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
    (concatEBitsWord air row (slot + 2))
    (concatEBitsWord air row (slot + 1)))).val +
    (composeHi16 (fieldCh (concatEBitsWord air row (slot + 3))
      (concatEBitsWord air row (slot + 2))
      (concatEBitsWord air row (slot + 1)))).val * 2 ^ 16

def roundStepA_kNat (row_idx slot : ℕ) : ℕ :=
  (k_limb_at row_idx slot 0).val + (k_limb_at row_idx slot 1).val * 2 ^ 16

def roundStepA_schedNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (scheduleBitsWord air (nextRow air row) slot)).val +
    (composeHi16 (scheduleBitsWord air (nextRow air row) slot)).val * 2 ^ 16

def roundStepA_sigma0Nat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (fieldBigSigma0 (concatABitsWord air row (slot + 3)))).val +
    (composeHi16 (fieldBigSigma0 (concatABitsWord air row (slot + 3)))).val * 2 ^ 16

def roundStepA_majNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (fieldMaj (concatABitsWord air row (slot + 3))
    (concatABitsWord air row (slot + 2))
    (concatABitsWord air row (slot + 1)))).val +
    (composeHi16 (fieldMaj (concatABitsWord air row (slot + 3))
      (concatABitsWord air row (slot + 2))
      (concatABitsWord air row (slot + 1)))).val * 2 ^ 16

def roundStepA_resultNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (aBitsWord air (nextRow air row) slot)).val +
    (composeHi16 (aBitsWord air (nextRow air row) slot)).val * 2 ^ 16

def roundStepA_sumWord (air : C FBB ExtF) (row slot row_idx : ℕ) : UInt32 :=
  ((((((roundStepA_hNat air row slot).toUInt32 +
        (roundStepA_sigma1Nat air row slot).toUInt32) +
        (roundStepA_chNat air row slot).toUInt32) +
        (roundStepA_kNat row_idx slot).toUInt32) +
        (roundStepA_schedNat air row slot).toUInt32) +
        (roundStepA_sigma0Nat air row slot).toUInt32) +
        (roundStepA_majNat air row slot).toUInt32

theorem round_step_a_rhs_eq_sum (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hidx_bound : row_idx < 16)
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    (roundStep (slotInputState air row slot)
      (sha256K[row_idx * 4 + slot]!)
      (scheduleWordAtRow air (nextRow air row) slot)).a =
      roundStepA_sumWord air row slot row_idx := by
  have hslot0 : slot < 8 := by omega
  have hslot1 : slot + 1 < 8 := by omega
  have hslot2 : slot + 2 < 8 := by omega
  have hslot3 : slot + 3 < 8 := by omega
  have hh_bits : isBitsWord (concatEBitsWord air row slot) :=
    concatEBits_boolean air row slot hslot0 hbb hbb_next
  have he_bits : isBitsWord (concatEBitsWord air row (slot + 3)) :=
    concatEBits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hf_bits : isBitsWord (concatEBitsWord air row (slot + 2)) :=
    concatEBits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hg_bits : isBitsWord (concatEBitsWord air row (slot + 1)) :=
    concatEBits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have ha_bits : isBitsWord (concatABitsWord air row (slot + 3)) :=
    concatABits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hb_bits : isBitsWord (concatABitsWord air row (slot + 2)) :=
    concatABits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hc_bits : isBitsWord (concatABitsWord air row (slot + 1)) :=
    concatABits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have hsig1_bits :
      isBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) :=
    fieldBigSigma1_isBitsWord _ he_bits
  have hch_bits :
      isBitsWord (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))) :=
    fieldCh_isBitsWord _ _ _ he_bits hf_bits hg_bits
  have hsig0_bits :
      isBitsWord (fieldBigSigma0 (concatABitsWord air row (slot + 3))) :=
    fieldBigSigma0_isBitsWord _ ha_bits
  have hmaj_bits :
      isBitsWord (fieldMaj (concatABitsWord air row (slot + 3))
        (concatABitsWord air row (slot + 2))
        (concatABitsWord air row (slot + 1))) :=
    fieldMaj_isBitsWord _ _ _ ha_bits hb_bits hc_bits
  have hh_word :
      concatEWord air row slot = (roundStepA_hNat air row slot).toUInt32 := by
    rw [concatEWord_eq_bitsWordToUInt32 air row slot hslot0 hbb hbb_next]
    simpa [roundStepA_hNat] using
      bitsWordToUInt32_eq_compose16 (concatEBitsWord air row slot) hh_bits
  have hsig1_word :
      bigSigma1 (concatEWord air row (slot + 3)) = (roundStepA_sigma1Nat air row slot).toUInt32 := by
    calc
      bigSigma1 (concatEWord air row (slot + 3))
          = bigSigma1 (bitsWordToUInt32 (concatEBitsWord air row (slot + 3))) := by
              rw [concatEWord_eq_bitsWordToUInt32 air row (slot + 3) hslot3 hbb hbb_next]
      _ = bitsWordToUInt32 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) := by
            rw [(fieldBigSigma1_eq_bigSigma1 (concatEBitsWord air row (slot + 3)) he_bits).symm]
      _ = (roundStepA_sigma1Nat air row slot).toUInt32 := by
            simpa [roundStepA_sigma1Nat] using bitsWordToUInt32_eq_compose16
              (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) hsig1_bits
  have hch_word :
      ch (concatEWord air row (slot + 3))
        (concatEWord air row (slot + 2))
        (concatEWord air row (slot + 1)) = (roundStepA_chNat air row slot).toUInt32 := by
    calc
      ch (concatEWord air row (slot + 3))
            (concatEWord air row (slot + 2))
            (concatEWord air row (slot + 1))
          = ch (bitsWordToUInt32 (concatEBitsWord air row (slot + 3)))
              (bitsWordToUInt32 (concatEBitsWord air row (slot + 2)))
              (bitsWordToUInt32 (concatEBitsWord air row (slot + 1))) := by
                rw [concatEWord_eq_bitsWordToUInt32 air row (slot + 3) hslot3 hbb hbb_next,
                  concatEWord_eq_bitsWordToUInt32 air row (slot + 2) hslot2 hbb hbb_next,
                  concatEWord_eq_bitsWordToUInt32 air row (slot + 1) hslot1 hbb hbb_next]
      _ = bitsWordToUInt32
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) := by
            symm
            exact fieldCh_eq_ch _ _ _ he_bits hf_bits hg_bits
      _ = (roundStepA_chNat air row slot).toUInt32 := by
            simpa [roundStepA_chNat] using bitsWordToUInt32_eq_compose16
              (fieldCh (concatEBitsWord air row (slot + 3))
                (concatEBitsWord air row (slot + 2))
                (concatEBitsWord air row (slot + 1))) hch_bits
  have hk_word :
      sha256K[row_idx * 4 + slot]! = (roundStepA_kNat row_idx slot).toUInt32 := by
    simpa [roundStepA_kNat] using k_word_eq_limbs row_idx slot hidx_bound hslot
  have hsched_word :
      scheduleWordAtRow air (nextRow air row) slot = (roundStepA_schedNat air row slot).toUInt32 := by
    rw [scheduleWordAtRow_eq_bitsWordToUInt32]
    simpa [roundStepA_schedNat] using bitsWordToUInt32_eq_compose16
      (scheduleBitsWord air (nextRow air row) slot) hsched_bits
  have hsig0_word :
      bigSigma0 (concatAWord air row (slot + 3)) = (roundStepA_sigma0Nat air row slot).toUInt32 := by
    calc
      bigSigma0 (concatAWord air row (slot + 3))
          = bigSigma0 (bitsWordToUInt32 (concatABitsWord air row (slot + 3))) := by
              rw [concatAWord_eq_bitsWordToUInt32 air row (slot + 3) hslot3 hbb hbb_next]
      _ = bitsWordToUInt32 (fieldBigSigma0 (concatABitsWord air row (slot + 3))) := by
            rw [(fieldBigSigma0_eq_bigSigma0 (concatABitsWord air row (slot + 3)) ha_bits).symm]
      _ = (roundStepA_sigma0Nat air row slot).toUInt32 := by
            simpa [roundStepA_sigma0Nat] using bitsWordToUInt32_eq_compose16
              (fieldBigSigma0 (concatABitsWord air row (slot + 3))) hsig0_bits
  have hmaj_word :
      maj (concatAWord air row (slot + 3))
        (concatAWord air row (slot + 2))
        (concatAWord air row (slot + 1)) = (roundStepA_majNat air row slot).toUInt32 := by
    calc
      maj (concatAWord air row (slot + 3))
            (concatAWord air row (slot + 2))
            (concatAWord air row (slot + 1))
          = maj (bitsWordToUInt32 (concatABitsWord air row (slot + 3)))
              (bitsWordToUInt32 (concatABitsWord air row (slot + 2)))
              (bitsWordToUInt32 (concatABitsWord air row (slot + 1))) := by
                rw [concatAWord_eq_bitsWordToUInt32 air row (slot + 3) hslot3 hbb hbb_next,
                  concatAWord_eq_bitsWordToUInt32 air row (slot + 2) hslot2 hbb hbb_next,
                  concatAWord_eq_bitsWordToUInt32 air row (slot + 1) hslot1 hbb hbb_next]
      _ = bitsWordToUInt32
            (fieldMaj (concatABitsWord air row (slot + 3))
              (concatABitsWord air row (slot + 2))
              (concatABitsWord air row (slot + 1))) := by
            symm
            exact fieldMaj_eq_maj _ _ _ ha_bits hb_bits hc_bits
      _ = (roundStepA_majNat air row slot).toUInt32 := by
            simpa [roundStepA_majNat] using bitsWordToUInt32_eq_compose16
              (fieldMaj (concatABitsWord air row (slot + 3))
                (concatABitsWord air row (slot + 2))
                (concatABitsWord air row (slot + 1))) hmaj_bits
  dsimp [roundStep, slotInputState, roundStepA_sumWord]
  rw [hh_word, hsig1_word, hch_word, hk_word, hsched_word, hsig0_word, hmaj_word]
  simp [add_assoc]

theorem round_step_a_sum_eq_result (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row))
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    roundStepA_sumWord air row slot row_idx =
      (roundStepA_resultNat air row slot).toUInt32 := by
  have hslot0 : slot < 8 := by omega
  have hslot1 : slot + 1 < 8 := by omega
  have hslot2 : slot + 2 < 8 := by omega
  have hslot3 : slot + 3 < 8 := by omega
  have hh_bits : isBitsWord (concatEBitsWord air row slot) :=
    concatEBits_boolean air row slot hslot0 hbb hbb_next
  have he_bits : isBitsWord (concatEBitsWord air row (slot + 3)) :=
    concatEBits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hf_bits : isBitsWord (concatEBitsWord air row (slot + 2)) :=
    concatEBits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hg_bits : isBitsWord (concatEBitsWord air row (slot + 1)) :=
    concatEBits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have ha_bits : isBitsWord (concatABitsWord air row (slot + 3)) :=
    concatABits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hb_bits : isBitsWord (concatABitsWord air row (slot + 2)) :=
    concatABits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hc_bits : isBitsWord (concatABitsWord air row (slot + 1)) :=
    concatABits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have hsig1_bits :
      isBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) :=
    fieldBigSigma1_isBitsWord _ he_bits
  have hch_bits :
      isBitsWord (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))) :=
    fieldCh_isBitsWord _ _ _ he_bits hf_bits hg_bits
  have hsig0_bits :
      isBitsWord (fieldBigSigma0 (concatABitsWord air row (slot + 3))) :=
    fieldBigSigma0_isBitsWord _ ha_bits
  have hmaj_bits :
      isBitsWord (fieldMaj (concatABitsWord air row (slot + 3))
        (concatABitsWord air row (slot + 2))
        (concatABitsWord air row (slot + 1))) :=
    fieldMaj_isBitsWord _ _ _ ha_bits hb_bits hc_bits
  have hnext_a_bits : isBitsWord (aBitsWord air (nextRow air row) slot) := by
    intro i
    exact hbb_next.1 slot i.val hslot i.isLt
  have hlo_eq := round_step_a_lo_eq air row slot row_idx hslot hrow hrot hrs hbb hbb_next
    hround_next hflags_next hidx hidx_bound
  have hhi_eq := round_step_a_hi_eq air row slot row_idx hslot hrow hrot hrs hbb hbb_next
    hround_next hflags_next hidx hidx_bound
  have hh_lo_lt : (composeLo16 (concatEBitsWord air row slot)).val < 2 ^ 16 :=
    composeLo16_val_lt _ hh_bits
  have hh_hi_lt : (composeHi16 (concatEBitsWord air row slot)).val < 2 ^ 16 :=
    composeHi16_val_lt _ hh_bits
  have hsig1_lo_lt :
      (composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))).val < 2 ^ 16 :=
    composeLo16_val_lt _ hsig1_bits
  have hsig1_hi_lt :
      (composeHi16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))).val < 2 ^ 16 :=
    composeHi16_val_lt _ hsig1_bits
  have hch_lo_lt :
      (composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1)))).val < 2 ^ 16 :=
    composeLo16_val_lt _ hch_bits
  have hch_hi_lt :
      (composeHi16 (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1)))).val < 2 ^ 16 :=
    composeHi16_val_lt _ hch_bits
  have hsig0_lo_lt :
      (composeLo16 (fieldBigSigma0 (concatABitsWord air row (slot + 3)))).val < 2 ^ 16 :=
    composeLo16_val_lt _ hsig0_bits
  have hsig0_hi_lt :
      (composeHi16 (fieldBigSigma0 (concatABitsWord air row (slot + 3)))).val < 2 ^ 16 :=
    composeHi16_val_lt _ hsig0_bits
  have hmaj_lo_lt :
      (composeLo16 (fieldMaj (concatABitsWord air row (slot + 3))
        (concatABitsWord air row (slot + 2))
        (concatABitsWord air row (slot + 1)))).val < 2 ^ 16 :=
    composeLo16_val_lt _ hmaj_bits
  have hmaj_hi_lt :
      (composeHi16 (fieldMaj (concatABitsWord air row (slot + 3))
        (concatABitsWord air row (slot + 2))
        (concatABitsWord air row (slot + 1)))).val < 2 ^ 16 :=
    composeHi16_val_lt _ hmaj_bits
  have hk_lo_lt : (k_limb_at row_idx slot 0).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 0 hidx_bound hslot (by omega)
  have hk_hi_lt : (k_limb_at row_idx slot 1).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 1 hidx_bound hslot (by omega)
  have hsched_lo_lt :
      (composeLo16 (scheduleBitsWord air (nextRow air row) slot)).val < 2 ^ 16 :=
    composeLo16_val_lt _ hsched_bits
  have hsched_hi_lt :
      (composeHi16 (scheduleBitsWord air (nextRow air row) slot)).val < 2 ^ 16 :=
    composeHi16_val_lt _ hsched_bits
  have hres_lo_lt :
      (composeLo16 (aBitsWord air (nextRow air row) slot)).val < 2 ^ 16 :=
    composeLo16_val_lt _ hnext_a_bits
  have hres_hi_lt :
      (composeHi16 (aBitsWord air (nextRow air row) slot)).val < 2 ^ 16 :=
    composeHi16_val_lt _ hnext_a_bits
  have hcarry_lo_lt : (next_carry_a air slot 0 row).val < 2 ^ 8 := by
    simpa [next_carry_a_eq_nextRow air hrot slot 0 row hrow] using
      (hcarry_next slot 0 hslot (by omega)).1
  have hcarry_hi_lt : (next_carry_a air slot 1 row).val < 2 ^ 8 := by
    simpa [next_carry_a_eq_nextRow air hrot slot 1 row hrow] using
      (hcarry_next slot 1 hslot (by omega)).1
  have hbounds :
      ∀ x ∈ [composeLo16 (concatEBitsWord air row slot),
             composeHi16 (concatEBitsWord air row slot),
             composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))),
             composeHi16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))),
             composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
               (concatEBitsWord air row (slot + 2))
               (concatEBitsWord air row (slot + 1))),
             composeHi16 (fieldCh (concatEBitsWord air row (slot + 3))
               (concatEBitsWord air row (slot + 2))
               (concatEBitsWord air row (slot + 1))),
             k_limb_at row_idx slot 0, k_limb_at row_idx slot 1,
             composeLo16 (scheduleBitsWord air (nextRow air row) slot),
             composeHi16 (scheduleBitsWord air (nextRow air row) slot),
             composeLo16 (fieldBigSigma0 (concatABitsWord air row (slot + 3))),
             composeHi16 (fieldBigSigma0 (concatABitsWord air row (slot + 3))),
             composeLo16 (fieldMaj (concatABitsWord air row (slot + 3))
               (concatABitsWord air row (slot + 2))
               (concatABitsWord air row (slot + 1))),
             composeHi16 (fieldMaj (concatABitsWord air row (slot + 3))
               (concatABitsWord air row (slot + 2))
               (concatABitsWord air row (slot + 1)))], x.val < 2 ^ 16 := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hh_lo_lt
    · exact hh_hi_lt
    · exact hsig1_lo_lt
    · exact hsig1_hi_lt
    · exact hch_lo_lt
    · exact hch_hi_lt
    · exact hk_lo_lt
    · exact hk_hi_lt
    · exact hsched_lo_lt
    · exact hsched_hi_lt
    · exact hsig0_lo_lt
    · exact hsig0_hi_lt
    · exact hmaj_lo_lt
    · exact hmaj_hi_lt
  simpa [roundStepA_sumWord, roundStepA_hNat, roundStepA_sigma1Nat, roundStepA_chNat,
    roundStepA_kNat, roundStepA_schedNat, roundStepA_sigma0Nat, roundStepA_majNat,
    roundStepA_resultNat] using
    (limbed_addition_seven_uint32
      (composeLo16 (concatEBitsWord air row slot))
      (composeHi16 (concatEBitsWord air row slot))
      (composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))))
      (composeHi16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))))
      (composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))))
      (composeHi16 (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))))
      (k_limb_at row_idx slot 0)
      (k_limb_at row_idx slot 1)
      (composeLo16 (scheduleBitsWord air (nextRow air row) slot))
      (composeHi16 (scheduleBitsWord air (nextRow air row) slot))
      (composeLo16 (fieldBigSigma0 (concatABitsWord air row (slot + 3))))
      (composeHi16 (fieldBigSigma0 (concatABitsWord air row (slot + 3))))
      (composeLo16 (fieldMaj (concatABitsWord air row (slot + 3))
        (concatABitsWord air row (slot + 2))
        (concatABitsWord air row (slot + 1))))
      (composeHi16 (fieldMaj (concatABitsWord air row (slot + 3))
        (concatABitsWord air row (slot + 2))
        (concatABitsWord air row (slot + 1))))
      (composeLo16 (aBitsWord air (nextRow air row) slot))
      (composeHi16 (aBitsWord air (nextRow air row) slot))
      (next_carry_a air slot 0 row)
      (next_carry_a air slot 1 row)
      hbounds hres_lo_lt hres_hi_lt hcarry_lo_lt hcarry_hi_lt hlo_eq hhi_eq)

/-- A single round step: the new a-word matches roundStep.a. -/
theorem single_round_a_correct (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (row_idx : ℕ)
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row))
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    aWord air (nextRow air row) slot =
      (roundStep (slotInputState air row slot)
        (sha256K[row_idx * 4 + slot]!)
        (scheduleWordAtRow air (nextRow air row) slot)).a := by
  have hnext_a_bits : isBitsWord (aBitsWord air (nextRow air row) slot) := by
    intro i
    exact hbb_next.1 slot i.val hslot i.isLt
  have hres_word :
      aWord air (nextRow air row) slot =
        (roundStepA_resultNat air row slot).toUInt32 := by
    rw [aWord_eq_bitsWordToUInt32]
    simpa [roundStepA_resultNat] using
      bitsWordToUInt32_eq_compose16 (aBitsWord air (nextRow air row) slot) hnext_a_bits
  calc
    aWord air (nextRow air row) slot = (roundStepA_resultNat air row slot).toUInt32 := hres_word
    _ = roundStepA_sumWord air row slot row_idx := by
          symm
          exact round_step_a_sum_eq_result air row slot row_idx hslot hrow hrot hrs hbb hbb_next
            hround_next hflags_next hidx hidx_bound hcarry_next hsched_bits
    _ = (roundStep (slotInputState air row slot)
          (sha256K[row_idx * 4 + slot]!)
          (scheduleWordAtRow air (nextRow air row) slot)).a := by
          symm
          exact round_step_a_rhs_eq_sum air row slot row_idx hslot hbb hbb_next
            hidx_bound hsched_bits

/-! ## E-state semantic bridge (formerly RoundStepEState) -/

def roundStepE_dNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (concatABitsWord air row slot)).val +
    (composeHi16 (concatABitsWord air row slot)).val * 2 ^ 16

def roundStepE_hNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (concatEBitsWord air row slot)).val +
    (composeHi16 (concatEBitsWord air row slot)).val * 2 ^ 16

def roundStepE_sigma1Nat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))).val +
    (composeHi16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))).val * 2 ^ 16

def roundStepE_chNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
    (concatEBitsWord air row (slot + 2))
    (concatEBitsWord air row (slot + 1)))).val +
    (composeHi16 (fieldCh (concatEBitsWord air row (slot + 3))
      (concatEBitsWord air row (slot + 2))
      (concatEBitsWord air row (slot + 1)))).val * 2 ^ 16

def roundStepE_kNat (row_idx slot : ℕ) : ℕ :=
  (k_limb_at row_idx slot 0).val + (k_limb_at row_idx slot 1).val * 2 ^ 16

def roundStepE_schedNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (scheduleBitsWord air (nextRow air row) slot)).val +
    (composeHi16 (scheduleBitsWord air (nextRow air row) slot)).val * 2 ^ 16

def roundStepE_resultNat (air : C FBB ExtF) (row slot : ℕ) : ℕ :=
  (composeLo16 (eBitsWord air (nextRow air row) slot)).val +
    (composeHi16 (eBitsWord air (nextRow air row) slot)).val * 2 ^ 16

def roundStepE_sumWord (air : C FBB ExtF) (row slot row_idx : ℕ) : UInt32 :=
  (((((roundStepE_dNat air row slot).toUInt32 +
      (roundStepE_hNat air row slot).toUInt32) +
      (roundStepE_sigma1Nat air row slot).toUInt32) +
      (roundStepE_chNat air row slot).toUInt32) +
      (roundStepE_kNat row_idx slot).toUInt32) +
      (roundStepE_schedNat air row slot).toUInt32

theorem round_step_e_rhs_eq_sum (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hidx_bound : row_idx < 16)
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    (roundStep (slotInputState air row slot)
      (sha256K[row_idx * 4 + slot]!)
      (scheduleWordAtRow air (nextRow air row) slot)).e =
      roundStepE_sumWord air row slot row_idx := by
  have hslot0 : slot < 8 := by omega
  have hslot1 : slot + 1 < 8 := by omega
  have hslot2 : slot + 2 < 8 := by omega
  have hslot3 : slot + 3 < 8 := by omega
  have hd_bits : isBitsWord (concatABitsWord air row slot) :=
    concatABits_boolean air row slot hslot0 hbb hbb_next
  have hh_bits : isBitsWord (concatEBitsWord air row slot) :=
    concatEBits_boolean air row slot hslot0 hbb hbb_next
  have he_bits : isBitsWord (concatEBitsWord air row (slot + 3)) :=
    concatEBits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hf_bits : isBitsWord (concatEBitsWord air row (slot + 2)) :=
    concatEBits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hg_bits : isBitsWord (concatEBitsWord air row (slot + 1)) :=
    concatEBits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have hsig1_bits :
      isBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) :=
    fieldBigSigma1_isBitsWord _ he_bits
  have hch_bits :
      isBitsWord (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))) :=
    fieldCh_isBitsWord _ _ _ he_bits hf_bits hg_bits
  have hd_word :
      concatAWord air row slot = (roundStepE_dNat air row slot).toUInt32 := by
    rw [concatAWord_eq_bitsWordToUInt32 air row slot hslot0 hbb hbb_next]
    simpa [roundStepE_dNat] using
      bitsWordToUInt32_eq_compose16 (concatABitsWord air row slot) hd_bits
  have hh_word :
      concatEWord air row slot = (roundStepE_hNat air row slot).toUInt32 := by
    rw [concatEWord_eq_bitsWordToUInt32 air row slot hslot0 hbb hbb_next]
    simpa [roundStepE_hNat] using
      bitsWordToUInt32_eq_compose16 (concatEBitsWord air row slot) hh_bits
  have hsig1_word :
      bigSigma1 (concatEWord air row (slot + 3)) = (roundStepE_sigma1Nat air row slot).toUInt32 := by
    calc
      bigSigma1 (concatEWord air row (slot + 3))
          = bigSigma1 (bitsWordToUInt32 (concatEBitsWord air row (slot + 3))) := by
              rw [concatEWord_eq_bitsWordToUInt32 air row (slot + 3) hslot3 hbb hbb_next]
      _ = bitsWordToUInt32 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) := by
            rw [(fieldBigSigma1_eq_bigSigma1 (concatEBitsWord air row (slot + 3)) he_bits).symm]
      _ = (roundStepE_sigma1Nat air row slot).toUInt32 := by
            simpa [roundStepE_sigma1Nat] using bitsWordToUInt32_eq_compose16
              (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) hsig1_bits
  have hch_word :
      ch (concatEWord air row (slot + 3))
        (concatEWord air row (slot + 2))
        (concatEWord air row (slot + 1)) = (roundStepE_chNat air row slot).toUInt32 := by
    calc
      ch (concatEWord air row (slot + 3))
            (concatEWord air row (slot + 2))
            (concatEWord air row (slot + 1))
          = ch (bitsWordToUInt32 (concatEBitsWord air row (slot + 3)))
              (bitsWordToUInt32 (concatEBitsWord air row (slot + 2)))
              (bitsWordToUInt32 (concatEBitsWord air row (slot + 1))) := by
                rw [concatEWord_eq_bitsWordToUInt32 air row (slot + 3) hslot3 hbb hbb_next,
                  concatEWord_eq_bitsWordToUInt32 air row (slot + 2) hslot2 hbb hbb_next,
                  concatEWord_eq_bitsWordToUInt32 air row (slot + 1) hslot1 hbb hbb_next]
      _ = bitsWordToUInt32
            (fieldCh (concatEBitsWord air row (slot + 3))
              (concatEBitsWord air row (slot + 2))
              (concatEBitsWord air row (slot + 1))) := by
            symm
            exact fieldCh_eq_ch _ _ _ he_bits hf_bits hg_bits
      _ = (roundStepE_chNat air row slot).toUInt32 := by
            simpa [roundStepE_chNat] using bitsWordToUInt32_eq_compose16
              (fieldCh (concatEBitsWord air row (slot + 3))
                (concatEBitsWord air row (slot + 2))
                (concatEBitsWord air row (slot + 1))) hch_bits
  have hk_word :
      sha256K[row_idx * 4 + slot]! = (roundStepE_kNat row_idx slot).toUInt32 := by
    simpa [roundStepE_kNat] using k_word_eq_limbs row_idx slot hidx_bound hslot
  have hsched_word :
      scheduleWordAtRow air (nextRow air row) slot = (roundStepE_schedNat air row slot).toUInt32 := by
    rw [scheduleWordAtRow_eq_bitsWordToUInt32]
    simpa [roundStepE_schedNat] using bitsWordToUInt32_eq_compose16
      (scheduleBitsWord air (nextRow air row) slot) hsched_bits
  dsimp [roundStep, slotInputState, roundStepE_sumWord]
  rw [hd_word, hh_word, hsig1_word, hch_word, hk_word, hsched_word]
  simp [add_assoc]

theorem round_step_e_sum_eq_result (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row))
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    roundStepE_sumWord air row slot row_idx =
      (roundStepE_resultNat air row slot).toUInt32 := by
  have hslot0 : slot < 8 := by omega
  have hslot1 : slot + 1 < 8 := by omega
  have hslot2 : slot + 2 < 8 := by omega
  have hslot3 : slot + 3 < 8 := by omega
  have hd_bits : isBitsWord (concatABitsWord air row slot) :=
    concatABits_boolean air row slot hslot0 hbb hbb_next
  have hh_bits : isBitsWord (concatEBitsWord air row slot) :=
    concatEBits_boolean air row slot hslot0 hbb hbb_next
  have he_bits : isBitsWord (concatEBitsWord air row (slot + 3)) :=
    concatEBits_boolean air row (slot + 3) hslot3 hbb hbb_next
  have hf_bits : isBitsWord (concatEBitsWord air row (slot + 2)) :=
    concatEBits_boolean air row (slot + 2) hslot2 hbb hbb_next
  have hg_bits : isBitsWord (concatEBitsWord air row (slot + 1)) :=
    concatEBits_boolean air row (slot + 1) hslot1 hbb hbb_next
  have hsig1_bits :
      isBitsWord (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) :=
    fieldBigSigma1_isBitsWord _ he_bits
  have hch_bits :
      isBitsWord (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))) :=
    fieldCh_isBitsWord _ _ _ he_bits hf_bits hg_bits
  have hnext_e_bits : isBitsWord (eBitsWord air (nextRow air row) slot) := by
    intro i
    exact hbb_next.2 slot i.val hslot i.isLt
  have hlo_eq := round_step_e_lo_eq air row slot row_idx hslot hrow hrot hrs hbb hbb_next
    hround_next hflags_next hidx hidx_bound
  have hhi_eq := round_step_e_hi_eq air row slot row_idx hslot hrow hrot hrs hbb hbb_next
    hround_next hflags_next hidx hidx_bound
  have hd_lo_lt : (composeLo16 (concatABitsWord air row slot)).val < 2 ^ 16 :=
    composeLo16_val_lt _ hd_bits
  have hd_hi_lt : (composeHi16 (concatABitsWord air row slot)).val < 2 ^ 16 :=
    composeHi16_val_lt _ hd_bits
  have hh_lo_lt : (composeLo16 (concatEBitsWord air row slot)).val < 2 ^ 16 :=
    composeLo16_val_lt _ hh_bits
  have hh_hi_lt : (composeHi16 (concatEBitsWord air row slot)).val < 2 ^ 16 :=
    composeHi16_val_lt _ hh_bits
  have hsig1_lo_lt :
      (composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))).val < 2 ^ 16 :=
    composeLo16_val_lt _ hsig1_bits
  have hsig1_hi_lt :
      (composeHi16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3)))).val < 2 ^ 16 :=
    composeHi16_val_lt _ hsig1_bits
  have hch_lo_lt :
      (composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1)))).val < 2 ^ 16 :=
    composeLo16_val_lt _ hch_bits
  have hch_hi_lt :
      (composeHi16 (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1)))).val < 2 ^ 16 :=
    composeHi16_val_lt _ hch_bits
  have hk_lo_lt : (k_limb_at row_idx slot 0).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 0 hidx_bound hslot (by omega)
  have hk_hi_lt : (k_limb_at row_idx slot 1).val < 2 ^ 16 :=
    k_limb_at_lt row_idx slot 1 hidx_bound hslot (by omega)
  have hsched_lo_lt :
      (composeLo16 (scheduleBitsWord air (nextRow air row) slot)).val < 2 ^ 16 :=
    composeLo16_val_lt _ hsched_bits
  have hsched_hi_lt :
      (composeHi16 (scheduleBitsWord air (nextRow air row) slot)).val < 2 ^ 16 :=
    composeHi16_val_lt _ hsched_bits
  have hres_lo_lt :
      (composeLo16 (eBitsWord air (nextRow air row) slot)).val < 2 ^ 16 :=
    composeLo16_val_lt _ hnext_e_bits
  have hres_hi_lt :
      (composeHi16 (eBitsWord air (nextRow air row) slot)).val < 2 ^ 16 :=
    composeHi16_val_lt _ hnext_e_bits
  have hcarry_lo_lt : (next_carry_e air slot 0 row).val < 2 ^ 8 := by
    simpa [next_carry_e_eq_nextRow air hrot slot 0 row hrow] using
      (hcarry_next slot 0 hslot (by omega)).2
  have hcarry_hi_lt : (next_carry_e air slot 1 row).val < 2 ^ 8 := by
    simpa [next_carry_e_eq_nextRow air hrot slot 1 row hrow] using
      (hcarry_next slot 1 hslot (by omega)).2
  have hbounds :
      ∀ x ∈ [composeLo16 (concatABitsWord air row slot),
             composeHi16 (concatABitsWord air row slot),
             composeLo16 (concatEBitsWord air row slot),
             composeHi16 (concatEBitsWord air row slot),
             composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))),
             composeHi16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))),
             composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
               (concatEBitsWord air row (slot + 2))
               (concatEBitsWord air row (slot + 1))),
             composeHi16 (fieldCh (concatEBitsWord air row (slot + 3))
               (concatEBitsWord air row (slot + 2))
               (concatEBitsWord air row (slot + 1))),
             k_limb_at row_idx slot 0, k_limb_at row_idx slot 1,
             composeLo16 (scheduleBitsWord air (nextRow air row) slot),
             composeHi16 (scheduleBitsWord air (nextRow air row) slot)], x.val < 2 ^ 16 := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hd_lo_lt
    · exact hd_hi_lt
    · exact hh_lo_lt
    · exact hh_hi_lt
    · exact hsig1_lo_lt
    · exact hsig1_hi_lt
    · exact hch_lo_lt
    · exact hch_hi_lt
    · exact hk_lo_lt
    · exact hk_hi_lt
    · exact hsched_lo_lt
    · exact hsched_hi_lt
  simpa [roundStepE_sumWord, roundStepE_dNat, roundStepE_hNat, roundStepE_sigma1Nat,
    roundStepE_chNat, roundStepE_kNat, roundStepE_schedNat, roundStepE_resultNat] using
    (limbed_addition_six_uint32
      (composeLo16 (concatABitsWord air row slot))
      (composeHi16 (concatABitsWord air row slot))
      (composeLo16 (concatEBitsWord air row slot))
      (composeHi16 (concatEBitsWord air row slot))
      (composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))))
      (composeHi16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))))
      (composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))))
      (composeHi16 (fieldCh (concatEBitsWord air row (slot + 3))
        (concatEBitsWord air row (slot + 2))
        (concatEBitsWord air row (slot + 1))))
      (k_limb_at row_idx slot 0)
      (k_limb_at row_idx slot 1)
      (composeLo16 (scheduleBitsWord air (nextRow air row) slot))
      (composeHi16 (scheduleBitsWord air (nextRow air row) slot))
      (composeLo16 (eBitsWord air (nextRow air row) slot))
      (composeHi16 (eBitsWord air (nextRow air row) slot))
      (next_carry_e air slot 0 row)
      (next_carry_e air slot 1 row)
      hbounds hres_lo_lt hres_hi_lt hcarry_lo_lt hcarry_hi_lt hlo_eq hhi_eq)

/-- A single round step: the new e-word matches roundStep.e. -/
theorem single_round_e_correct (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (row_idx : ℕ)
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16)
    (hcarry_next : roundCarryBoundsAt air (nextRow air row))
    (hsched_bits : isBitsWord (scheduleBitsWord air (nextRow air row) slot)) :
    eWord air (nextRow air row) slot =
      (roundStep (slotInputState air row slot)
        (sha256K[row_idx * 4 + slot]!)
        (scheduleWordAtRow air (nextRow air row) slot)).e := by
  have hnext_e_bits : isBitsWord (eBitsWord air (nextRow air row) slot) := by
    intro i
    exact hbb_next.2 slot i.val hslot i.isLt
  have hres_word :
      eWord air (nextRow air row) slot =
        (roundStepE_resultNat air row slot).toUInt32 := by
    rw [eWord_eq_bitsWordToUInt32]
    simpa [roundStepE_resultNat] using
      bitsWordToUInt32_eq_compose16 (eBitsWord air (nextRow air row) slot) hnext_e_bits
  calc
    eWord air (nextRow air row) slot = (roundStepE_resultNat air row slot).toUInt32 := hres_word
    _ = roundStepE_sumWord air row slot row_idx := by
          symm
          exact round_step_e_sum_eq_result air row slot row_idx hslot hrow hrot hrs hbb hbb_next
            hround_next hflags_next hidx hidx_bound hcarry_next hsched_bits
    _ = (roundStep (slotInputState air row slot)
          (sha256K[row_idx * 4 + slot]!)
          (scheduleWordAtRow air (nextRow air row) slot)).e := by
          symm
          exact round_step_e_rhs_eq_sum air row slot row_idx hslot hbb hbb_next
            hidx_bound hsched_bits

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
