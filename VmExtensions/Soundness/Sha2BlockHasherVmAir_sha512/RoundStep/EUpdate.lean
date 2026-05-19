/-
  Layer C: Round Step (E-State Update)

  Derived `e`-update limb equalities over the wrap-aware SHA-512 word views.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.RoundStep.Semantics

set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

theorem round_step_e_limb_eq (air : C FBB ExtF) (row slot limb row_idx : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 20) :
    bitsU16Limb (concatABitsWord air row slot) limb +
      bitsU16Limb (concatEBitsWord air row slot) limb +
      bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) limb +
      bitsU16Limb
        (fieldCh (concatEBitsWord air row (slot + 3))
          (concatEBitsWord air row (slot + 2))
          (concatEBitsWord air row (slot + 1))) limb +
      k_limb_at row_idx slot limb +
      bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) limb +
      roundStepCarryInE air row slot limb =
    bitsU16Limb (eBitsWord air (nextRow air row) slot) limb +
      next_carry_e air slot limb row * (2 ^ 16 : ℕ) := by
  have hraw := hrs.e_update_limb_eq slot limb hslot hlimb
  have hk :
      roundConstantPolyAtNext air row slot limb = k_limb_at row_idx slot limb :=
    roundConstantPolyAtNext_eq_k_limb_at air row slot limb row_idx hslot hlimb hidx hidx_bound
  rw [hk] at hraw
  rw [hround_next] at hraw
  simp only [mul_one] at hraw
  simpa [bitsU16Limb, hlimb, add_assoc, add_left_comm, add_comm,
    nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row slot hrot hrow,
    nextEBitsWord_eq_eBitsWord_nextRow air row slot hrot hrow,
    rawConcatABitsWord_eq_concatABitsWord air row slot hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row slot hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 1) hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 2) hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 3) hrot hrow] using hraw

theorem round_step_e_lo_eq (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 20) :
    bitsU16Limb (concatABitsWord air row slot) 0 +
      bitsU16Limb (concatEBitsWord air row slot) 0 +
      bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) 0 +
      bitsU16Limb
        (fieldCh (concatEBitsWord air row (slot + 3))
          (concatEBitsWord air row (slot + 2))
          (concatEBitsWord air row (slot + 1))) 0 +
      k_limb_at row_idx slot 0 +
      bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) 0 +
      roundStepCarryInE air row slot 0 =
    bitsU16Limb (eBitsWord air (nextRow air row) slot) 0 +
      next_carry_e air slot 0 row * (2 ^ 16 : ℕ) := by
  simpa using round_step_e_limb_eq air row slot 0 row_idx hslot (by omega) hrow hrot hrs
    hround_next hidx hidx_bound

theorem round_step_e_hi_eq (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 20) :
    bitsU16Limb (concatABitsWord air row slot) 3 +
      bitsU16Limb (concatEBitsWord air row slot) 3 +
      bitsU16Limb (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) 3 +
      bitsU16Limb
        (fieldCh (concatEBitsWord air row (slot + 3))
          (concatEBitsWord air row (slot + 2))
          (concatEBitsWord air row (slot + 1))) 3 +
      k_limb_at row_idx slot 3 +
      bitsU16Limb (scheduleBitsWord air (nextRow air row) slot) 3 +
      roundStepCarryInE air row slot 3 =
    bitsU16Limb (eBitsWord air (nextRow air row) slot) 3 +
      next_carry_e air slot 3 row * (2 ^ 16 : ℕ) := by
  simpa using round_step_e_limb_eq air row slot 3 row_idx hslot (by omega) hrow hrot hrs
    hround_next hidx hidx_bound

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
