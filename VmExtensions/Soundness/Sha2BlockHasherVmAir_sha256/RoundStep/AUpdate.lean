/-
  Layer C: Round Step (A-State Update)
  Field-level low/high-limb equations for the `a` update.
  Depends on: Semantics
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.RoundStep.Semantics

set_option autoImplicit false

set_option maxHeartbeats 10000000

namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

theorem round_step_a_lo_eq (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16) :
    composeLo16 (concatEBitsWord air row slot) +
      composeLo16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) +
      composeLo16 (fieldCh (concatEBitsWord air row (slot + 3))
          (concatEBitsWord air row (slot + 2))
          (concatEBitsWord air row (slot + 1))) +
      k_limb_at row_idx slot 0 +
      composeLo16 (scheduleBitsWord air (nextRow air row) slot) +
      composeLo16 (fieldBigSigma0 (concatABitsWord air row (slot + 3))) +
    composeLo16 (fieldMaj (concatABitsWord air row (slot + 3))
          (concatABitsWord air row (slot + 2))
          (concatABitsWord air row (slot + 1))) =
    composeLo16 (aBitsWord air (nextRow air row) slot) +
      next_carry_a air slot 0 row * (2 ^ 16 : ℕ) := by
  have hraw := round_step_a_lo_eq_raw air row slot row_idx hslot hrow hrot hrs hbb hbb_next
    hround_next hflags_next hidx hidx_bound
  simpa only [nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row slot hrot hrow,
    nextABitsWord_eq_aBitsWord_nextRow air row slot hrot hrow,
    rawConcatABitsWord_eq_concatABitsWord air row (slot + 1) hrot hrow,
    rawConcatABitsWord_eq_concatABitsWord air row (slot + 2) hrot hrow,
    rawConcatABitsWord_eq_concatABitsWord air row (slot + 3) hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row slot hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 1) hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 2) hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 3) hrot hrow,
    add_assoc, add_left_comm, add_comm] using hraw

/-- Field-level high-limb equation for the `a` update of one round slot. -/
theorem round_step_a_hi_eq (air : C FBB ExtF) (row slot row_idx : ℕ)
    (hslot : slot < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hrs : round_step_constraints air row)
    (hbb : allWorkVarBitsBoolean air row)
    (hbb_next : allWorkVarBitsBoolean air (nextRow air row))
    (hround_next : next_is_round_row air row = 1)
    (hflags_next : flag_constraints air (nextRow air row))
    (hidx : encoder_selector_idx air (nextRow air row) = (row_idx : FBB))
    (hidx_bound : row_idx < 16) :
    composeHi16 (concatEBitsWord air row slot) +
      composeHi16 (fieldBigSigma1 (concatEBitsWord air row (slot + 3))) +
      composeHi16 (fieldCh (concatEBitsWord air row (slot + 3))
          (concatEBitsWord air row (slot + 2))
          (concatEBitsWord air row (slot + 1))) +
      k_limb_at row_idx slot 1 +
      composeHi16 (scheduleBitsWord air (nextRow air row) slot) +
      composeHi16 (fieldBigSigma0 (concatABitsWord air row (slot + 3))) +
    composeHi16 (fieldMaj (concatABitsWord air row (slot + 3))
          (concatABitsWord air row (slot + 2))
          (concatABitsWord air row (slot + 1))) +
      next_carry_a air slot 0 row =
    composeHi16 (aBitsWord air (nextRow air row) slot) +
      next_carry_a air slot 1 row * (2 ^ 16 : ℕ) := by
  have hraw := round_step_a_hi_eq_raw air row slot row_idx hslot hrow hrot hrs hbb hbb_next
    hround_next hflags_next hidx hidx_bound
  simpa only [nextScheduleBitsWord_eq_scheduleBitsWord_nextRow air row slot hrot hrow,
    nextABitsWord_eq_aBitsWord_nextRow air row slot hrot hrow,
    rawConcatABitsWord_eq_concatABitsWord air row (slot + 1) hrot hrow,
    rawConcatABitsWord_eq_concatABitsWord air row (slot + 2) hrot hrow,
    rawConcatABitsWord_eq_concatABitsWord air row (slot + 3) hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row slot hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 1) hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 2) hrot hrow,
    rawConcatEBitsWord_eq_concatEBitsWord air row (slot + 3) hrot hrow,
    add_assoc, add_left_comm, add_comm] using hraw

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
