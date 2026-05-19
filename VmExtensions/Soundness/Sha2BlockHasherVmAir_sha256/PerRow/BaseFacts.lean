/-
  Layer A: Per-Row Facts (Base Facts)

  Converts raw constraint satisfaction into semantic predicates:
  - flag_constraints → flagsWellFormed
  - flag_constraints → first selector/encoder facts

  The heavier selector facts live in `SelectorFacts.lean`, and the
  workvar-bit booleanness layer lives in `BitsFacts.lean`.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Core.FieldArithmetic

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## Flag Booleanness (constraints 0–3)

Constraints 0–3 each have the form `flag * (flag - 1) = 0`.
Each follows directly from `bit_boolean_of_sq_eq_zero`. -/

/-- `is_round_row` is boolean (constraint 0). -/
theorem is_round_row_boolean (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    is_round_row air row = 0 ∨ is_round_row air row = 1 := by
  exact bit_boolean_of_sq_eq_zero _ hf.1

/-- `is_first_4_rows` is boolean (constraint 1). -/
theorem is_first_4_rows_boolean (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    is_first_4_rows air row = 0 ∨ is_first_4_rows air row = 1 := by
  exact bit_boolean_of_sq_eq_zero _ hf.2.1

/-- `is_digest_row` is boolean (constraint 2). -/
theorem is_digest_row_boolean (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    is_digest_row air row = 0 ∨ is_digest_row air row = 1 := by
  exact bit_boolean_of_sq_eq_zero _ hf.2.2.1

/-- `is_round_row + is_digest_row` is boolean (constraint 3). -/
theorem round_plus_digest_boolean (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    is_round_row air row + is_digest_row air row = 0 ∨
    is_round_row air row + is_digest_row air row = 1 := by
  exact bit_boolean_of_sq_eq_zero _ hf.2.2.2.1

/-! ## Encoder Digit Constraints (constraints 4–10) -/

/-- Each of the 5 encoder digits is ternary (constraints 4–8).
    Each constraint is `d * (d-1) * (d-2) = 0`. -/
theorem encoder_digits_ternary (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    ∀ i, i < 5 → encoder_idx air i row = 0 ∨
                   encoder_idx air i row = 1 ∨
                   encoder_idx air i row = 2 := by
  rcases hf with ⟨_, _, _, _, h4, h5, h6, h7, h8, _, _, _, _, _, _, _⟩
  intro i hi
  interval_cases i
  · simpa using ternary_of_cube_eq_zero (encoder_idx air 0 row) h4
  · simpa using ternary_of_cube_eq_zero (encoder_idx air 1 row) h5
  · simpa using ternary_of_cube_eq_zero (encoder_idx air 2 row) h6
  · simpa using ternary_of_cube_eq_zero (encoder_idx air 3 row) h7
  · simpa using ternary_of_cube_eq_zero (encoder_idx air 4 row) h8

/-- The sum of the 5 encoder digits is ternary (constraint 9). -/
theorem encoder_digit_sum_ternary (air : C FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    encoder_digit_sum air row = 0 ∨
    encoder_digit_sum air row = 1 ∨
    encoder_digit_sum air row = 2 := by
  rcases hf with ⟨_, _, _, _, _, _, _, _, _, h9, _, _, _, _, _, _⟩
  simpa [encoder_digit_sum] using ternary_of_cube_eq_zero (encoder_digit_sum air row) h9

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
