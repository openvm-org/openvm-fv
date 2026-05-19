/-
  Theta CPrime interface for the KeccakfPermAir single-round correctness proof.

  This file provides:
  • `fieldXor_bool`: boolean closure of `fieldXor` — XOR of two boolean field
    elements is boolean.
  • `c_prime_bit_eq_xor`: each `c_prime_bit[i]` equals the three-way field XOR
    of three `c_bit` witnesses, with the neighbor and shifted-bit indexing
    from `Theta/CPrime.lean` (constraints 570–889).
  • `c_prime_bit_is_bool`: booleanity of every `c_prime_bit` column, derived
    by applying `fieldXor_bool` twice to the boolean `c_bit` inputs.

  This file only relates `c_prime` to `c`; it does not identify `c` with
  input-column parity.
-/
import VmExtensions.Soundness.KeccakfPermAir.Round.BooleanFacts

set_option autoImplicit false
set_option linter.all false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints

/-! ## `fieldXor` boolean closure

`fieldXor a b = a + b - 2*a*b`.  When both `a` and `b` are in `{0, 1}`,
the result is again in `{0, 1}`.  This is the algebraic version of the
fact that XOR maps `Bool × Bool → Bool`. -/

/-- `fieldXor` of two boolean field elements is boolean.
    Proof: case-split on `a ∈ {0,1}` and `b ∈ {0,1}` (four cases),
    then compute `fieldXor` in each case. -/
theorem fieldXor_bool {F : Type} [CommRing F] {a b : F}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    fieldXor a b = 0 ∨ fieldXor a b = 1 := by
  -- fieldXor a b = a + b - 2 * a * b
  -- Case split on (a, b) ∈ {(0,0), (0,1), (1,0), (1,1)}.
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [fieldXor] <;> ring_nf <;> simp

/-! ## Index bounds for neighbor and shifted-bit positions

The three-way XOR formula references `c_bit` at three indices:
- `i` (center), already known to be < 320
- `left_idx = 64 * ((x + 4) % 5) + z` where `x = i / 64`, `z = i % 64`
- `right_shift_idx = 64 * ((x + 1) % 5) + (z + 63) % 64`

Both neighbor indices are in `[0, 320)` because the column and bit
modular arithmetic keep them in range. -/

/-- The left-neighbor index is < 320. -/
private theorem left_idx_lt (i : ℕ) (hi : i < 320) :
    64 * ((i / 64 + 4) % 5) + i % 64 < 320 := by
  omega

/-- The right-shifted index is < 320. -/
private theorem right_shift_idx_lt (i : ℕ) (hi : i < 320) :
    64 * ((i / 64 + 1) % 5) + (i % 64 + 63) % 64 < 320 := by
  omega

/-! ## `c_prime_bit` = three-way XOR of `c_bit` witnesses

From `RoundLocalConstraints.c_prime_def`, each constraint says
`c_prime_bit[i] - fieldXor(fieldXor(c_bit[i], c_bit[left(i)]), c_bit[rightShift(i)]) = 0`.
Rearranging by `sub_eq_zero` gives the equality directly. -/

/-- Each `c_prime_bit[i]` equals the three-way `fieldXor` of:
    - `c_bit[i]` (center)
    - `c_bit[left_idx]` (same bit in column `(x+4)%5`)
    - `c_bit[right_shift_idx]` (bit `(z+63)%64` in column `(x+1)%5`)

    This is the interface theorem recovering the exact XOR expression from
    the `Theta/CPrime.lean` constraint wrappers (constraints 570–889).
    The neighbor/shift indexing is preserved verbatim from `c_prime_def`. -/
theorem c_prime_bit_eq_xor
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (i : ℕ) (hi : i < 320) :
    let x := i / 64
    let z := i % 64
    let left_idx := 64 * ((x + 4) % 5) + z
    let right_shift_idx := 64 * ((x + 1) % 5) + (z + 63) % 64
    c_prime_bit air i row =
      fieldXor (fieldXor (c_bit air i row) (c_bit air left_idx row))
               (c_bit air right_shift_idx row) := by
  -- The c_prime_def constraint gives: (c_prime_bit - xor_expr) = 0
  -- By sub_eq_zero, this becomes xor_expr = c_prime_bit, then .symm reverses.
  have hc := h_round.c_prime_def i hi
  -- hc has let-bindings; unfold them so sub_eq_zero can work on the raw equation.
  simp only at hc
  -- hc : c_prime_bit air i row - fieldXor (...) (...) = 0
  -- sub_eq_zero.mp gives: c_prime_bit = fieldXor (...)
  exact sub_eq_zero.mp hc

/-! ## `c_prime_bit` is boolean

Since `c_prime_bit[i]` is a `fieldXor` of three boolean `c_bit` values,
it is itself boolean.  The proof applies `fieldXor_bool` twice:
1. `fieldXor(center, left)` is boolean (both inputs boolean by `c_bit_is_bool`)
2. `fieldXor(fieldXor(center, left), right_shift)` is boolean (step 1 + `c_bit_is_bool`) -/

/-- Each `c_prime_bit` column is boolean (0 or 1) at this row.
    Proof: rewrite to the three-way XOR via `c_prime_bit_eq_xor`, then
    apply `fieldXor_bool` twice using `c_bit_is_bool` for the three inputs. -/
theorem c_prime_bit_is_bool
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (i : ℕ) (hi : i < 320) :
    c_prime_bit air i row = 0 ∨ c_prime_bit air i row = 1 := by
  -- Step 1: Rewrite c_prime_bit to the fieldXor expression.
  rw [c_prime_bit_eq_xor h_round i hi]
  -- Step 2: Establish booleanity of the three c_bit inputs.
  have hc_center := c_bit_is_bool h_round i hi
  have hc_left := c_bit_is_bool h_round _ (left_idx_lt i hi)
  have hc_right := c_bit_is_bool h_round _ (right_shift_idx_lt i hi)
  -- Step 3: Apply fieldXor_bool twice.
  -- First application: fieldXor(center, left) is boolean.
  have h_inner := fieldXor_bool hc_center hc_left
  -- Second application: fieldXor(fieldXor(center, left), right_shift) is boolean.
  exact fieldXor_bool h_inner hc_right

end KeccakfPermAir.Soundness
