import VmExtensions.Constraints.KeccakfPermAir.Columns

set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace KeccakfPermAir.constraints

/-! ## Semantic Views

Structured 2D/3D indexing over the flat column abbreviations.

Indexing convention:
- lane `(x, y)` = flat index `5*y + x`
- each lane = 4 u16 limbs (for limb arrays) or 64 bits (for bit arrays)
-/

section views
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  /-! ### State views: 5×5×4 u16 limb arrays -/

  /-- State `a` at lane `(x, y)`, limb index. -/
  abbrev a_view (c : C F ExtF) (x y : Fin 5) (limb : Fin 4) (row : ℕ) : F :=
    a c (4 * (5 * y.val + x.val) + limb.val) row

  /-- Preimage at lane `(x, y)`, limb index. -/
  abbrev preimage_view (c : C F ExtF) (x y : Fin 5) (limb : Fin 4) (row : ℕ) : F :=
    preimage c (4 * (5 * y.val + x.val) + limb.val) row

  /-- State after ρπ+χ at lane `(x, y)`, limb index. -/
  abbrev a_prime_prime_view (c : C F ExtF) (x y : Fin 5) (limb : Fin 4) (row : ℕ) : F :=
    a_prime_prime c (4 * (5 * y.val + x.val) + limb.val) row

  /-! ### Bit views: 5×5×64 and 5×64 -/

  /-- θ result bit at lane `(x, y)`, bit index. -/
  abbrev a_prime_bit_view (c : C F ExtF) (x y : Fin 5) (bit : Fin 64) (row : ℕ) : F :=
    a_prime_bit c (64 * (5 * y.val + x.val) + bit.val) row

  /-- θ column-parity bit at column `x`, bit index. -/
  abbrev c_bit_view (c : C F ExtF) (x : Fin 5) (bit : Fin 64) (row : ℕ) : F :=
    c_bit c (64 * x.val + bit.val) row

  /-- θ parity-prime bit at column `x`, bit index. -/
  abbrev c_prime_bit_view (c : C F ExtF) (x : Fin 5) (bit : Fin 64) (row : ℕ) : F :=
    c_prime_bit c (64 * x.val + bit.val) row

  /-! ### Iota views -/

  /-- Bits of a_prime_prime[0][0] at bit index. -/
  abbrev a_pp_00_bit_view (c : C F ExtF) (bit : Fin 64) (row : ℕ) : F :=
    a_pp_00_bit c bit.val row

  /-- ι result limb for lane [0][0] at limb index. -/
  abbrev a_ppp_00_limb_view (c : C F ExtF) (limb : Fin 4) (row : ℕ) : F :=
    a_ppp_00_limb c limb.val row

  /-! ### Index-in-bounds lemmas -/

  lemma a_view_flat_lt (x y : Fin 5) (limb : Fin 4) :
      4 * (5 * y.val + x.val) + limb.val < 100 := by omega

  lemma a_prime_bit_view_flat_lt (x y : Fin 5) (bit : Fin 64) :
      64 * (5 * y.val + x.val) + bit.val < 1600 := by omega

  lemma c_bit_view_flat_lt (x : Fin 5) (bit : Fin 64) :
      64 * x.val + bit.val < 320 := by omega

  lemma c_prime_bit_view_flat_lt (x : Fin 5) (bit : Fin 64) :
      64 * x.val + bit.val < 320 := by omega

end views

end KeccakfPermAir.constraints
