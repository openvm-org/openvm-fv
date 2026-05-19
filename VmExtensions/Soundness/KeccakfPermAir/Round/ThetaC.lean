/-
  Theta C recovery for the KeccakfPermAir single-round correctness proof.

  This file provides:
  • `theta_parity_constraint`: the raw parity constraint from `Theta/Parity.lean`,
    restated as a clean projection from `RoundLocalConstraints`.
  • `parity_of_five_bools`: when five boolean field values have a parity polynomial
    constraint `(S - P)(S - P - 2)(S - P - 4) = 0` with boolean P, then
    P = iterated fieldXor of the five values (i.e., P is their parity).
  • `c_prime_eq_parity_a_prime`: each `c_prime_bit[i]` equals the XOR-parity of
    the five `a_prime_bit` values at y-offsets 0, 320, 640, 960, 1280.
  • `fieldXor_comm`, `fieldXor_assoc_bool`, `fieldXor_self_cancel`: XOR algebra.
  • `xor3_eq_fieldXor`: the three-input xor3 polynomial equals nested fieldXor
    when all inputs are boolean.
  • `xor_parity_cancellation`: algebraic core of the c-recovery cancellation.
  • `c_bit_eq_parity_xor3`: the unconditional cancellation theorem — c_bit witnesses
    equal the XOR-parity of the xor3-defined input bits, recovering the semantic
    meaning of c from `RoundLocalConstraints` alone.

-/
import VmExtensions.Soundness.KeccakfPermAir.Round.ThetaCPrime
import VmExtensions.Soundness.KeccakfPermAir.Round.ThetaXor3

set_option autoImplicit false
set_option linter.all false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints

/-! ## Parity constraint projection

The `theta_parity` field of `RoundLocalConstraints` states that for each
bit position i (0–319), the cubic parity polynomial vanishes:
  (sum5 - c_prime_bit[i]) * (sum5 - c_prime_bit[i] - 2) * (sum5 - c_prime_bit[i] - 4) = 0
where sum5 is the sum of five a_prime_bit values at y-offsets 0, 320, 640, 960, 1280.
This is a direct projection — no new reasoning needed. -/

/-- The raw parity constraint from `Theta/Parity.lean`: for each bit position
    i < 320, the difference `sum5 - c_prime_bit[i]` satisfies the cubic factor
    `d * (d - 2) * (d - 4) = 0`.

    This is the interface theorem recording exactly what `theta_parity` says,
    projected from `RoundLocalConstraints`. -/
theorem theta_parity_constraint
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (i : ℕ) (hi : i < 320) :
    let sum5 := a_prime_bit air i row + a_prime_bit air (i + 320) row +
                a_prime_bit air (i + 640) row + a_prime_bit air (i + 960) row +
                a_prime_bit air (i + 1280) row
    let diff := sum5 - c_prime_bit air i row
    diff * (diff - 2) * (diff - 4) = 0 :=
  h_round.theta_parity i hi

/-! ## fieldXor algebra

Properties of `fieldXor a b = a + b - 2*a*b` needed for parity reasoning.
When both arguments are boolean (in {0, 1}), `fieldXor` is boolean XOR. -/

/-- `fieldXor` is commutative. -/
theorem fieldXor_comm {F : Type} [CommRing F] (a b : F) :
    fieldXor a b = fieldXor b a := by
  simp [fieldXor]; ring

/-- `fieldXor` is associative when all inputs are boolean.
    (Not true in general, but holds on {0,1}.) -/
theorem fieldXor_assoc_bool {F : Type} [CommRing F] {a b c : F}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    fieldXor (fieldXor a b) c = fieldXor a (fieldXor b c) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp [fieldXor] <;> ring

/-- `fieldXor a a = 0` when `a` is boolean. -/
theorem fieldXor_self_cancel {F : Type} [CommRing F] {a : F}
    (ha : a = 0 ∨ a = 1) :
    fieldXor a a = 0 := by
  rcases ha with rfl | rfl <;> simp [fieldXor] <;> ring

/-- `fieldXor a 0 = a`. -/
theorem fieldXor_zero_right {F : Type} [CommRing F] (a : F) :
    fieldXor a 0 = a := by
  simp [fieldXor]

/-- `fieldXor 0 a = a`. -/
theorem fieldXor_zero_left {F : Type} [CommRing F] (a : F) :
    fieldXor 0 a = a := by
  simp [fieldXor]

/-! ## Parity of five boolean values

The core boolean algebra lemma: when five field values are each 0 or 1,
their sum S is in {0, 1, 2, 3, 4, 5}. If P is boolean and
(S - P)(S - P - 2)(S - P - 4) = 0, then P = S mod 2 (the parity).

Equivalently, P = fieldXor(b₀, fieldXor(b₁, fieldXor(b₂, fieldXor(b₃, b₄)))).

The cubic parity polynomial cannot distinguish correct from incorrect parity
in fields of characteristic 3 or 5, so we require `(3 : F) ≠ 0` and
`(5 : F) ≠ 0`. Both hold for BabyBear (char = 2013265921 > 5).

We prove this by exhaustive case analysis on the five boolean inputs and P. -/

/-- 3 ≠ 0 in BabyBear.  Used to close invalid parity cases where the
    cubic product evaluates to ±3 (mod BB_prime). -/
private lemma fbb_ne_zero_3 : ¬ (3 : FBB) = 0 := by native_decide

/-- 15 ≠ 0 in BabyBear.  Used to close invalid parity cases where the
    cubic product evaluates to ±15 (mod BB_prime). -/
private lemma fbb_ne_zero_15 : ¬ (15 : FBB) = 0 := by native_decide

set_option maxHeartbeats 1600000 in
/-- When five boolean BabyBear values sum to S and P is boolean with
    `(S - P) * (S - P - 2) * (S - P - 4) = 0`, then
    P equals the iterated `fieldXor` (parity) of the five values.

    Specialized to FBB (BabyBear) because the cubic parity polynomial
    cannot distinguish correct from incorrect parity in fields of
    characteristic 3 or 5. BabyBear has char = 2013265921 > 5.

    Proof: case split on all 6 boolean variables (64 cases).
    Valid cases (P = correct parity): `norm_num` simplifies the cubic
    to `0 = 0`, then `simp [fieldXor]; ring` closes the identity.
    Invalid cases (P = wrong parity): `norm_num` reduces the cubic to
    `3 = 0` or `15 = 0` in FBB, contradicted by `fbb_ne_zero_3/15`. -/
theorem parity_of_five_bools
    {b₀ b₁ b₂ b₃ b₄ P : FBB}
    (h0 : b₀ = 0 ∨ b₀ = 1) (h1 : b₁ = 0 ∨ b₁ = 1)
    (h2 : b₂ = 0 ∨ b₂ = 1) (h3 : b₃ = 0 ∨ b₃ = 1)
    (h4 : b₄ = 0 ∨ b₄ = 1) (hP : P = 0 ∨ P = 1)
    (hcubic : let S := b₀ + b₁ + b₂ + b₃ + b₄
              let d := S - P
              d * (d - 2) * (d - 4) = 0) :
    P = fieldXor b₀ (fieldXor b₁ (fieldXor b₂ (fieldXor b₃ b₄))) := by
  -- Exhaustive case split on 6 boolean variables (64 cases).
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;>
  rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
  rcases h4 with rfl | rfl <;> rcases hP with rfl | rfl <;> (
    -- After case split, all variables are concrete (0 or 1 in FBB).
    -- Unfold let-bindings, then norm_num evaluates the cubic product.
    simp only at hcubic
    try norm_num at hcubic
    -- Invalid cases: hcubic is `3 = 0` or `15 = 0`, contradicted by helpers.
    -- Valid cases: hcubic was eliminated. Close with fieldXor + ring.
    first
    | exact absurd hcubic fbb_ne_zero_3
    | exact absurd hcubic fbb_ne_zero_15
    | (simp only [fieldXor]; ring))

/-! ## c_prime_bit = parity of a_prime_bit over y

Applying `parity_of_five_bools` to the `theta_parity` constraint with
booleanity from `a_prime_bit_is_bool` and `c_prime_bit_is_bool`. -/

/-- Index bound: i + 320 < 1600 when i < 320. -/
private theorem idx_320_lt (i : ℕ) (hi : i < 320) : i + 320 < 1600 := by omega
/-- Index bound: i + 640 < 1600 when i < 320. -/
private theorem idx_640_lt (i : ℕ) (hi : i < 320) : i + 640 < 1600 := by omega
/-- Index bound: i + 960 < 1600 when i < 320. -/
private theorem idx_960_lt (i : ℕ) (hi : i < 320) : i + 960 < 1600 := by omega
/-- Index bound: i + 1280 < 1600 when i < 320. -/
private theorem idx_1280_lt (i : ℕ) (hi : i < 320) : i + 1280 < 1600 := by omega

/-- Each `c_prime_bit[i]` equals the XOR-parity of the five `a_prime_bit`
    values at y-offsets 0, 320, 640, 960, 1280.

    This is the semantic content of the `theta_parity` constraint: the
    `c_prime_bit` witnesses are the column parities of the `a_prime_bit`
    theta-output witnesses.

    Proof: apply `parity_of_five_bools` with booleanity from
    `a_prime_bit_is_bool` and `c_prime_bit_is_bool`, and the cubic
    constraint from `theta_parity_constraint`. -/
theorem c_prime_eq_parity_a_prime
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (i : ℕ) (hi : i < 320) :
    c_prime_bit air i row =
      fieldXor (a_prime_bit air i row)
        (fieldXor (a_prime_bit air (i + 320) row)
          (fieldXor (a_prime_bit air (i + 640) row)
            (fieldXor (a_prime_bit air (i + 960) row)
                      (a_prime_bit air (i + 1280) row)))) := by
  exact parity_of_five_bools
    (a_prime_bit_is_bool h_round i (by omega))
    (a_prime_bit_is_bool h_round (i + 320) (idx_320_lt i hi))
    (a_prime_bit_is_bool h_round (i + 640) (idx_640_lt i hi))
    (a_prime_bit_is_bool h_round (i + 960) (idx_960_lt i hi))
    (a_prime_bit_is_bool h_round (i + 1280) (idx_1280_lt i hi))
    (c_prime_bit_is_bool h_round i hi)
    (theta_parity_constraint h_round i hi)

/-! ## xor3 polynomial = nested fieldXor on booleans

The three-input XOR polynomial used in `xor3_recompose16_eq` is:
  xor3(a, b, c) = a + b + c - 2ab - 2ac - 2bc + 4abc

When all three inputs are boolean, this equals `fieldXor(fieldXor(a, b), c)`.
This identity connects the limb-level xor3 recomposition to bit-level XOR. -/

/-- The three-input XOR polynomial equals nested `fieldXor` when all
    inputs are boolean.
    Proof: case-split on all 8 boolean combinations. -/
theorem xor3_eq_fieldXor {F : Type} [CommRing F] {a b c : F}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    a + b + c - 2 * a * b - 2 * a * c - 2 * b * c + 4 * a * b * c =
    fieldXor (fieldXor a b) c := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp [fieldXor] <;> ring

/-! ## Cancellation: c_bit = parity of input a-column bits

### Strategy

The cancellation argument works at the bit level.
For each bit position i in c_bit/c_prime_bit (0 ≤ i < 320), there are five
corresponding y-positions in a_prime_bit: i, i+320, i+640, i+960, i+1280.

The xor3 linking gives (per bit): `a_bit = fieldXor(fieldXor(c_bit, c_prime_bit), a_prime_bit)`
The parity constraint gives: `c_prime_bit = fieldXor-parity(a_prime_bit over y)`

XOR-parity of 5 values of the form `w ⊕ v_y` where w = c ⊕ c' is constant:
Since 5 is odd, w appears an odd number of times, so parity(w⊕v_0,...,w⊕v_4) = w ⊕ parity(v_0,...,v_4).
Substituting parity(v_y) = c': result is w ⊕ c' = (c ⊕ c') ⊕ c' = c.

The proof uses algebraic composition (fieldXor_assoc_bool, fieldXor_pair_cancel,
fieldXor_self_cancel) rather than a large case split. -/

/-- The five y-indices for a_prime_bit: for a fixed (x, z) encoded as
    bit-position i = 64*x + z, the five a_prime_bit indices are
    i, i+320, i+640, i+960, i+1280 (one per y ∈ {0,1,2,3,4}). -/
def a_prime_y_indices (i : ℕ) : Fin 5 → ℕ
  | ⟨0, _⟩ => i
  | ⟨1, _⟩ => i + 320
  | ⟨2, _⟩ => i + 640
  | ⟨3, _⟩ => i + 960
  | ⟨4, _⟩ => i + 1280

/-- Helper: `fieldXor(fieldXor(a, x), fieldXor(a, y)) = fieldXor(x, y)` when
    all inputs are boolean.  This is "XOR with a constant cancels in pairs".
    Proof: 8-case split on (a, x, y). -/
private theorem fieldXor_pair_cancel {F : Type} [CommRing F] {a x y : F}
    (ha : a = 0 ∨ a = 1) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    fieldXor (fieldXor a x) (fieldXor a y) = fieldXor x y := by
  rcases ha with rfl | rfl <;> rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [fieldXor] <;> ring

/-- Key algebraic cancellation: XOR-parity of 5 values of the form
    `fieldXor(fieldXor(c, c'), v_y)` where c,c' are constant across y
    equals c, provided c' = parity(v_0, ..., v_4) and all values are boolean.

    The constant `w = c ⊕ c'` term appears
    an odd number of times (5), so its parity contribution is `w` itself.
    Combined with `c' = parity(v_y)`, the result is `w ⊕ c' = c`.

    Proof: algebraic composition using `fieldXor_assoc_bool`,
    `fieldXor_pair_cancel`, `fieldXor_self_cancel`, and `fieldXor_zero_right`.
    No large case split needed. -/
theorem xor_parity_cancellation {F : Type} [CommRing F]
    {c c' v₀ v₁ v₂ v₃ v₄ : F}
    (hc : c = 0 ∨ c = 1) (hc' : c' = 0 ∨ c' = 1)
    (hv0 : v₀ = 0 ∨ v₀ = 1) (hv1 : v₁ = 0 ∨ v₁ = 1)
    (hv2 : v₂ = 0 ∨ v₂ = 1) (hv3 : v₃ = 0 ∨ v₃ = 1)
    (hv4 : v₄ = 0 ∨ v₄ = 1)
    (hparity : c' = fieldXor v₀ (fieldXor v₁ (fieldXor v₂ (fieldXor v₃ v₄)))) :
    fieldXor (fieldXor (fieldXor c c') v₀)
      (fieldXor (fieldXor (fieldXor c c') v₁)
        (fieldXor (fieldXor (fieldXor c c') v₂)
          (fieldXor (fieldXor (fieldXor c c') v₃)
                    (fieldXor (fieldXor c c') v₄)))) = c := by
  -- Let w = fieldXor c c' (boolean since c, c' are).
  set w := fieldXor c c' with hw_def
  have hw : w = 0 ∨ w = 1 := fieldXor_bool hc hc'
  -- Step 1: Cancel the innermost pair.
  -- fieldXor(w ⊕ v₃, w ⊕ v₄) = fieldXor(v₃, v₄)
  rw [fieldXor_pair_cancel hw hv3 hv4]
  -- Step 2: Reassociate fieldXor(w⊕v₂, fieldXor(v₃, v₄)).
  -- = fieldXor(w, fieldXor(v₂, fieldXor(v₃, v₄)))
  have hv34 : fieldXor v₃ v₄ = 0 ∨ fieldXor v₃ v₄ = 1 := fieldXor_bool hv3 hv4
  rw [fieldXor_assoc_bool hw hv2 hv34]
  -- Step 3: Cancel pair (w⊕v₁, w⊕fieldXor(v₂, fieldXor(v₃, v₄))).
  have hv234 : fieldXor v₂ (fieldXor v₃ v₄) = 0 ∨ fieldXor v₂ (fieldXor v₃ v₄) = 1 :=
    fieldXor_bool hv2 hv34
  rw [fieldXor_pair_cancel hw hv1 hv234]
  -- Step 4: Reassociate to extract w.
  have hv1234 : fieldXor v₁ (fieldXor v₂ (fieldXor v₃ v₄)) = 0 ∨
                fieldXor v₁ (fieldXor v₂ (fieldXor v₃ v₄)) = 1 :=
    fieldXor_bool hv1 hv234
  rw [fieldXor_assoc_bool hw hv0 hv1234]
  -- Step 5: By hparity, fieldXor(v₀, ..., v₄) = c'.
  rw [← hparity]
  -- Step 6: fieldXor(fieldXor(c, c'), c') = fieldXor(c, fieldXor(c', c')) = fieldXor(c, 0) = c
  rw [hw_def, fieldXor_assoc_bool hc hc' hc', fieldXor_self_cancel hc', fieldXor_zero_right]

/-! ## c_bit = parity of input a-column

This is the culminating theorem of the theta witness recovery:
`c_bit[i] = XOR-parity over y of the input a-column bits`.

The xor3 linking constraint `a_limb = recompose16(xor3(c_bit, c_prime_bit, a_prime_bit))`
defines the input-column bits as the per-position XOR of the three witness families:
  `a_bit[y, i] := fieldXor(fieldXor(c_bit[i], c_prime_bit[i]), a_prime_bit[y*320 + i])`

(By `xor3_eq_fieldXor`, this equals the xor3 polynomial on boolean inputs.)

The cancellation theorem then shows: c_bit[i] = XOR-parity of these xor3-defined bits
over the five y values. This is unconditional — it depends only on `RoundLocalConstraints`
and the booleanity/parity theorems from earlier in this file. -/

/-- **Theta c-recovery (unconditional)**: for each bit position i < 320,
    `c_bit[i]` equals the XOR-parity of the five xor3-defined input bits
    at y-positions 0..4.

    The five "input bits" are:
      `fieldXor(fieldXor(c_bit[i], c_prime_bit[i]), a_prime_bit[y*320 + i])`
    for y = 0, 1, 2, 3, 4. By the xor3 linking constraint, these are the
    bits of the `a` column (input state).

    This theorem combines:
    - `c_prime_eq_parity_a_prime`: c' = parity(a'_y over y)
    - `xor_parity_cancellation`: parity(c ⊕ c' ⊕ a'_y over y) = c
    to conclude c_bit[i] = parity of the xor3 bits over y.

    Requires only `RoundLocalConstraints` — no external assumptions. -/
theorem c_bit_eq_parity_xor3
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row)
    (i : ℕ) (hi : i < 320) :
    c_bit air i row =
      fieldXor
        (fieldXor (fieldXor (c_bit air i row) (c_prime_bit air i row))
                  (a_prime_bit air i row))
        (fieldXor
          (fieldXor (fieldXor (c_bit air i row) (c_prime_bit air i row))
                    (a_prime_bit air (i + 320) row))
          (fieldXor
            (fieldXor (fieldXor (c_bit air i row) (c_prime_bit air i row))
                      (a_prime_bit air (i + 640) row))
            (fieldXor
              (fieldXor (fieldXor (c_bit air i row) (c_prime_bit air i row))
                        (a_prime_bit air (i + 960) row))
              (fieldXor (fieldXor (c_bit air i row) (c_prime_bit air i row))
                        (a_prime_bit air (i + 1280) row))))) := by
  -- Get booleanity hypotheses.
  have hc := c_bit_is_bool h_round i hi
  have hc' := c_prime_bit_is_bool h_round i hi
  have hv0 := a_prime_bit_is_bool h_round i (by omega)
  have hv1 := a_prime_bit_is_bool h_round (i + 320) (idx_320_lt i hi)
  have hv2 := a_prime_bit_is_bool h_round (i + 640) (idx_640_lt i hi)
  have hv3 := a_prime_bit_is_bool h_round (i + 960) (idx_960_lt i hi)
  have hv4 := a_prime_bit_is_bool h_round (i + 1280) (idx_1280_lt i hi)
  -- Get the parity relation c' = parity(a'_y).
  have hparity := c_prime_eq_parity_a_prime h_round i hi
  -- Apply the cancellation lemma directly (reversing equality direction).
  exact (xor_parity_cancellation hc hc' hv0 hv1 hv2 hv3 hv4 hparity).symm

end KeccakfPermAir.Soundness
