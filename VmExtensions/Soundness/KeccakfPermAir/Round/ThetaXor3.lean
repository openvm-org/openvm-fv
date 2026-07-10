/-
  Raw xor3-linking interface for the KeccakfPermAir single-round correctness
  proof.

  This lower-level helper exposes the raw theta xor3 relation without the
  full theta-state interface.

  Provides:
  • `xor3_recompose16_eq_value`: converts the raw `xor3_recompose16_eq`
    constraint `(sum − out) = 0` into an equality `out = xor3-weighted-sum`.
  • `theta_a_eq_xor3_recompose`: for each limb j ∈ [0, 100), the `a` column
    at index j equals the 16-bit xor3 recomposition of corresponding c_bit,
    c_prime_bit, and a_prime_bit chunks.
  • `theta_xor3_raw`: for each limb j ∈ [0, 100), the raw
    `xor3_recompose16_eq` constraint holds, as a direct projection from
    `RoundLocalConstraints`.

-/
import VmExtensions.Soundness.KeccakfPermAir.Round.Surface

set_option autoImplicit false
set_option linter.all false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints

/-! ## `xor3_recompose16_eq` value extraction

The `xor3_recompose16_eq` constraint says:
  `(∑_{i=0}^{15} 2^i * xor3(A[i], B[i], C[i])) − output = 0`
where `xor3(a, b, c) = a + b + c − 2ab − 2ac − 2bc + 4abc` is the
three-input boolean XOR polynomial.

Rearranging gives `output = ∑ 2^i * xor3(A[i], B[i], C[i])` as a
field equality.  This is the XOR-recomposition analogue of
`recompose16_eq_value` from BooleanFacts.lean. -/

/-- `xor3_recompose16_eq` expressed as: output = little-endian weighted sum
    of 16 three-way XOR values.
    Proof: the constraint says `(sum − out) = 0`, so `out = sum` by
    `sub_eq_zero`. -/
theorem xor3_recompose16_eq_value {F ExtF : Type} [Field F] [Field ExtF]
    {C : Type → Type → Type} [Circuit F ExtF C]
    {c : C F ExtF} {a_base b_base c_base output_col row : ℕ}
    (h : KeccakfPermAir.extraction.xor3_recompose16_eq c a_base b_base c_base output_col row) :
    let a (i : ℕ) := Circuit.main c (id := 0) (column := a_base + i) (row := row) (rotation := 0)
    let b (i : ℕ) := Circuit.main c (id := 0) (column := b_base + i) (row := row) (rotation := 0)
    let d (i : ℕ) := Circuit.main c (id := 0) (column := c_base + i) (row := row) (rotation := 0)
    let x3 (i : ℕ) :=
      a i + b i + d i - 2 * a i * b i - 2 * a i * d i - 2 * b i * d i + 4 * a i * b i * d i
    Circuit.main c (id := 0) (column := output_col) (row := row) (rotation := 0) =
    x3 0 + 2 * x3 1 + 4 * x3 2 + 8 * x3 3 + 16 * x3 4 + 32 * x3 5 + 64 * x3 6 + 128 * x3 7 +
    256 * x3 8 + 512 * x3 9 + 1024 * x3 10 + 2048 * x3 11 + 4096 * x3 12 + 8192 * x3 13 +
    16384 * x3 14 + 32768 * x3 15 := by
  -- After unfolding, h : (sum - out) = 0.  Then sub_eq_zero.mp gives sum = out.
  simp only [KeccakfPermAir.extraction.xor3_recompose16_eq] at h
  exact (sub_eq_zero.mp h).symm

/-! ## `theta_a_eq_xor3_recompose`: value-level linking over the full range

For each limb j ∈ [0, 100) the `a` column at flat index j equals the
16-bit xor3 recomposition of corresponding chunks from three bit-column
families (using column abbreviations from `Columns.lean`):
- `c_bit` at offset `64 * x + 16 * limb + i`
- `c_prime_bit` at offset `64 * x + 16 * limb + i`
- `a_prime_bit` at offset `16 * j + i`

where `x = (j / 4) % 5` and `limb = j % 4`.

This covers the full `a`-column range 125..224 with no gap at the
216/217 boundary. -/

/-- For each limb j < 100, the `a` column at index j equals the 16-bit
    xor3 recomposition of corresponding c_bit, c_prime_bit, and a_prime_bit
    chunks.  This is the raw chunkwise relation `a = c ⊕ c' ⊕ a'` at the
    limb level.

    The column offsets (into their respective families) are:
    - c_bit / c_prime_bit: `64 * ((j/4) % 5) + 16 * (j % 4) + i`
    - a_prime_bit:          `16 * j + i`

    Proof: extract `theta_xor3_recompose` from `RoundLocalConstraints`,
    apply `xor3_recompose16_eq_value` to convert `(sum − out) = 0` to
    `out = sum`, then reconcile column abbreviations with Circuit.main
    via Nat addition associativity. -/
theorem theta_a_eq_xor3_recompose
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (j : ℕ) (hj : j < 100) :
    let x := (j / 4) % 5
    let limb := j % 4
    let cbi (i : ℕ) := c_bit air (64 * x + 16 * limb + i) row
    let cpbi (i : ℕ) := c_prime_bit air (64 * x + 16 * limb + i) row
    let apbi (i : ℕ) := a_prime_bit air (16 * j + i) row
    let x3 (i : ℕ) :=
      cbi i + cpbi i + apbi i -
      2 * cbi i * cpbi i - 2 * cbi i * apbi i - 2 * cpbi i * apbi i +
      4 * cbi i * cpbi i * apbi i
    a air j row =
    x3 0 + 2 * x3 1 + 4 * x3 2 + 8 * x3 3 + 16 * x3 4 + 32 * x3 5 + 64 * x3 6 + 128 * x3 7 +
    256 * x3 8 + 512 * x3 9 + 1024 * x3 10 + 2048 * x3 11 + 4096 * x3 12 + 8192 * x3 13 +
    16384 * x3 14 + 32768 * x3 15 := by
  -- Step 1: Extract the xor3_recompose16_eq constraint and convert to equality.
  have hx := h_round.theta_xor3_recompose j hj
  simp only at hx
  have hval := xor3_recompose16_eq_value hx
  -- Step 2: hval is in terms of Circuit.main with column = (base + offset) + i.
  -- The goal uses column abbreviations with column = base + (offset + i).
  -- Unfold abbreviations to Circuit.main, then normalize Nat.add associativity
  -- so both sides use the same grouping.
  dsimp only [a, c_bit, c_prime_bit, a_prime_bit] at hval ⊢
  simp only [Nat.add_assoc] at hval ⊢
  exact hval

/-! ## Raw linking theorem: unified xor3 recomposition over the full range

For each limb j ∈ [0, 100) the xor3 recomposition constraint holds between:
- `c_bit` at base `225 + 64 * x + 16 * limb`
- `c_prime_bit` at base `545 + 64 * x + 16 * limb`
- `a_prime_bit` at base `865 + 16 * j`
- output `a` at column `125 + j`

where `x = (j / 4) % 5` and `limb = j % 4`.

This covers the full `a`-column range 125..224 (j = 0..99)
with no gap at the 216/217 boundary.  The split between `Theta/APrimeBits.lean`
(j = 0..91) and `Theta/Linking.lean` (j = 92..99) is hidden behind the
unified `theta_xor3_recompose` field of `RoundLocalConstraints`.

Use `xor3_recompose16_eq_value` with `theta_xor3_raw` to get the equality
form. -/

/-- For each limb j < 100, the `xor3_recompose16_eq` constraint holds
    between the c_bit, c_prime_bit, and a_prime_bit bit-column chunks
    and the `a` limb column at index 125 + j.

    This is the raw chunkwise relation `a = c ⊕ c' ⊕ a'` at the limb
    level.

    Proof: direct projection from the `RoundLocalConstraints` bundle. -/
theorem theta_xor3_raw
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (j : ℕ) (hj : j < 100) :
    let x := (j / 4) % 5
    let limb := j % 4
    KeccakfPermAir.extraction.xor3_recompose16_eq air
      (225 + 64 * x + 16 * limb)
      (545 + 64 * x + 16 * limb)
      (865 + 16 * j)
      (125 + j)
      row := by
  -- Direct projection from the RoundLocalConstraints bundle.
  have hx := h_round.theta_xor3_recompose j hj
  simp only at hx
  exact hx

end KeccakfPermAir.Soundness
