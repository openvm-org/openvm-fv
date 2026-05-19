/-
  Field-to-spec bridge and boolean recognition facts for the
  KeccakfPermAir single-round correctness proof.

  This file provides:
  • Boolean recognition: `c_bit`, `a_prime_bit`, and `a_pp_00_bit` are in {0, 1}.
  • BabyBear binary value bridge: boolean FBB elements have `.val` in {0, 1}.
  • `recompose16_eq` value extraction: turns `(sum − out) = 0` into `out = sum`.
  • `recompose16_fieldToU16`: bridge from recompose16_eq + boolean bits to
    `fieldToU16` / u16 reconstruction.
  • `laneOfLimbs_eq`: 4×u16 limb reconstruction stated against `laneOfLimbs`.
  • Lane-level lemmas connecting to `rowInputState` and `rowOutputState`.
  • State extensionality: two states are equal iff all 25 lanes agree.

-/
import VmExtensions.Soundness.KeccakfPermAir.Round.Surface

set_option autoImplicit false
set_option linter.all false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints
open Keccak

/-! ## Boolean recognition

From the `b * (b − 1) = 0` constraints in `RoundLocalConstraints`, derive
`b = 0 ∨ b = 1` using `binary_of_mul_sub_one_eq_zero`.

These are the starting point for XOR, parity, and
recomposition reasoning.  Note that `c_prime_bit` booleanity is NOT proved
here—it is deferred to `ThetaCPrime.lean` where it follows from the
explicit XOR formula in `Theta/CPrime.lean`. -/

/-- Each `c_bit` column is boolean (0 or 1) at this row.
    Proof: apply the field-algebra factoring lemma to the `b*(b-1)=0`
    constraint from `h_round.c_bit_bool`. -/
theorem c_bit_is_bool
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (i : ℕ) (hi : i < 320) :
    c_bit air i row = 0 ∨ c_bit air i row = 1 :=
  binary_of_mul_sub_one_eq_zero (h_round.c_bit_bool i hi)

/-- Each `a_prime_bit` column is boolean (0 or 1) at this row.
    Proof: same factoring lemma on `h_round.a_prime_bit_bool`. -/
theorem a_prime_bit_is_bool
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (i : ℕ) (hi : i < 1600) :
    a_prime_bit air i row = 0 ∨ a_prime_bit air i row = 1 :=
  binary_of_mul_sub_one_eq_zero (h_round.a_prime_bit_bool i hi)

/-- Each `a_pp_00_bit` column is boolean (0 or 1) at this row.
    Proof: same factoring lemma on `h_round.a_pp_00_bit_bool`. -/
theorem a_pp_00_bit_is_bool
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (i : ℕ) (hi : i < 64) :
    a_pp_00_bit air i row = 0 ∨ a_pp_00_bit air i row = 1 :=
  binary_of_mul_sub_one_eq_zero (h_round.a_pp_00_bit_bool i hi)

/-! ## BabyBear binary value bridge

When an FBB element is known to be 0 or 1 in the field, its `.val`
(as a natural number) is 0 or 1.  This lets callers convert
field-level booleanity into natural-number-level booleanity for
`StepLimbs` and spec-level reasoning. -/

/-- A boolean FBB element has `.val` in {0, 1}.
    Proof: case split on `x = 0` vs `x = 1`; in each case the `.val`
    reduces to the expected natural number. -/
theorem binary_fbb_val {x : FBB} (h : x = 0 ∨ x = 1) :
    x.val = 0 ∨ x.val = 1 := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## `recompose16_eq` value extraction

The `recompose16_eq` constraint says
`(∑_{i=0}^{15} 2^i * bit[i]) − output = 0`.
Rearranging gives `output = ∑ 2^i * bit[i]` as a field equality.

This is the algebraic bridge that connects raw polynomial constraints to
the little-endian binary sum interpretation used by `fieldToU16` and
`laneOfLimbs`.  Booleanity of the bits is not required here—only the
polynomial identity matters. -/

/-- `recompose16_eq` expressed as: output = little-endian binary sum of 16 bits.
    Proof: the constraint says `(sum − out) = 0`, so `out = sum` by
    `sub_eq_zero`. -/
theorem recompose16_eq_value {F ExtF : Type} [Field F] [Field ExtF]
    {C : Type → Type → Type} [Circuit F ExtF C]
    {c : C F ExtF} {bit_base output_col row : ℕ}
    (h : KeccakfPermAir.extraction.recompose16_eq c bit_base output_col row) :
    let b (i : ℕ) := Circuit.main c (id := 0) (column := bit_base + i) (row := row) (rotation := 0)
    Circuit.main c (id := 0) (column := output_col) (row := row) (rotation := 0) =
    b 0 + 2 * b 1 + 4 * b 2 + 8 * b 3 + 16 * b 4 + 32 * b 5 + 64 * b 6 + 128 * b 7 +
    256 * b 8 + 512 * b 9 + 1024 * b 10 + 2048 * b 11 + 4096 * b 12 + 8192 * b 13 +
    16384 * b 14 + 32768 * b 15 := by
  -- After unfolding, h : (sum - out) = 0. Then sub_eq_zero.mp gives sum = out.
  simp only [KeccakfPermAir.extraction.recompose16_eq] at h
  exact (sub_eq_zero.mp h).symm

/-! ## `recompose16_eq` → `fieldToU16` bridge

When `recompose16_eq` holds and the 16 bits are all boolean (0 or 1 in FBB),
the output column's `fieldToU16` equals the little-endian natural-number sum.
This bridges the field-level recompose constraint to the u16 reconstruction
used by `laneOfLimbs` and ultimately by `rowInputState` / `rowOutputState`.

The key insight: for boolean FBB bits, `b.val` is 0 or 1, so the field sum
`∑ 2^i * b[i]` has `.val` equal to `∑ 2^i * b[i].val`, which fits in 16 bits
(max value 65535 < BB_prime).  Then `fieldToU16` = `Nat.toUInt16` is lossless.
-/

/-- Helper: boolean FBB has `.val ≤ 1`. -/
theorem fbb_bool_val_le {x : FBB} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by
  rcases binary_fbb_val h with h | h <;> omega

set_option maxHeartbeats 800000 in
/-- When `recompose16_eq` holds and the 16 input bits are boolean, the output
    column's `fieldToU16` equals the little-endian u16 of the bits' natural values.

    This bridge lemma converts
    field equality (`recompose16_eq`) + booleanity to `fieldToU16 out = ...`.

    Stated on abstract FBB values to avoid `Circuit.main` synthesis issues.
    Usage: obtain `heq` from `recompose16_eq_value`, supply booleanity of bits. -/
theorem recompose16_fieldToU16
    (out : FBB) (b : Fin 16 → FBB)
    (hbool : ∀ i, b i = 0 ∨ b i = 1)
    (heq : out = b ⟨0, by omega⟩ + 2 * b ⟨1, by omega⟩ + 4 * b ⟨2, by omega⟩ +
                 8 * b ⟨3, by omega⟩ + 16 * b ⟨4, by omega⟩ + 32 * b ⟨5, by omega⟩ +
                 64 * b ⟨6, by omega⟩ + 128 * b ⟨7, by omega⟩ +
                 256 * b ⟨8, by omega⟩ + 512 * b ⟨9, by omega⟩ +
                 1024 * b ⟨10, by omega⟩ + 2048 * b ⟨11, by omega⟩ +
                 4096 * b ⟨12, by omega⟩ + 8192 * b ⟨13, by omega⟩ +
                 16384 * b ⟨14, by omega⟩ + 32768 * b ⟨15, by omega⟩) :
    fieldToU16 out = (
      (b ⟨0, by omega⟩).val + 2 * (b ⟨1, by omega⟩).val +
      4 * (b ⟨2, by omega⟩).val + 8 * (b ⟨3, by omega⟩).val +
      16 * (b ⟨4, by omega⟩).val + 32 * (b ⟨5, by omega⟩).val +
      64 * (b ⟨6, by omega⟩).val + 128 * (b ⟨7, by omega⟩).val +
      256 * (b ⟨8, by omega⟩).val + 512 * (b ⟨9, by omega⟩).val +
      1024 * (b ⟨10, by omega⟩).val + 2048 * (b ⟨11, by omega⟩).val +
      4096 * (b ⟨12, by omega⟩).val + 8192 * (b ⟨13, by omega⟩).val +
      16384 * (b ⟨14, by omega⟩).val + 32768 * (b ⟨15, by omega⟩).val).toUInt16 := by
  unfold fieldToU16; rw [heq]; congr 1
  have hle : ∀ i, (b i).val ≤ 1 := fun i => fbb_bool_val_le (hbool i)
  -- For Fin n, (a + b).val = (a.val + b.val) % n and (a * b).val = (a.val * b.val) % n.
  -- We need to show that the nested % BB_prime all simplify away because
  -- every intermediate value is < BB_prime.  We unfold to % form then use
  -- Nat.mod_eq_of_lt at each step, building up via an omega chain.
  -- Helper: (c : FBB).val = c % BB_prime for nat literal c
  -- For each step: (prev + (w : FBB) * b_k).val
  --   = (prev.val + ((w : FBB) * b_k).val) % BB_prime
  --   = (prev.val + (w % BB_prime * (b_k).val) % BB_prime) % BB_prime
  -- All simplify to prev.val + w * (b_k).val when < BB_prime.
  --
  -- We prove by chaining: define n_k = the nat partial sum, and show s_k.val = n_k.
  -- Use `show` to match the Fin.add/mul unfoldings.
  -- Step-by-step proof: for each partial sum, show .val = nat sum.
  -- s_k = s_{k-1} + (2^k : FBB) * b_k
  -- s_k.val = (s_{k-1}.val + ((2^k : FBB) * b_k).val) % BB_prime
  -- ((2^k : FBB) * b_k).val = (2^k % BB_prime * (b_k).val) % BB_prime
  -- Since 2^k < BB_prime and (b_k).val ≤ 1, the product is < BB_prime.
  -- Since s_{k-1}.val ≤ 2^k - 1 and the product ≤ 2^k, sum < 2^{k+1} ≤ 65536 < BB_prime.
  -- So all % BB_prime are identity.
  -- We can express this as a sequence of `have` lemmas.
  -- Use abbreviations for clarity.
  have p := BB_eq.symm  -- BB_prime = 2013265921
  -- Step 0: s0.val = b0.val
  -- This is definitional (s0 = b0)
  -- Step 1: (b0 + 2*b1).val = b0.val + 2 * b1.val
  -- (b0 + 2*b1).val = (b0.val + (2*b1).val) % P
  -- (2*b1).val = (2 % P * b1.val) % P = (2 * b1.val) % P = 2 * b1.val (since ≤ 2 < P)
  -- b0.val + 2 * b1.val ≤ 1 + 2 = 3 < P, so % P is id.
  -- We use `show` + `Nat.mod_eq_of_lt` + `omega`.

  -- Actually, the cleanest way: prove a helper that does one step.
  -- add_step : s.val = n → n + w * (b k).val < BB_prime → w < BB_prime →
  --            (s + (w : FBB) * b k).val = n + w * (b k).val
  suffices key : ∀ (s : FBB) (n w : ℕ) (k : Fin 16),
      s.val = n → w < BB_prime → n + w * (b k).val < BB_prime →
      (s + (w : FBB) * b k).val = n + w * (b k).val by
    -- Now chain the 15 additions (b0 is the base, then +2*b1, +4*b2, ..., +32768*b15).
    have h0 : (b ⟨0, by omega⟩).val = (b ⟨0, by omega⟩).val := rfl
    have h1 := key _ _ 2 ⟨1, by omega⟩ h0 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; omega)
    have h2 := key _ _ 4 ⟨2, by omega⟩ h1 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; omega)
    have h3 := key _ _ 8 ⟨3, by omega⟩ h2 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; omega)
    have h4 := key _ _ 16 ⟨4, by omega⟩ h3 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; omega)
    have h5 := key _ _ 32 ⟨5, by omega⟩ h4 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; omega)
    have h6 := key _ _ 64 ⟨6, by omega⟩ h5 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; have := hle ⟨6, by omega⟩; omega)
    have h7 := key _ _ 128 ⟨7, by omega⟩ h6 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; have := hle ⟨6, by omega⟩; have := hle ⟨7, by omega⟩; omega)
    have h8 := key _ _ 256 ⟨8, by omega⟩ h7 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; have := hle ⟨6, by omega⟩; have := hle ⟨7, by omega⟩; have := hle ⟨8, by omega⟩; omega)
    have h9 := key _ _ 512 ⟨9, by omega⟩ h8 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; have := hle ⟨6, by omega⟩; have := hle ⟨7, by omega⟩; have := hle ⟨8, by omega⟩; have := hle ⟨9, by omega⟩; omega)
    have h10 := key _ _ 1024 ⟨10, by omega⟩ h9 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; have := hle ⟨6, by omega⟩; have := hle ⟨7, by omega⟩; have := hle ⟨8, by omega⟩; have := hle ⟨9, by omega⟩; have := hle ⟨10, by omega⟩; omega)
    have h11 := key _ _ 2048 ⟨11, by omega⟩ h10 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; have := hle ⟨6, by omega⟩; have := hle ⟨7, by omega⟩; have := hle ⟨8, by omega⟩; have := hle ⟨9, by omega⟩; have := hle ⟨10, by omega⟩; have := hle ⟨11, by omega⟩; omega)
    have h12 := key _ _ 4096 ⟨12, by omega⟩ h11 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; have := hle ⟨6, by omega⟩; have := hle ⟨7, by omega⟩; have := hle ⟨8, by omega⟩; have := hle ⟨9, by omega⟩; have := hle ⟨10, by omega⟩; have := hle ⟨11, by omega⟩; have := hle ⟨12, by omega⟩; omega)
    have h13 := key _ _ 8192 ⟨13, by omega⟩ h12 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; have := hle ⟨6, by omega⟩; have := hle ⟨7, by omega⟩; have := hle ⟨8, by omega⟩; have := hle ⟨9, by omega⟩; have := hle ⟨10, by omega⟩; have := hle ⟨11, by omega⟩; have := hle ⟨12, by omega⟩; have := hle ⟨13, by omega⟩; omega)
    have h14 := key _ _ 16384 ⟨14, by omega⟩ h13 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; have := hle ⟨6, by omega⟩; have := hle ⟨7, by omega⟩; have := hle ⟨8, by omega⟩; have := hle ⟨9, by omega⟩; have := hle ⟨10, by omega⟩; have := hle ⟨11, by omega⟩; have := hle ⟨12, by omega⟩; have := hle ⟨13, by omega⟩; have := hle ⟨14, by omega⟩; omega)
    exact key _ _ 32768 ⟨15, by omega⟩ h14 (by norm_num) (by have := hle ⟨0, by omega⟩; have := hle ⟨1, by omega⟩; have := hle ⟨2, by omega⟩; have := hle ⟨3, by omega⟩; have := hle ⟨4, by omega⟩; have := hle ⟨5, by omega⟩; have := hle ⟨6, by omega⟩; have := hle ⟨7, by omega⟩; have := hle ⟨8, by omega⟩; have := hle ⟨9, by omega⟩; have := hle ⟨10, by omega⟩; have := hle ⟨11, by omega⟩; have := hle ⟨12, by omega⟩; have := hle ⟨13, by omega⟩; have := hle ⟨14, by omega⟩; have := hle ⟨15, by omega⟩; omega)
  -- Prove the helper
  intro s n w k hs hw hlt
  show (s.val + ((w : FBB) * b k).val) % BB_prime = n + w * (b k).val
  -- ((w : FBB) * b k).val = (w % BB_prime * (b k).val) % BB_prime
  show (s.val + (((w : FBB).val * (b k).val) % BB_prime)) % BB_prime = n + w * (b k).val
  rw [show (w : FBB).val = w % BB_prime from rfl, Nat.mod_eq_of_lt hw]
  have hbk := hle k
  rw [Nat.mod_eq_of_lt (by omega : w * (b k).val < BB_prime)]
  rw [hs, Nat.mod_eq_of_lt hlt]

/-! ## 4×u16 → lane reconstruction (`laneOfLimbs`)

Given four field limb values whose `fieldToU16` are known, show that
`laneOfLimbs` produces the expected `UInt64` lane. This lemma connects
per-limb `fieldToU16` facts to a single lane equality. -/

/-- Four field limbs combine to a lane via `laneOfLimbs`.
    When the `fieldToU16` of each limb is known, `laneOfLimbs` equals
    `limbs4ToU64` applied to those u16 values. -/
theorem laneOfLimbs_eq (l0 l1 l2 l3 : FBB)
    (v0 v1 v2 v3 : UInt16)
    (h0 : fieldToU16 l0 = v0) (h1 : fieldToU16 l1 = v1)
    (h2 : fieldToU16 l2 = v2) (h3 : fieldToU16 l3 = v3) :
    laneOfLimbs l0 l1 l2 l3 = limbs4ToU64 v0 v1 v2 v3 := by
  unfold laneOfLimbs
  rw [h0, h1, h2, h3]

/-! ## Lane-level state connection lemmas

These lemmas connect `laneOfLimbs` equalities to entries in `rowInputState`
and `rowOutputState`. Given per-limb `fieldToU16` facts, `laneOfLimbs_eq`
produces lane equalities, and these lemmas rewrite them into state-level
equalities closed by `state_ext`. -/

/-- If `laneOfLimbs` of the four `a` limbs for flat index `i` equals some
    value `v`, then the `i`-th input lane equals `v`. -/
theorem rowInputState_lane_eq
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF)
    (row : ℕ) (i : Fin 25) (v : UInt64)
    (h : laneOfLimbs (a air (4 * i.val) row) (a air (4 * i.val + 1) row)
                     (a air (4 * i.val + 2) row) (a air (4 * i.val + 3) row) = v) :
    (rowInputState air row)[i.val]'(by omega) = v := by
  rw [rowInputState_lane]; exact h

/-- If `laneOfLimbs` of the four `a_ppp_00_limb` columns equals `v`,
    then the output lane at index 0 equals `v`. -/
theorem rowOutputState_lane_zero_eq
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF)
    (row : ℕ) (v : UInt64)
    (h : laneOfLimbs (a_ppp_00_limb air 0 row) (a_ppp_00_limb air 1 row)
                     (a_ppp_00_limb air 2 row) (a_ppp_00_limb air 3 row) = v) :
    (rowOutputState air row)[0]'(by omega) = v := by
  rw [rowOutputState_lane_zero]; exact h

/-- If `laneOfLimbs` of the four `a_prime_prime` limbs for nonzero flat index
    `i` equals `v`, then the `i`-th output lane equals `v`. -/
theorem rowOutputState_lane_nonzero_eq
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF)
    (row : ℕ) (i : Fin 25) (hi : i.val ≠ 0) (v : UInt64)
    (h : laneOfLimbs (a_prime_prime air (4 * i.val) row)
                     (a_prime_prime air (4 * i.val + 1) row)
                     (a_prime_prime air (4 * i.val + 2) row)
                     (a_prime_prime air (4 * i.val + 3) row) = v) :
    (rowOutputState air row)[i.val]'(by omega) = v := by
  rw [rowOutputState_lane_nonzero air row i hi]; exact h

/-! ## State extensionality

States (`Arr25`) are arrays of 25 `UInt64` lanes.  To prove two states
are equal, it suffices to prove all 25 lanes agree.  This lets
assembly proofs close state equalities from lane-by-lane
theorems (e.g., 24 nonzero lanes from `ChiFacts` + lane [0][0] from
`IotaFacts`). -/

/-- Two states are equal iff all their lanes agree.
    Proof: `Subtype.ext` reduces to array equality, then `Array.ext`
    reduces to pointwise lane equality. -/
theorem state_ext (s1 s2 : State)
    (h : ∀ i : Fin 25, s1[i.val]'(by omega) = s2[i.val]'(by omega)) :
    s1 = s2 := by
  apply Subtype.ext
  apply Array.ext
  · rw [s1.property, s2.property]
  · intro i h1 h2
    exact h ⟨i, s1.property ▸ h1⟩

end KeccakfPermAir.Soundness
