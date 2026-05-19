/-
  Shared definitions for the KeccakfPermAir single-round correctness proof.

  This file defines:
  • `RoundLocalConstraints` — the conjunction of all rot=0 constraint families
    from Theta/CBits, Theta/CPrime, Theta/APrimeBits, Theta/Linking,
    Theta/Parity, Chi, and Iota.
  • `rowInputState` — semantic input state from the `a` limb columns.
  • `rowOutputState` — semantic output state from the split post-round columns:
    lane [0][0] from `a_ppp_00_limb[0..3]`, all other lanes from `a_prime_prime`.

-/
import VmExtensions.Constraints.KeccakfPermAir.Columns
import VmExtensions.Constraints.KeccakfPermAir.Views
import VmExtensions.Constraints.KeccakfPermAir.Theta.CBits
import VmExtensions.Constraints.KeccakfPermAir.Theta.CPrime
import VmExtensions.Constraints.KeccakfPermAir.Theta.APrimeBits
import VmExtensions.Constraints.KeccakfPermAir.Theta.Linking
import VmExtensions.Constraints.KeccakfPermAir.Theta.Parity
import VmExtensions.Constraints.KeccakfPermAir.Chi
import VmExtensions.Constraints.KeccakfPermAir.Iota
import VmExtensions.Keccak.Spec.Basic
import VmExtensions.Soundness.KeccakfPermAir.FieldLemmas
import OpenvmFv.Fundamentals.BabyBear

set_option autoImplicit false
set_option linter.all false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints
open Keccak

/-! ## Field-level helpers -/

/-- Field-level XOR on two values: `a ⊕ b = a + b - 2ab`.
    When `a, b ∈ {0, 1}`, this is boolean XOR. -/
def fieldXor {F : Type} [CommRing F] (a b : F) : F :=
  a + b - 2 * a * b

/-! ## Chi constraint bundle

The 100 chi constraints (2910–3009) encode the combined ρπ+χ step.
Each constraint is a `chi_recompose16_eq` call with AIR-specific column bases
that bake in the ρπ permutation and rotation offsets.  Two constraints (2996
and 3000) are opaque extraction wrappers.

The fields expose individual chi constraints by name. -/

structure ChiConstraints
    {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : Prop where
  h2910 : constraint_2910 c row
  h2911 : constraint_2911 c row
  h2912 : constraint_2912 c row
  h2913 : constraint_2913 c row
  h2914 : constraint_2914 c row
  h2915 : constraint_2915 c row
  h2916 : constraint_2916 c row
  h2917 : constraint_2917 c row
  h2918 : constraint_2918 c row
  h2919 : constraint_2919 c row
  h2920 : constraint_2920 c row
  h2921 : constraint_2921 c row
  h2922 : constraint_2922 c row
  h2923 : constraint_2923 c row
  h2924 : constraint_2924 c row
  h2925 : constraint_2925 c row
  h2926 : constraint_2926 c row
  h2927 : constraint_2927 c row
  h2928 : constraint_2928 c row
  h2929 : constraint_2929 c row
  h2930 : constraint_2930 c row
  h2931 : constraint_2931 c row
  h2932 : constraint_2932 c row
  h2933 : constraint_2933 c row
  h2934 : constraint_2934 c row
  h2935 : constraint_2935 c row
  h2936 : constraint_2936 c row
  h2937 : constraint_2937 c row
  h2938 : constraint_2938 c row
  h2939 : constraint_2939 c row
  h2940 : constraint_2940 c row
  h2941 : constraint_2941 c row
  h2942 : constraint_2942 c row
  h2943 : constraint_2943 c row
  h2944 : constraint_2944 c row
  h2945 : constraint_2945 c row
  h2946 : constraint_2946 c row
  h2947 : constraint_2947 c row
  h2948 : constraint_2948 c row
  h2949 : constraint_2949 c row
  h2950 : constraint_2950 c row
  h2951 : constraint_2951 c row
  h2952 : constraint_2952 c row
  h2953 : constraint_2953 c row
  h2954 : constraint_2954 c row
  h2955 : constraint_2955 c row
  h2956 : constraint_2956 c row
  h2957 : constraint_2957 c row
  h2958 : constraint_2958 c row
  h2959 : constraint_2959 c row
  h2960 : constraint_2960 c row
  h2961 : constraint_2961 c row
  h2962 : constraint_2962 c row
  h2963 : constraint_2963 c row
  h2964 : constraint_2964 c row
  h2965 : constraint_2965 c row
  h2966 : constraint_2966 c row
  h2967 : constraint_2967 c row
  h2968 : constraint_2968 c row
  h2969 : constraint_2969 c row
  h2970 : constraint_2970 c row
  h2971 : constraint_2971 c row
  h2972 : constraint_2972 c row
  h2973 : constraint_2973 c row
  h2974 : constraint_2974 c row
  h2975 : constraint_2975 c row
  h2976 : constraint_2976 c row
  h2977 : constraint_2977 c row
  h2978 : constraint_2978 c row
  h2979 : constraint_2979 c row
  h2980 : constraint_2980 c row
  h2981 : constraint_2981 c row
  h2982 : constraint_2982 c row
  h2983 : constraint_2983 c row
  h2984 : constraint_2984 c row
  h2985 : constraint_2985 c row
  h2986 : constraint_2986 c row
  h2987 : constraint_2987 c row
  h2988 : constraint_2988 c row
  h2989 : constraint_2989 c row
  h2990 : constraint_2990 c row
  h2991 : constraint_2991 c row
  h2992 : constraint_2992 c row
  h2993 : constraint_2993 c row
  h2994 : constraint_2994 c row
  h2995 : constraint_2995 c row
  h2996 : constraint_2996 c row
  h2997 : constraint_2997 c row
  h2998 : constraint_2998 c row
  h2999 : constraint_2999 c row
  h3000 : constraint_3000 c row
  h3001 : constraint_3001 c row
  h3002 : constraint_3002 c row
  h3003 : constraint_3003 c row
  h3004 : constraint_3004 c row
  h3005 : constraint_3005 c row
  h3006 : constraint_3006 c row
  h3007 : constraint_3007 c row
  h3008 : constraint_3008 c row
  h3009 : constraint_3009 c row

/-! ## RoundLocalConstraints

The conjunction of all rot=0 constraint families needed for the single-round
correctness proof.  Each field documents which imported constraint file it
comes from and what constraint numbers it covers. -/

structure RoundLocalConstraints
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF)
    (row : ℕ) : Prop where

  /-- ### Theta/CBits.lean (constraints 250–569)
  Boolean constraints for all 320 c_bit columns. -/

  c_bit_bool : ∀ i, i < 320 →
    c_bit air i row * (c_bit air i row - 1) = 0

  /-- ### Theta/CPrime.lean (constraints 570–889)
  Each c_prime_bit is the field XOR of three c_bit values:
  c_prime_bit[i] = fieldXor(fieldXor(c_bit[i], c_bit[left(i)]), c_bit[rightShift(i)])
  where left(i) = same bit position in the (x+4)%5 column
  and rightShift(i) = bit (z+63)%64 in the (x+1)%5 column. -/

  c_prime_def : ∀ i, i < 320 →
    let x := i / 64
    let z := i % 64
    let left_idx := 64 * ((x + 4) % 5) + z
    let right_shift_idx := 64 * ((x + 1) % 5) + (z + 63) % 64
    (c_prime_bit air i row) -
      fieldXor (fieldXor (c_bit air i row) (c_bit air left_idx row))
               (c_bit air right_shift_idx row) = 0

  /-- ### Theta/APrimeBits.lean (constraints 890–2489) + Theta/Linking.lean (constraints 2490–2585)
  Boolean constraints for all 1600 a_prime_bit columns.
  APrimeBits.lean covers indices 0–1507, Linking.lean covers 1508–1599. -/

  a_prime_bit_bool : ∀ i, i < 1600 →
    a_prime_bit air i row * (a_prime_bit air i row - 1) = 0

  /-- ### Theta/APrimeBits.lean + Theta/Linking.lean: xor3_recompose16_eq
  For each of the 100 a-limb columns (cols 125–224), the 3-way XOR of
  corresponding c_bit, c_prime_bit, and a_prime_bit chunks recomposes to the
  a column value.  APrimeBits.lean covers output columns 125–216 (j=0..91),
  Linking.lean covers 217–224 (j=92..99).

  The column base formula for limb j:
  - c_bit base:       225 + 64 * ((j/4) % 5) + 16 * (j % 4)
  - c_prime_bit base: 545 + 64 * ((j/4) % 5) + 16 * (j % 4)
  - a_prime_bit base: 865 + 16 * j
  - output a column:  125 + j -/

  theta_xor3_recompose : ∀ j, j < 100 →
    let x := (j / 4) % 5
    let limb := j % 4
    KeccakfPermAir.extraction.xor3_recompose16_eq air
      (225 + 64 * x + 16 * limb)
      (545 + 64 * x + 16 * limb)
      (865 + 16 * j)
      (125 + j)
      row

  /-- ### Theta/Parity.lean (constraints 2590–2909)
  Parity check: for each bit position i (0–319), the sum of five a_prime_bit
  values minus the corresponding c_prime_bit must be in {0, 2, 4}.
  The five a_prime_bit indices are at offsets +320 for each of the five y-rows:
  a_prime_bit[i], [i+320], [i+640], [i+960], [i+1280]. -/

  theta_parity : ∀ i, i < 320 →
    let sum5 := a_prime_bit air i row + a_prime_bit air (i + 320) row +
                a_prime_bit air (i + 640) row + a_prime_bit air (i + 960) row +
                a_prime_bit air (i + 1280) row
    let diff := sum5 - c_prime_bit air i row
    diff * (diff - 2) * (diff - 4) = 0

  /-- ### Chi.lean (constraints 2910–3009)
  All 100 chi constraints, bundled as `ChiConstraints`. -/

  chi : ChiConstraints air row

  /-- ### Iota.lean: boolean constraints (constraints 3010–3073)
  Boolean constraints for all 64 a_pp_00_bit columns. -/

  a_pp_00_bit_bool : ∀ i, i < 64 →
    a_pp_00_bit air i row * (a_pp_00_bit air i row - 1) = 0

  /-- ### Iota.lean: pre-iota recompose (constraints 3074–3077)
  Recompose a_pp_00_bit[0..63] into the first four a_prime_prime columns
  (cols 2465–2468), which are lane [0][0] of the chi output before iota.
  Constraint 3074+k: recompose16_eq c (2565 + 16*k) (2465 + k) row -/

  iota_preiota_recompose : ∀ k, k < 4 →
    KeccakfPermAir.extraction.recompose16_eq air (2565 + 16 * k) (2465 + k) row

  /-- ### Iota.lean: iota output (constraints 3078–3081)
  The final iota-output limbs for lane [0][0] (cols 2629–2632).
  Constraints 3078, 3079, 3081 are opaque extraction wrappers.
  Constraint 3080 is a visible recompose16_eq targeting col 2631. -/

  iota_output_3078 : constraint_3078 air row
  iota_output_3079 : constraint_3079 air row
  iota_output_3080 : constraint_3080 air row
  iota_output_3081 : constraint_3081 air row

/-! ## State reconstruction

Convert field-valued AIR columns to spec-level `State` (25 UInt64 lanes).
Each lane is reconstructed from 4 u16 limbs in little-endian order:
  lane = limb0 + limb1 * 2^16 + limb2 * 2^32 + limb3 * 2^48.

The field values are BabyBear elements (Fin BB_prime).  `Fin.val` gives
the natural number, and `UInt16.ofNat` truncates to 16 bits.  Under the
proof's constraints, the limb values actually fit in 16 bits, so no
information is lost.
-/

/-- Convert a BabyBear field element to UInt16 by taking its natural value
    modulo 2^16.  Under boolean + recompose constraints, the value fits. -/
def fieldToU16 (x : FBB) : UInt16 :=
  x.val.toUInt16

/-- Pack four u16 limbs into one UInt64 lane (little-endian):
    lane = l0 + l1 * 2^16 + l2 * 2^32 + l3 * 2^48. -/
def limbs4ToU64 (l0 l1 l2 l3 : UInt16) : UInt64 :=
  l0.toUInt64 ||| (l1.toUInt64 <<< 16) |||
  (l2.toUInt64 <<< 32) ||| (l3.toUInt64 <<< 48)

/-- Reconstruct a single lane from four field-valued limb columns.
    Applies `fieldToU16` to each limb and packs them little-endian. -/
def laneOfLimbs (l0 l1 l2 l3 : FBB) : UInt64 :=
  limbs4ToU64 (fieldToU16 l0) (fieldToU16 l1) (fieldToU16 l2) (fieldToU16 l3)

/-! ### rowInputState -/

/-- The semantic input state reconstructed from the `a` limb columns
    (cols 125–224) at this row.

    Lane `(x, y)` at flat index `5*y + x` is reconstructed from:
      a[4*(5*y+x) + 0], a[4*(5*y+x) + 1], a[4*(5*y+x) + 2], a[4*(5*y+x) + 3]
    using the little-endian 4×u16 per lane convention.

    This is the same convention as the bus-state bridge in `Spec.lean`. -/
def rowInputState
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF)
    (row : ℕ) : State :=
  ⟨Array.ofFn fun (i : Fin 25) =>
    let base := 4 * i.val
    laneOfLimbs (a air base row) (a air (base + 1) row)
                (a air (base + 2) row) (a air (base + 3) row),
   by simp⟩

/-! ### rowOutputState -/

/-- The semantic output state reconstructed from the split post-round columns.

    Lane `[0][0]` (flat index 0) comes from `a_ppp_00_limb[0..3]`
    (cols 2629–2632), the iota-updated output.

    All other lanes `(x, y)` with `5*y + x ≠ 0` come from
    `a_prime_prime[4*(5*y+x) + 0..3]` (cols 2465–2564), the chi output.

    Both use the same little-endian 4×u16 per lane convention. -/
def rowOutputState
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF)
    (row : ℕ) : State :=
  ⟨Array.ofFn fun (i : Fin 25) =>
    if i.val = 0 then
      -- Lane [0][0]: from a_ppp_00_limb[0..3] (iota output)
      laneOfLimbs (a_ppp_00_limb air 0 row) (a_ppp_00_limb air 1 row)
                  (a_ppp_00_limb air 2 row) (a_ppp_00_limb air 3 row)
    else
      -- All other lanes: from a_prime_prime[4*i + 0..3] (chi output)
      let base := 4 * i.val
      laneOfLimbs (a_prime_prime air base row) (a_prime_prime air (base + 1) row)
                  (a_prime_prime air (base + 2) row) (a_prime_prime air (base + 3) row),
   by simp⟩

/-! ## Convenience projections -/

/-- Reduce subscript on `Arr25` anonymous constructor to array subscript. -/
@[simp] private theorem arr25_getElem_mk (arr : Array UInt64) (h : arr.size = 25)
    (i : Nat) (hi : i < 25) :
    (⟨arr, h⟩ : Arr25)[i]'hi = arr[i]'(h ▸ hi) := rfl

/-- Extract a single input lane from the row. -/
theorem rowInputState_lane
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF)
    (row : ℕ) (i : Fin 25) :
    (rowInputState air row)[i.val]'(by omega) =
      laneOfLimbs (a air (4 * i.val) row) (a air (4 * i.val + 1) row)
                  (a air (4 * i.val + 2) row) (a air (4 * i.val + 3) row) := by
  simp only [rowInputState, arr25_getElem_mk, Array.getElem_ofFn]

/-- Output lane [0][0] comes from the iota-updated a_ppp_00_limb columns. -/
theorem rowOutputState_lane_zero
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF)
    (row : ℕ) :
    (rowOutputState air row)[0]'(by omega) =
      laneOfLimbs (a_ppp_00_limb air 0 row) (a_ppp_00_limb air 1 row)
                  (a_ppp_00_limb air 2 row) (a_ppp_00_limb air 3 row) := by
  simp only [rowOutputState, arr25_getElem_mk, Array.getElem_ofFn, ite_true]

/-- Output lane at nonzero index comes from the a_prime_prime columns. -/
theorem rowOutputState_lane_nonzero
    {ExtF : Type} [Field ExtF]
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF)
    (row : ℕ) (i : Fin 25) (hi : i.val ≠ 0) :
    (rowOutputState air row)[i.val]'(by omega) =
      laneOfLimbs (a_prime_prime air (4 * i.val) row) (a_prime_prime air (4 * i.val + 1) row)
                  (a_prime_prime air (4 * i.val + 2) row) (a_prime_prime air (4 * i.val + 3) row) := by
  simp only [rowOutputState, arr25_getElem_mk, Array.getElem_ofFn]
  rw [if_neg hi]

end KeccakfPermAir.Soundness
