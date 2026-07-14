/-
  Iota step for the KeccakfPermAir single-round correctness proof.

  **Semantic role of constraints 3078, 3079, 3080, 3081 (iota output limbs)**:

  Constraints 3074–3077 recompose the 64 `a_pp_00_bit` witness bits into
  `a_prime_prime[0..3]` (the pre-iota chi-output lane [0][0]).

  Constraints 3078–3081 compute the four final-output limbs
  `a_ppp_00_limb[0..3]` by XORing those same witness bits with the
  round-constant bits selected by the step flags:

  • constraint_3078 → a_ppp_00_limb[0] (col 2629):
    XORs RC bits 0, 1, 3, 7, 15 via step-flag sums into the u16 recomposition.
    Bits 2, 4–6, 8–14 are plain (always-zero RC bits).

  • constraint_3079 → a_ppp_00_limb[1] (col 2630):
    Only RC bit 31 (bit 15 of limb 1) is XORed via a step-flag sum.
    Bits 16–30 are plain.

  • constraint_3080 → a_ppp_00_limb[2] (col 2631):
    Plain `recompose16_eq` — no round-constant bits in positions 32–47
    for any of the 24 Keccak round constants.

  • constraint_3081 → a_ppp_00_limb[3] (col 2632):
    Only RC bit 63 (bit 15 of limb 3) is XORed via a step-flag sum.
    Bits 48–62 are plain.

  Under the one-hot step-flag hypothesis `h_step`, each flag sum
  collapses to 0 or 1, matching the corresponding bit of
  `roundConstants[round.val]`.  Combined with `chi_preiota_lane_zero`
  from ChiFacts.lean, this identifies the final lane [0][0] with the
  spec-level `ι` update.

  Exports:
  • `iota_lane_zero` — (rowOutputState air row)[0] =
      (ι (χ (ρπ (θ (rowInputState air row)))) round.val ...)[0]

  The only step-flag hypothesis in the public interface is `h_step`.
  This file does not duplicate nonzero-lane claims from ChiFacts.lean.
-/
import VmExtensions.Soundness.KeccakfPermAir.Round.ChiFacts
import VmExtensions.Soundness.KeccakfPermAir.Round.BooleanFacts

set_option autoImplicit false
set_option linter.all false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints
open KeccakfPermAir.StepLimbs
open Keccak

/-! ## Iota Horner-peeling lemmas

The openvm v2.0.0 extraction emits `constraint_3078/3079/3081` as nested Horner
`inter_*` accumulator chains rather than a form definitionally equal to the
`fieldXor`/`a_pp_00_bit` recomposition.  Each `peel_iota_<cnum>` keeps the
accumulators opaque and telescopes the recursion one bit at a time (mixed plain
and RC-xor bits), abstracting the columns to an opaque `mc` so the `ring` steps
never unfold the concrete `Circuit` instance dictionary. -/

private theorem peel_iota_3078 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3078 c row) :
    mc 2629 = fieldXor (mc 2565) (mc 0 + mc 4 + mc 5 + mc 6 + mc 7 + mc 10 + mc 12 + mc 13 + mc 14 + mc 15 + mc 20 + mc 22) + 2 * fieldXor (mc 2566) (mc 1 + mc 2 + mc 4 + mc 8 + mc 11 + mc 12 + mc 13 + mc 15 + mc 16 + mc 18 + mc 19) + 4 * mc 2567 + 8 * fieldXor (mc 2568) (mc 2 + mc 4 + mc 7 + mc 8 + mc 9 + mc 10 + mc 11 + mc 12 + mc 13 + mc 14 + mc 18 + mc 19 + mc 23) + 16 * mc 2569 + 32 * mc 2570 + 64 * mc 2571 + 128 * fieldXor (mc 2572) (mc 1 + mc 2 + mc 4 + mc 6 + mc 8 + mc 9 + mc 12 + mc 13 + mc 14 + mc 17 + mc 20 + mc 21) + 256 * mc 2573 + 512 * mc 2574 + 1024 * mc 2575 + 2048 * mc 2576 + 4096 * mc 2577 + 8192 * mc 2578 + 16384 * mc 2579 + 32768 * fieldXor (mc 2580) (mc 1 + mc 2 + mc 3 + mc 4 + mc 6 + mc 7 + mc 10 + mc 12 + mc 14 + mc 15 + mc 16 + mc 18 + mc 20 + mc 21 + mc 23) := by
  simp only [KeccakfPermAir.extraction.constraint_3078, KeccakfPermAir.extraction.inter_6916, fieldXor, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6915 c row = (mc 2566 + (mc 1 + mc 2 + mc 4 + mc 8 + mc 11 + mc 12 + mc 13 + mc 15 + mc 16 + mc 18 + mc 19) - 2*(mc 2566)*(mc 1 + mc 2 + mc 4 + mc 8 + mc 11 + mc 12 + mc 13 + mc 15 + mc 16 + mc 18 + mc 19)) + 2 * KeccakfPermAir.extraction.inter_6913 c row := by
    simp only [KeccakfPermAir.extraction.inter_6915, KeccakfPermAir.extraction.inter_6905, KeccakfPermAir.extraction.inter_6914, fieldXor, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6913 c row = mc 2567 + 2 * KeccakfPermAir.extraction.inter_6912 c row := by
    simp only [KeccakfPermAir.extraction.inter_6913, fieldXor, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6912 c row = (mc 2568 + (mc 2 + mc 4 + mc 7 + mc 8 + mc 9 + mc 10 + mc 11 + mc 12 + mc 13 + mc 14 + mc 18 + mc 19 + mc 23) - 2*(mc 2568)*(mc 2 + mc 4 + mc 7 + mc 8 + mc 9 + mc 10 + mc 11 + mc 12 + mc 13 + mc 14 + mc 18 + mc 19 + mc 23)) + 2 * KeccakfPermAir.extraction.inter_6910 c row := by
    simp only [KeccakfPermAir.extraction.inter_6912, KeccakfPermAir.extraction.inter_6911, fieldXor, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6910 c row = mc 2569 + 2 * KeccakfPermAir.extraction.inter_6909 c row := by
    simp only [KeccakfPermAir.extraction.inter_6910, fieldXor, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6909 c row = mc 2570 + 2 * KeccakfPermAir.extraction.inter_6908 c row := by
    simp only [KeccakfPermAir.extraction.inter_6909, fieldXor, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6908 c row = mc 2571 + 2 * KeccakfPermAir.extraction.inter_6907 c row := by
    simp only [KeccakfPermAir.extraction.inter_6908, fieldXor, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6907 c row = (mc 2572 + (mc 1 + mc 2 + mc 4 + mc 6 + mc 8 + mc 9 + mc 12 + mc 13 + mc 14 + mc 17 + mc 20 + mc 21) - 2*(mc 2572)*(mc 1 + mc 2 + mc 4 + mc 6 + mc 8 + mc 9 + mc 12 + mc 13 + mc 14 + mc 17 + mc 20 + mc 21)) + 2 * KeccakfPermAir.extraction.inter_6904 c row := by
    simp only [KeccakfPermAir.extraction.inter_6907, KeccakfPermAir.extraction.inter_6905, KeccakfPermAir.extraction.inter_6906, fieldXor, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6904 c row = mc 2573 + 2 * KeccakfPermAir.extraction.inter_6903 c row := by
    simp only [KeccakfPermAir.extraction.inter_6904, fieldXor, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6903 c row = mc 2574 + 2 * KeccakfPermAir.extraction.inter_6902 c row := by
    simp only [KeccakfPermAir.extraction.inter_6903, fieldXor, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6902 c row = mc 2575 + 2 * KeccakfPermAir.extraction.inter_6901 c row := by
    simp only [KeccakfPermAir.extraction.inter_6902, fieldXor, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6901 c row = mc 2576 + 2 * KeccakfPermAir.extraction.inter_6900 c row := by
    simp only [KeccakfPermAir.extraction.inter_6901, fieldXor, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6900 c row = mc 2577 + 2 * KeccakfPermAir.extraction.inter_6899 c row := by
    simp only [KeccakfPermAir.extraction.inter_6900, fieldXor, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6899 c row = mc 2578 + 2 * KeccakfPermAir.extraction.inter_6898 c row := by
    simp only [KeccakfPermAir.extraction.inter_6899, fieldXor, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6898 c row = mc 2579 + 2 * KeccakfPermAir.extraction.inter_6897 c row := by
    simp only [KeccakfPermAir.extraction.inter_6898, fieldXor, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6897 c row = (mc 2580 + (mc 1 + mc 2 + mc 3 + mc 4 + mc 6 + mc 7 + mc 10 + mc 12 + mc 14 + mc 15 + mc 16 + mc 18 + mc 20 + mc 21 + mc 23) - 2*(mc 2580)*(mc 1 + mc 2 + mc 3 + mc 4 + mc 6 + mc 7 + mc 10 + mc 12 + mc 14 + mc 15 + mc 16 + mc 18 + mc 20 + mc 21 + mc 23)) := by
    simp only [KeccakfPermAir.extraction.inter_6897, KeccakfPermAir.extraction.inter_6896, fieldXor, hmc]; ring
  simp only [fieldXor]
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_iota_3079 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3079 c row) :
    mc 2630 = mc 2581 + 2 * mc 2582 + 4 * mc 2583 + 8 * mc 2584 + 16 * mc 2585 + 32 * mc 2586 + 64 * mc 2587 + 128 * mc 2588 + 256 * mc 2589 + 512 * mc 2590 + 1024 * mc 2591 + 2048 * mc 2592 + 4096 * mc 2593 + 8192 * mc 2594 + 16384 * mc 2595 + 32768 * fieldXor (mc 2596) (mc 3 + mc 5 + mc 6 + mc 10 + mc 11 + mc 12 + mc 19 + mc 20 + mc 22 + mc 23) := by
  simp only [KeccakfPermAir.extraction.constraint_3079, fieldXor, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6932 c row = mc 2582 + 2 * KeccakfPermAir.extraction.inter_6931 c row := by
    simp only [KeccakfPermAir.extraction.inter_6932, fieldXor, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6931 c row = mc 2583 + 2 * KeccakfPermAir.extraction.inter_6930 c row := by
    simp only [KeccakfPermAir.extraction.inter_6931, fieldXor, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6930 c row = mc 2584 + 2 * KeccakfPermAir.extraction.inter_6929 c row := by
    simp only [KeccakfPermAir.extraction.inter_6930, fieldXor, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6929 c row = mc 2585 + 2 * KeccakfPermAir.extraction.inter_6928 c row := by
    simp only [KeccakfPermAir.extraction.inter_6929, fieldXor, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6928 c row = mc 2586 + 2 * KeccakfPermAir.extraction.inter_6927 c row := by
    simp only [KeccakfPermAir.extraction.inter_6928, fieldXor, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6927 c row = mc 2587 + 2 * KeccakfPermAir.extraction.inter_6926 c row := by
    simp only [KeccakfPermAir.extraction.inter_6927, fieldXor, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6926 c row = mc 2588 + 2 * KeccakfPermAir.extraction.inter_6925 c row := by
    simp only [KeccakfPermAir.extraction.inter_6926, fieldXor, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6925 c row = mc 2589 + 2 * KeccakfPermAir.extraction.inter_6924 c row := by
    simp only [KeccakfPermAir.extraction.inter_6925, fieldXor, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6924 c row = mc 2590 + 2 * KeccakfPermAir.extraction.inter_6923 c row := by
    simp only [KeccakfPermAir.extraction.inter_6924, fieldXor, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6923 c row = mc 2591 + 2 * KeccakfPermAir.extraction.inter_6922 c row := by
    simp only [KeccakfPermAir.extraction.inter_6923, fieldXor, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6922 c row = mc 2592 + 2 * KeccakfPermAir.extraction.inter_6921 c row := by
    simp only [KeccakfPermAir.extraction.inter_6922, fieldXor, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6921 c row = mc 2593 + 2 * KeccakfPermAir.extraction.inter_6920 c row := by
    simp only [KeccakfPermAir.extraction.inter_6921, fieldXor, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6920 c row = mc 2594 + 2 * KeccakfPermAir.extraction.inter_6919 c row := by
    simp only [KeccakfPermAir.extraction.inter_6920, fieldXor, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6919 c row = mc 2595 + 2 * KeccakfPermAir.extraction.inter_6918 c row := by
    simp only [KeccakfPermAir.extraction.inter_6919, fieldXor, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6918 c row = (mc 2596 + (mc 3 + mc 5 + mc 6 + mc 10 + mc 11 + mc 12 + mc 19 + mc 20 + mc 22 + mc 23) - 2*(mc 2596)*(mc 3 + mc 5 + mc 6 + mc 10 + mc 11 + mc 12 + mc 19 + mc 20 + mc 22 + mc 23)) := by
    simp only [KeccakfPermAir.extraction.inter_6918, KeccakfPermAir.extraction.inter_6917, fieldXor, hmc]; ring
  simp only [fieldXor]
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15

private theorem peel_iota_3081 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3081 c row) :
    mc 2632 = mc 2613 + 2 * mc 2614 + 4 * mc 2615 + 8 * mc 2616 + 16 * mc 2617 + 32 * mc 2618 + 64 * mc 2619 + 128 * mc 2620 + 256 * mc 2621 + 512 * mc 2622 + 1024 * mc 2623 + 2048 * mc 2624 + 4096 * mc 2625 + 8192 * mc 2626 + 16384 * mc 2627 + 32768 * fieldXor (mc 2628) (mc 2 + mc 3 + mc 6 + mc 7 + mc 13 + mc 14 + mc 15 + mc 16 + mc 17 + mc 19 + mc 20 + mc 21 + mc 23) := by
  simp only [KeccakfPermAir.extraction.constraint_3081, fieldXor, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6962 c row = mc 2614 + 2 * KeccakfPermAir.extraction.inter_6961 c row := by
    simp only [KeccakfPermAir.extraction.inter_6962, fieldXor, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6961 c row = mc 2615 + 2 * KeccakfPermAir.extraction.inter_6960 c row := by
    simp only [KeccakfPermAir.extraction.inter_6961, fieldXor, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6960 c row = mc 2616 + 2 * KeccakfPermAir.extraction.inter_6959 c row := by
    simp only [KeccakfPermAir.extraction.inter_6960, fieldXor, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6959 c row = mc 2617 + 2 * KeccakfPermAir.extraction.inter_6958 c row := by
    simp only [KeccakfPermAir.extraction.inter_6959, fieldXor, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6958 c row = mc 2618 + 2 * KeccakfPermAir.extraction.inter_6957 c row := by
    simp only [KeccakfPermAir.extraction.inter_6958, fieldXor, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6957 c row = mc 2619 + 2 * KeccakfPermAir.extraction.inter_6956 c row := by
    simp only [KeccakfPermAir.extraction.inter_6957, fieldXor, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6956 c row = mc 2620 + 2 * KeccakfPermAir.extraction.inter_6955 c row := by
    simp only [KeccakfPermAir.extraction.inter_6956, fieldXor, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6955 c row = mc 2621 + 2 * KeccakfPermAir.extraction.inter_6954 c row := by
    simp only [KeccakfPermAir.extraction.inter_6955, fieldXor, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6954 c row = mc 2622 + 2 * KeccakfPermAir.extraction.inter_6953 c row := by
    simp only [KeccakfPermAir.extraction.inter_6954, fieldXor, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6953 c row = mc 2623 + 2 * KeccakfPermAir.extraction.inter_6952 c row := by
    simp only [KeccakfPermAir.extraction.inter_6953, fieldXor, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6952 c row = mc 2624 + 2 * KeccakfPermAir.extraction.inter_6951 c row := by
    simp only [KeccakfPermAir.extraction.inter_6952, fieldXor, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6951 c row = mc 2625 + 2 * KeccakfPermAir.extraction.inter_6950 c row := by
    simp only [KeccakfPermAir.extraction.inter_6951, fieldXor, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6950 c row = mc 2626 + 2 * KeccakfPermAir.extraction.inter_6949 c row := by
    simp only [KeccakfPermAir.extraction.inter_6950, fieldXor, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6949 c row = mc 2627 + 2 * KeccakfPermAir.extraction.inter_6948 c row := by
    simp only [KeccakfPermAir.extraction.inter_6949, fieldXor, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6948 c row = (mc 2628 + (mc 2 + mc 3 + mc 6 + mc 7 + mc 13 + mc 14 + mc 15 + mc 16 + mc 17 + mc 19 + mc 20 + mc 21 + mc 23) - 2*(mc 2628)*(mc 2 + mc 3 + mc 6 + mc 7 + mc 13 + mc 14 + mc 15 + mc 16 + mc 17 + mc 19 + mc 20 + mc 21 + mc 23)) := by
    simp only [KeccakfPermAir.extraction.inter_6948, KeccakfPermAir.extraction.inter_6947, fieldXor, hmc]; ring
  simp only [fieldXor]
  linear_combination -hx + (2 : F) * e1 + (4 : F) * e2 + (8 : F) * e3 + (16 : F) * e4 + (32 : F) * e5 + (64 : F) * e6 + (128 : F) * e7 + (256 : F) * e8 + (512 : F) * e9 + (1024 : F) * e10 + (2048 : F) * e11 + (4096 : F) * e12 + (8192 : F) * e13 + (16384 : F) * e14 + (32768 : F) * e15



/-! ## ι spec helpers -/

-- `ι` only modifies lane [0][0], so `(ι st r h)[0] = st[0] ^^^ rc[r]`.
theorem ι_getElem_zero (st : State) (r : Nat) (h : r < roundConstants.size) :
    (ι st r h)[0]'(by omega) = st[0]'(by omega) ^^^ roundConstants[r]'h := by
  simp [ι, subtypeModify, Id.run]; simp [Array.getElem_modify]

-- For nonzero lanes, ι leaves them unchanged.
theorem ι_getElem_nonzero (st : State) (r : Nat) (h : r < roundConstants.size)
    (i : Nat) (hi : i < 25) (hi0 : i ≠ 0) :
    (ι st r h)[i]'hi = st[i]'hi := by
  simp [ι, subtypeModify, Id.run]; simp [Array.getElem_modify, hi0]; rfl

/-! ## Round constant bit as FBB -/

def rcBitFBB (round : Fin 24) (n : Nat) : FBB :=
  if (roundConstants[round.val]'(by simpa [roundConstants] using round.isLt)).toBitVec.getLsbD n
  then 1 else 0

theorem rcBitFBB_is_bool (round : Fin 24) (n : Nat) :
    rcBitFBB round n = 0 ∨ rcBitFBB round n = 1 := by
  unfold rcBitFBB; split <;> simp

theorem fbbToBool_rcBitFBB (round : Fin 24) (n : Nat) :
    fbbToBool (rcBitFBB round n) =
    (roundConstants[round.val]'(by simpa [roundConstants] using round.isLt)).toBitVec.getLsbD n := by
  unfold rcBitFBB; split <;> simp_all [fbbToBool]

/-! ## Pre-iota bit extraction -/

-- Bit j of fieldToU16(a_prime_prime[L]) = fbbToBool(a_pp_00_bit[16L+j]).
-- From constraints 3074–3077.
private theorem preiota_bit
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_round : RoundLocalConstraints air row) (L : Fin 4) (j : Nat) (hj : j < 16) :
    (fieldToU16 (a_prime_prime air L.val row)).toUInt64.toBitVec.getLsbD j =
    fbbToBool (a_pp_00_bit air (16 * L.val + j) row) := by
  have hrecomp := h_round.iota_preiota_recompose L.val L.isLt
  have hval := recompose16_eq_value hrecomp
  dsimp only at hval
  exact fieldToU16_getLsbD_fbbToBool
    (fun i => a_pp_00_bit air (16 * L.val + i.val) row)
    (fun i => a_pp_00_bit_is_bool h_round _ (by omega))
    _ hval j hj

/-! ## Constraint value extraction -/

-- constraint_3078: a_ppp_00_limb[0] with 5 XOR bits (RC bits 0,1,3,7,15).
set_option maxHeartbeats 800000 in
private theorem constraint_3078_value
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : constraint_3078 air row) :
    a_ppp_00_limb air 0 row =
    fieldXor (a_pp_00_bit air 0 row)
      (step_flag air 0 row + step_flag air 4 row + step_flag air 5 row +
       step_flag air 6 row + step_flag air 7 row + step_flag air 10 row +
       step_flag air 12 row + step_flag air 13 row + step_flag air 14 row +
       step_flag air 15 row + step_flag air 20 row + step_flag air 22 row) +
    2 * fieldXor (a_pp_00_bit air 1 row)
      (step_flag air 1 row + step_flag air 2 row + step_flag air 4 row +
       step_flag air 8 row + step_flag air 11 row + step_flag air 12 row +
       step_flag air 13 row + step_flag air 15 row + step_flag air 16 row +
       step_flag air 18 row + step_flag air 19 row) +
    4 * a_pp_00_bit air 2 row +
    8 * fieldXor (a_pp_00_bit air 3 row)
      (step_flag air 2 row + step_flag air 4 row + step_flag air 7 row +
       step_flag air 8 row + step_flag air 9 row + step_flag air 10 row +
       step_flag air 11 row + step_flag air 12 row + step_flag air 13 row +
       step_flag air 14 row + step_flag air 18 row + step_flag air 19 row +
       step_flag air 23 row) +
    16 * a_pp_00_bit air 4 row + 32 * a_pp_00_bit air 5 row +
    64 * a_pp_00_bit air 6 row +
    128 * fieldXor (a_pp_00_bit air 7 row)
      (step_flag air 1 row + step_flag air 2 row + step_flag air 4 row +
       step_flag air 6 row + step_flag air 8 row + step_flag air 9 row +
       step_flag air 12 row + step_flag air 13 row + step_flag air 14 row +
       step_flag air 17 row + step_flag air 20 row + step_flag air 21 row) +
    256 * a_pp_00_bit air 8 row + 512 * a_pp_00_bit air 9 row +
    1024 * a_pp_00_bit air 10 row + 2048 * a_pp_00_bit air 11 row +
    4096 * a_pp_00_bit air 12 row + 8192 * a_pp_00_bit air 13 row +
    16384 * a_pp_00_bit air 14 row +
    32768 * fieldXor (a_pp_00_bit air 15 row)
      (step_flag air 1 row + step_flag air 2 row + step_flag air 3 row +
       step_flag air 4 row + step_flag air 6 row + step_flag air 7 row +
       step_flag air 10 row + step_flag air 12 row + step_flag air 14 row +
       step_flag air 15 row + step_flag air 16 row + step_flag air 18 row +
       step_flag air 20 row + step_flag air 21 row + step_flag air 23 row) := by
  -- The extraction gives `h` as the Horner-form iota constraint; `peel_iota_3078`
  -- telescopes it into the explicit `fieldXor` recomposition.  Unfold the output/
  -- bit/flag column abbreviations to raw `Circuit.main`, then discharge by
  -- definitional equality against the peeling lemma.
  dsimp only [a_ppp_00_limb, a_pp_00_bit, step_flag]
  exact peel_iota_3078 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h

-- constraint_3079: a_ppp_00_limb[1] with 1 XOR bit (RC bit 31).
set_option maxHeartbeats 400000 in
private theorem constraint_3079_value
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : constraint_3079 air row) :
    a_ppp_00_limb air 1 row =
    a_pp_00_bit air 16 row + 2 * a_pp_00_bit air 17 row +
    4 * a_pp_00_bit air 18 row + 8 * a_pp_00_bit air 19 row +
    16 * a_pp_00_bit air 20 row + 32 * a_pp_00_bit air 21 row +
    64 * a_pp_00_bit air 22 row + 128 * a_pp_00_bit air 23 row +
    256 * a_pp_00_bit air 24 row + 512 * a_pp_00_bit air 25 row +
    1024 * a_pp_00_bit air 26 row + 2048 * a_pp_00_bit air 27 row +
    4096 * a_pp_00_bit air 28 row + 8192 * a_pp_00_bit air 29 row +
    16384 * a_pp_00_bit air 30 row +
    32768 * fieldXor (a_pp_00_bit air 31 row)
      (step_flag air 3 row + step_flag air 5 row + step_flag air 6 row +
       step_flag air 10 row + step_flag air 11 row + step_flag air 12 row +
       step_flag air 19 row + step_flag air 20 row + step_flag air 22 row +
       step_flag air 23 row) := by
  -- The extraction gives `h` as the Horner-form iota constraint; `peel_iota_3079`
  -- telescopes it into the explicit `fieldXor` recomposition.  Unfold the output/
  -- bit/flag column abbreviations to raw `Circuit.main`, then discharge by
  -- definitional equality against the peeling lemma.
  dsimp only [a_ppp_00_limb, a_pp_00_bit, step_flag]
  exact peel_iota_3079 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h

-- constraint_3081: a_ppp_00_limb[3] with 1 XOR bit (RC bit 63).
set_option maxHeartbeats 400000 in
private theorem constraint_3081_value
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : constraint_3081 air row) :
    a_ppp_00_limb air 3 row =
    a_pp_00_bit air 48 row + 2 * a_pp_00_bit air 49 row +
    4 * a_pp_00_bit air 50 row + 8 * a_pp_00_bit air 51 row +
    16 * a_pp_00_bit air 52 row + 32 * a_pp_00_bit air 53 row +
    64 * a_pp_00_bit air 54 row + 128 * a_pp_00_bit air 55 row +
    256 * a_pp_00_bit air 56 row + 512 * a_pp_00_bit air 57 row +
    1024 * a_pp_00_bit air 58 row + 2048 * a_pp_00_bit air 59 row +
    4096 * a_pp_00_bit air 60 row + 8192 * a_pp_00_bit air 61 row +
    16384 * a_pp_00_bit air 62 row +
    32768 * fieldXor (a_pp_00_bit air 63 row)
      (step_flag air 2 row + step_flag air 3 row + step_flag air 6 row +
       step_flag air 7 row + step_flag air 13 row + step_flag air 14 row +
       step_flag air 15 row + step_flag air 16 row + step_flag air 17 row +
       step_flag air 19 row + step_flag air 20 row + step_flag air 21 row +
       step_flag air 23 row) := by
  -- The extraction gives `h` as the Horner-form iota constraint; `peel_iota_3081`
  -- telescopes it into the explicit `fieldXor` recomposition.  Unfold the output/
  -- bit/flag column abbreviations to raw `Circuit.main`, then discharge by
  -- definitional equality against the peeling lemma.
  dsimp only [a_ppp_00_limb, a_pp_00_bit, step_flag]
  exact peel_iota_3081 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h

/-! ## Flag sum collapse under h_step

Each flag sum in the iota constraints corresponds to a specific RC
bit position.  Under h_step, the sum of specific step_flag values
collapses to rcBitFBB.

Proved by fin_cases on round : Fin 24.  For each concrete round value,
all step_flags simplify to 0 or 1, and rcBitFBB evaluates to a
concrete value. -/

-- Generic flag sum collapse: sum of step_flags at specific indices.
-- We inline the proof for each RC bit position needed by the constraints.
-- After fin_cases, simp_all handles the concrete arithmetic.
set_option maxHeartbeats 6400000 in
private theorem flag_sum_0
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ} {round : Fin 24}
    (h1 : step_flag air round.val row = 1)
    (h0 : ∀ j, j < 24 → j ≠ round.val → step_flag air j row = 0) :
    step_flag air 0 row + step_flag air 4 row + step_flag air 5 row +
    step_flag air 6 row + step_flag air 7 row + step_flag air 10 row +
    step_flag air 12 row + step_flag air 13 row + step_flag air 14 row +
    step_flag air 15 row + step_flag air 20 row + step_flag air 22 row =
    rcBitFBB round 0 := by
  fin_cases round <;> simp_all [rcBitFBB, roundConstants, step_flag]

set_option maxHeartbeats 6400000 in
private theorem flag_sum_1
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ} {round : Fin 24}
    (h1 : step_flag air round.val row = 1)
    (h0 : ∀ j, j < 24 → j ≠ round.val → step_flag air j row = 0) :
    step_flag air 1 row + step_flag air 2 row + step_flag air 4 row +
    step_flag air 8 row + step_flag air 11 row + step_flag air 12 row +
    step_flag air 13 row + step_flag air 15 row + step_flag air 16 row +
    step_flag air 18 row + step_flag air 19 row =
    rcBitFBB round 1 := by
  fin_cases round <;> simp_all [rcBitFBB, roundConstants, step_flag]

set_option maxHeartbeats 6400000 in
private theorem flag_sum_3
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ} {round : Fin 24}
    (h1 : step_flag air round.val row = 1)
    (h0 : ∀ j, j < 24 → j ≠ round.val → step_flag air j row = 0) :
    step_flag air 2 row + step_flag air 4 row + step_flag air 7 row +
    step_flag air 8 row + step_flag air 9 row + step_flag air 10 row +
    step_flag air 11 row + step_flag air 12 row + step_flag air 13 row +
    step_flag air 14 row + step_flag air 18 row + step_flag air 19 row +
    step_flag air 23 row =
    rcBitFBB round 3 := by
  fin_cases round <;> simp_all [rcBitFBB, roundConstants, step_flag]

set_option maxHeartbeats 6400000 in
private theorem flag_sum_7
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ} {round : Fin 24}
    (h1 : step_flag air round.val row = 1)
    (h0 : ∀ j, j < 24 → j ≠ round.val → step_flag air j row = 0) :
    step_flag air 1 row + step_flag air 2 row + step_flag air 4 row +
    step_flag air 6 row + step_flag air 8 row + step_flag air 9 row +
    step_flag air 12 row + step_flag air 13 row + step_flag air 14 row +
    step_flag air 17 row + step_flag air 20 row + step_flag air 21 row =
    rcBitFBB round 7 := by
  fin_cases round <;> simp_all [rcBitFBB, roundConstants, step_flag]

set_option maxHeartbeats 6400000 in
private theorem flag_sum_15
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ} {round : Fin 24}
    (h1 : step_flag air round.val row = 1)
    (h0 : ∀ j, j < 24 → j ≠ round.val → step_flag air j row = 0) :
    step_flag air 1 row + step_flag air 2 row + step_flag air 3 row +
    step_flag air 4 row + step_flag air 6 row + step_flag air 7 row +
    step_flag air 10 row + step_flag air 12 row + step_flag air 14 row +
    step_flag air 15 row + step_flag air 16 row + step_flag air 18 row +
    step_flag air 20 row + step_flag air 21 row + step_flag air 23 row =
    rcBitFBB round 15 := by
  fin_cases round <;> simp_all [rcBitFBB, roundConstants, step_flag]

set_option maxHeartbeats 6400000 in
private theorem flag_sum_31
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ} {round : Fin 24}
    (h1 : step_flag air round.val row = 1)
    (h0 : ∀ j, j < 24 → j ≠ round.val → step_flag air j row = 0) :
    step_flag air 3 row + step_flag air 5 row + step_flag air 6 row +
    step_flag air 10 row + step_flag air 11 row + step_flag air 12 row +
    step_flag air 19 row + step_flag air 20 row + step_flag air 22 row +
    step_flag air 23 row =
    rcBitFBB round 31 := by
  fin_cases round <;> simp_all [rcBitFBB, roundConstants, step_flag]

set_option maxHeartbeats 6400000 in
private theorem flag_sum_63
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ} {round : Fin 24}
    (h1 : step_flag air round.val row = 1)
    (h0 : ∀ j, j < 24 → j ≠ round.val → step_flag air j row = 0) :
    step_flag air 2 row + step_flag air 3 row + step_flag air 6 row +
    step_flag air 7 row + step_flag air 13 row + step_flag air 14 row +
    step_flag air 15 row + step_flag air 16 row + step_flag air 17 row +
    step_flag air 19 row + step_flag air 20 row + step_flag air 21 row +
    step_flag air 23 row =
    rcBitFBB round 63 := by
  fin_cases round <;> simp_all [rcBitFBB, roundConstants, step_flag]

/-! ## RC bit zero helpers

For "plain" bit positions (where no round constant has that bit set),
roundConstants[r].bit(n) = false.  These are proved by decide
over the finite domain Fin 24 × Fin 16. -/

-- Bits 32–47 of all round constants are 0.
private theorem rc_bits_32_47 :
    ∀ (r : Fin 24) (j : Fin 16),
    (roundConstants[r.val]'(by simpa [roundConstants] using r.isLt)).toBitVec.getLsbD (32 + j.val) = false := by
  decide

-- For limb 0: the "plain" bit positions (j ∈ {2,4,5,6,8,9,10,11,12,13,14}) have RC bit = 0.
-- We don't need a single helper; the per-bit case in the main proof handles this
-- via decide on the specific (round, bit) pair.

-- Bits 16–30 of all round constants are 0 (limb 1 plain bits).
private theorem rc_bits_16_30 :
    ∀ (r : Fin 24) (j : Fin 16), j.val < 15 →
    (roundConstants[r.val]'(by simpa [roundConstants] using r.isLt)).toBitVec.getLsbD (16 + j.val) = false := by
  decide

-- Bits 48–62 of all round constants are 0 (limb 3 plain bits).
private theorem rc_bits_48_62 :
    ∀ (r : Fin 24) (j : Fin 16), j.val < 15 →
    (roundConstants[r.val]'(by simpa [roundConstants] using r.isLt)).toBitVec.getLsbD (48 + j.val) = false := by
  decide

-- fieldXor a 0 = a (may already exist; restate locally if needed)
private theorem fieldXor_zero_right' {F : Type} [Field F] (a : F) : fieldXor a 0 = a := by
  unfold fieldXor; ring

/-! ## Main theorem: iota lane [0][0] -/

-- The main exported theorem.
set_option maxHeartbeats 6400000 in
theorem iota_lane_zero
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ} {round : Fin 24}
    (h_round : RoundLocalConstraints air row)
    (h_step :
      step_flag air round.val row = 1 ∧
      ∀ j, j < 24 → j ≠ round.val →
        step_flag air j row = 0) :
    (rowOutputState air row)[0]'(by omega) =
    (ι (χ (ρπ (θ (rowInputState air row)))) round.val
      (by simpa [roundConstants] using round.isLt))[0]'(by omega) := by
  -- Unfold LHS to laneOfLimbs form
  rw [rowOutputState_lane_zero]
  -- Unfold RHS: ι spec + chi pre-iota lane
  rw [ι_getElem_zero]
  rw [← chi_preiota_lane_zero h_round]
  rw [chiOutputState_lane air row ⟨0, by omega⟩]
  -- Goal: laneOfLimbs(a_ppp_00_limb) = laneOfLimbs(a_prime_prime[0..3]) ^^^ rc
  -- Normalize arithmetic in indices (4*0 → 0, 4*0+k → k)
  show laneOfLimbs (a_ppp_00_limb air 0 row) (a_ppp_00_limb air 1 row)
      (a_ppp_00_limb air 2 row) (a_ppp_00_limb air 3 row) =
    laneOfLimbs (a_prime_prime air 0 row) (a_prime_prime air 1 row)
      (a_prime_prime air 2 row) (a_prime_prime air 3 row) ^^^
      roundConstants[round.val]'(by simpa [roundConstants] using round.isLt)
  -- Prove bit-by-bit
  apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro k hk
  -- Convert LHS to getBit form
  rw [show (laneOfLimbs _ _ _ _).toBitVec.getLsbD k =
      getBit (laneOfLimbs _ _ _ _) ⟨k, hk⟩ from rfl]
  rw [getBit_laneOfLimbs]
  -- Decompose RHS XOR
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  rw [show (laneOfLimbs _ _ _ _).toBitVec.getLsbD k =
      getBit (laneOfLimbs _ _ _ _) ⟨k, hk⟩ from rfl]
  rw [getBit_laneOfLimbs]
  -- Now both sides are 4-way if-then-else on the limb.
  -- Prove the per-limb-and-bit identity.
  obtain ⟨h1, h0⟩ := h_step
  -- Suffices: for each limb L and bit j within it, the bits match.
  suffices hLimb : ∀ (L : Nat) (hL : L < 4) (j : Nat) (hj : j < 16),
      (fieldToU16 (a_ppp_00_limb air L row)).toUInt64.toBitVec.getLsbD j =
      ((fieldToU16 (a_prime_prime air L row)).toUInt64.toBitVec.getLsbD j ^^
       (roundConstants[round.val]'(by simpa [roundConstants] using round.isLt)).toBitVec.getLsbD (16 * L + j)) by
    -- Dispatch the 4-way if to the right limb
    by_cases h16 : k < 16
    · simp only [h16, ite_true, show k < 32 from by omega, show k < 48 from by omega]
      rw [u16_toBitVec_eq_toU64_toBitVec _ k h16, u16_toBitVec_eq_toU64_toBitVec _ k h16]
      have := hLimb 0 (by omega) k h16
      simp only [show 16 * 0 + k = k from by omega] at this; exact this
    · by_cases h32 : k < 32
      · simp only [h16, ite_false, h32, ite_true, show k < 48 from by omega]
        rw [u16_toBitVec_eq_toU64_toBitVec _ (k-16) (by omega),
            u16_toBitVec_eq_toU64_toBitVec _ (k-16) (by omega)]
        have := hLimb 1 (by omega) (k-16) (by omega)
        simp only [show 16 * 1 + (k - 16) = k from by omega] at this; exact this
      · by_cases h48 : k < 48
        · simp only [h16, ite_false, h32, h48, ite_true]
          rw [u16_toBitVec_eq_toU64_toBitVec _ (k-32) (by omega),
              u16_toBitVec_eq_toU64_toBitVec _ (k-32) (by omega)]
          have := hLimb 2 (by omega) (k-32) (by omega)
          simp only [show 16 * 2 + (k - 32) = k from by omega] at this; exact this
        · simp only [h16, ite_false, h32, h48]
          rw [u16_toBitVec_eq_toU64_toBitVec _ (k-48) (by omega),
              u16_toBitVec_eq_toU64_toBitVec _ (k-48) (by omega)]
          have := hLimb 3 (by omega) (k-48) (by omega)
          simp only [show 16 * 3 + (k - 48) = k from by omega] at this; exact this
  -- Prove hLimb for each limb L and bit j.
  -- For each limb, use the iota constraint value form + fieldToU16_getLsbD_fbbToBool
  -- for LHS, and preiota_bit for RHS.
  intro L hL j hj
  -- Extract LHS bit using the iota constraint for limb L
  -- and RHS bit using the pre-iota constraint
  rw [preiota_bit h_round ⟨L, hL⟩ j hj]
  -- Goal: iota_output_bit = fbbToBool(a_pp_00_bit[16L+j]) ^^ rc_bit(16L+j)
  -- Case split on limb L
  interval_cases L
  -- Limb 0: constraint 3078, 5 XOR bits at positions 0,1,3,7,15.
  -- All 16 bits are fieldXor(a_pp_00_bit[j], rcBitFBB round j), since for
  -- plain bit positions rcBitFBB = 0 and fieldXor(a, 0) = a.
  · have hval0 := constraint_3078_value h_round.iota_output_3078
    rw [flag_sum_0 h1 h0, flag_sum_1 h1 h0, flag_sum_3 h1 h0,
        flag_sum_7 h1 h0, flag_sum_15 h1 h0] at hval0
    -- Uniform b: every bit is fieldXor(a_pp_00_bit, rcBitFBB).
    let b : Fin 16 → FBB := fun i =>
      fieldXor (a_pp_00_bit air i.val row) (rcBitFBB round i.val)
    have hbool : ∀ i : Fin 16, b i = 0 ∨ b i = 1 := fun i =>
      fieldXor_bool (a_pp_00_bit_is_bool h_round i.val (by omega)) (rcBitFBB_is_bool round i.val)
    -- heq: convert constraint value form to all-fieldXor form.
    -- For plain bits (2,4-6,8-14), a_pp_00_bit j = fieldXor(a_pp_00_bit j, 0)
    -- = fieldXor(a_pp_00_bit j, rcBitFBB round j) since rcBitFBB = 0.
    have heq : a_ppp_00_limb air 0 row = b ⟨0, by omega⟩ + 2 * b ⟨1, by omega⟩ +
        4 * b ⟨2, by omega⟩ + 8 * b ⟨3, by omega⟩ + 16 * b ⟨4, by omega⟩ +
        32 * b ⟨5, by omega⟩ + 64 * b ⟨6, by omega⟩ + 128 * b ⟨7, by omega⟩ +
        256 * b ⟨8, by omega⟩ + 512 * b ⟨9, by omega⟩ + 1024 * b ⟨10, by omega⟩ +
        2048 * b ⟨11, by omega⟩ + 4096 * b ⟨12, by omega⟩ + 8192 * b ⟨13, by omega⟩ +
        16384 * b ⟨14, by omega⟩ + 32768 * b ⟨15, by omega⟩ := by
      -- For plain bits, rcBitFBB = 0 so fieldXor(a, 0) = a.
      -- We convert each plain term in hval0 by rewriting with fieldXor_zero_right'.
      simp only [b]
      -- rcBitFBB round j = 0 for plain bits j ∈ {2,4,5,6,8,9,10,11,12,13,14}
      -- rcBitFBB round n = 0 for plain bit positions (proved by fin_cases on round)
      have hrc : ∀ n, n ∈ [2, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14] → rcBitFBB round n = 0 := by
        intro n hn
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (simp only [rcBitFBB]; fin_cases round <;> decide)
      rw [hrc 2 (by simp), hrc 4 (by simp), hrc 5 (by simp), hrc 6 (by simp),
          hrc 8 (by simp), hrc 9 (by simp), hrc 10 (by simp), hrc 11 (by simp),
          hrc 12 (by simp), hrc 13 (by simp), hrc 14 (by simp)]
      simp only [fieldXor_zero_right']
      exact hval0
    rw [fieldToU16_getLsbD_fbbToBool b hbool _ heq j hj]
    -- Goal: fbbToBool(b ⟨j, hj⟩) = fbbToBool(a_pp_00_bit[j]) ^^ rc_bit(j)
    simp only [b, show 16 * 0 + j = j from by omega]
    rw [fbbToBool_fieldXor (a_pp_00_bit_is_bool h_round _ (by omega)) (rcBitFBB_is_bool round _)]
    rw [fbbToBool_rcBitFBB]
  -- Limb 1: constraint 3079, 1 XOR bit at position 31 (bit 15 of limb 1)
  · have hval := constraint_3079_value h_round.iota_output_3079
    rw [flag_sum_31 h1 h0] at hval
    -- Define the b function for fieldToU16_getLsbD_fbbToBool
    -- For j < 15: b(j) = a_pp_00_bit(16+j)
    -- For j = 15: b(15) = fieldXor(a_pp_00_bit(31), rcBitFBB round 31)
    let b : Fin 16 → FBB := fun i =>
      if i.val < 15 then a_pp_00_bit air (16 + i.val) row
      else fieldXor (a_pp_00_bit air 31 row) (rcBitFBB round 31)
    have hbool : ∀ i : Fin 16, b i = 0 ∨ b i = 1 := by
      intro i; simp only [b]
      split
      · exact a_pp_00_bit_is_bool h_round _ (by omega)
      · exact fieldXor_bool (a_pp_00_bit_is_bool h_round 31 (by omega)) (rcBitFBB_is_bool round 31)
    have heq : a_ppp_00_limb air 1 row = b ⟨0, by omega⟩ + 2 * b ⟨1, by omega⟩ +
        4 * b ⟨2, by omega⟩ + 8 * b ⟨3, by omega⟩ + 16 * b ⟨4, by omega⟩ +
        32 * b ⟨5, by omega⟩ + 64 * b ⟨6, by omega⟩ + 128 * b ⟨7, by omega⟩ +
        256 * b ⟨8, by omega⟩ + 512 * b ⟨9, by omega⟩ + 1024 * b ⟨10, by omega⟩ +
        2048 * b ⟨11, by omega⟩ + 4096 * b ⟨12, by omega⟩ + 8192 * b ⟨13, by omega⟩ +
        16384 * b ⟨14, by omega⟩ + 32768 * b ⟨15, by omega⟩ := by
      simp only [b, show (0 : Nat) < 15 from by omega, show (1 : Nat) < 15 from by omega,
        show (2 : Nat) < 15 from by omega, show (3 : Nat) < 15 from by omega,
        show (4 : Nat) < 15 from by omega, show (5 : Nat) < 15 from by omega,
        show (6 : Nat) < 15 from by omega, show (7 : Nat) < 15 from by omega,
        show (8 : Nat) < 15 from by omega, show (9 : Nat) < 15 from by omega,
        show (10 : Nat) < 15 from by omega, show (11 : Nat) < 15 from by omega,
        show (12 : Nat) < 15 from by omega, show (13 : Nat) < 15 from by omega,
        show (14 : Nat) < 15 from by omega, show ¬(15 : Nat) < 15 from by omega,
        ite_true, ite_false]
      exact hval
    rw [fieldToU16_getLsbD_fbbToBool b hbool _ heq j hj]
    -- Goal: fbbToBool(b ⟨j, hj⟩) = fbbToBool(a_pp_00_bit[16+j]) ^^ rc_bit(16+j)
    simp only [b]
    by_cases hjlt : j < 15
    · -- Plain bit: b(j) = a_pp_00_bit(16+j), RC bit = false
      simp only [hjlt, ite_true, show 16 * 1 + j = 16 + j from by omega]
      rw [show (roundConstants[round.val]'(by simpa [roundConstants] using round.isLt)).toBitVec.getLsbD (16 + j) = false
        from rc_bits_16_30 round ⟨j, hj⟩ hjlt]
      simp [Bool.bne_false]
    · -- XOR bit (j = 15): b(15) = fieldXor(a_pp_00_bit(31), rcBitFBB round 31)
      have hj15 : j = 15 := by omega
      subst hj15
      simp only [show ¬(15 : Nat) < 15 from by omega, ite_false,
                  show 16 * 1 + 15 = 31 from by omega]
      rw [fbbToBool_fieldXor (a_pp_00_bit_is_bool h_round 31 (by omega)) (rcBitFBB_is_bool round 31)]
      rw [fbbToBool_rcBitFBB]
  -- Limb 2: constraint 3080, plain recompose (no XOR)
  · -- Extract bit from constraint 3080 (same structure as pre-iota)
    have hval := recompose16_eq_value h_round.iota_output_3080
    dsimp only at hval
    rw [fieldToU16_getLsbD_fbbToBool
      (fun i => a_pp_00_bit air (32 + i.val) row)
      (fun i => a_pp_00_bit_is_bool h_round _ (by omega))
      _ hval j hj]
    simp only [show 16 * 2 + j = 32 + j from by omega]
    rw [show (roundConstants[round.val]'(by simpa [roundConstants] using round.isLt)).toBitVec.getLsbD (32 + j) = false
      from rc_bits_32_47 round ⟨j, hj⟩]
    simp [Bool.bne_false]
  -- Limb 3: constraint 3081, 1 XOR bit at position 63 (bit 15 of limb 3)
  · have hval := constraint_3081_value h_round.iota_output_3081
    rw [flag_sum_63 h1 h0] at hval
    let b : Fin 16 → FBB := fun i =>
      if i.val < 15 then a_pp_00_bit air (48 + i.val) row
      else fieldXor (a_pp_00_bit air 63 row) (rcBitFBB round 63)
    have hbool : ∀ i : Fin 16, b i = 0 ∨ b i = 1 := by
      intro i; simp only [b]
      split
      · exact a_pp_00_bit_is_bool h_round _ (by omega)
      · exact fieldXor_bool (a_pp_00_bit_is_bool h_round 63 (by omega)) (rcBitFBB_is_bool round 63)
    have heq : a_ppp_00_limb air 3 row = b ⟨0, by omega⟩ + 2 * b ⟨1, by omega⟩ +
        4 * b ⟨2, by omega⟩ + 8 * b ⟨3, by omega⟩ + 16 * b ⟨4, by omega⟩ +
        32 * b ⟨5, by omega⟩ + 64 * b ⟨6, by omega⟩ + 128 * b ⟨7, by omega⟩ +
        256 * b ⟨8, by omega⟩ + 512 * b ⟨9, by omega⟩ + 1024 * b ⟨10, by omega⟩ +
        2048 * b ⟨11, by omega⟩ + 4096 * b ⟨12, by omega⟩ + 8192 * b ⟨13, by omega⟩ +
        16384 * b ⟨14, by omega⟩ + 32768 * b ⟨15, by omega⟩ := by
      simp only [b, show (0 : Nat) < 15 from by omega, show (1 : Nat) < 15 from by omega,
        show (2 : Nat) < 15 from by omega, show (3 : Nat) < 15 from by omega,
        show (4 : Nat) < 15 from by omega, show (5 : Nat) < 15 from by omega,
        show (6 : Nat) < 15 from by omega, show (7 : Nat) < 15 from by omega,
        show (8 : Nat) < 15 from by omega, show (9 : Nat) < 15 from by omega,
        show (10 : Nat) < 15 from by omega, show (11 : Nat) < 15 from by omega,
        show (12 : Nat) < 15 from by omega, show (13 : Nat) < 15 from by omega,
        show (14 : Nat) < 15 from by omega, show ¬(15 : Nat) < 15 from by omega,
        ite_true, ite_false]
      exact hval
    rw [fieldToU16_getLsbD_fbbToBool b hbool _ heq j hj]
    simp only [b]
    by_cases hjlt : j < 15
    · simp only [hjlt, ite_true, show 16 * 3 + j = 48 + j from by omega]
      rw [show (roundConstants[round.val]'(by simpa [roundConstants] using round.isLt)).toBitVec.getLsbD (48 + j) = false
        from rc_bits_48_62 round ⟨j, hj⟩ hjlt]
      simp [Bool.bne_false]
    · have hj15 : j = 15 := by omega
      subst hj15
      simp only [show ¬(15 : Nat) < 15 from by omega, ite_false,
                  show 16 * 3 + 15 = 63 from by omega]
      rw [fbbToBool_fieldXor (a_pp_00_bit_is_bool h_round 63 (by omega)) (rcBitFBB_is_bool round 63)]
      rw [fbbToBool_rcBitFBB]

end KeccakfPermAir.Soundness
