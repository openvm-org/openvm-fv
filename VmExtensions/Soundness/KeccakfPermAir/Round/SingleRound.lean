/-
  Single-round correctness assembly for KeccakfPermAir.

  This file is a thin assembly over previously proved round-step theorems:
  • `chi_nonzero_lanes` from ChiFacts — all 24 nonzero output lanes
  • `iota_lane_zero` from IotaFacts — lane [0][0] after ι

  The proof is a lane case split (i = 0 vs i ≠ 0) plus state extensionality.
  Theta, chi, and iota algebra is supplied by imported round lemmas.
-/
import VmExtensions.Soundness.KeccakfPermAir.Round.Surface
import VmExtensions.Soundness.KeccakfPermAir.Round.IotaFacts

set_option autoImplicit false
set_option linter.all false

namespace KeccakfPermAir.Soundness

open BabyBear
open KeccakfPermAir.constraints
open Keccak

-- Proof strategy:
-- 1. Use `state_ext` to reduce to per-lane equality.
-- 2. For lane 0: apply `iota_lane_zero` (which combines chi pre-iota + iota update).
-- 3. For lanes 1–24: apply `chi_nonzero_lanes` (chi output = χ(ρπ(θ(input)))),
--    then `ι_getElem_nonzero` to show ι leaves nonzero lanes unchanged.
theorem single_round_correctness
    {ExtF : Type} [Field ExtF]
    {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ} {round : Fin 24}
    (h_round : RoundLocalConstraints air row)
    (h_step :
      KeccakfPermAir.constraints.step_flag air round.val row = 1 ∧
      ∀ j, j < 24 → j ≠ round.val →
        KeccakfPermAir.constraints.step_flag air j row = 0) :
    rowOutputState air row =
      ι (χ (ρπ (θ (rowInputState air row))))
        round.val
        (by simpa [roundConstants] using round.isLt) := by
  apply state_ext
  intro i
  by_cases hi : i.val = 0
  · -- Lane [0][0]: from iota_lane_zero
    have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hi0]
    exact iota_lane_zero h_round h_step
  · -- Nonzero lanes: chi output, unchanged by ι
    rw [chi_nonzero_lanes h_round i hi]
    rw [ι_getElem_nonzero _ _ _ i.val (by omega) hi]

end KeccakfPermAir.Soundness
