/-
  Comparator CHALLENGE module.

  Frozen statement(s) of the top-level VmExtensions soundness theorem(s) the
  comparator gate certifies. Each theorem here is stated with `sorry`; the
  comparator checks that the identically-named theorem in `Solution.lean` proves
  the SAME statement using only the axioms in `config.json`'s `permitted_axioms`.

  Keep each signature character-for-character in sync with the corresponding
  theorem in the VmExtensions source (and with `Solution.lean`). If the upstream
  statement changes, the comparator's statement-equality check will fail until
  this file is updated — that is the intended tripwire.

  This module deliberately lives OUTSIDE the VmExtensions source tree so its
  `sorry` is not flagged by `scripts/check_hygiene.py`.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Block.Soundness

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints
open Sha2BlockHasherVmAir_sha256.BlockSpec

namespace ComparatorGate

/-- Frozen statement of `Sha2BlockHasherVmAir_sha256.BlockSpec.sha2_block_soundness`. -/
theorem sha2_block_soundness
    {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]
    (air : C FBB ExtF) (start : ℕ)
    (hstart : start ≤ Circuit.last_row air)
    (hsel : encoder_selector_idx air start = 0)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (htrace_fit : traceLengthFitsField air)
    (h_bus_wf : ∀ mult a b c op,
      (mult, [a, b, c, op]) ∈ Circuit.buses air BitwiseBus →
      mult = 1 → a.val < 256 ∧ b.val < 256) :
    blockCompressionSpec air start := sorry

end ComparatorGate
