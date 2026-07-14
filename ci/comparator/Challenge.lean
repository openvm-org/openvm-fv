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
import VmExtensions.Soundness.Keccakf.Main

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

section Keccakf

open KeccakfOpAir
open KeccakfOpAir.constraints
open KeccakfOpAir.Views
open KeccakfOpAir.Soundness
open KeccakfOpAir.WFC
open KeccakfPermAir
open KeccakfOp.Spec
open Keccakf.Interface
open Keccakf.Soundness
open Consistency
open BabyBear

variable {ExtF : Type} [Field ExtF]

namespace ComparatorGate

/-- Frozen statement of `Keccakf.Soundness.keccakf_matches_spec`. -/
theorem keccakf_matches_spec
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_opAllHold : ∀ row (h_row : row ≤ opAir.last_row),
      allHold_simplified opAir row h_row)
    (h_opAxioms : ∀ row, row ≤ opAir.last_row →
      axiomsPerRow opAir row)
    (h_opWfAssume : ∀ row, row ≤ opAir.last_row →
      wf_propertiesToAssumePerRow opAir row)
    (h_permAllHold : ∀ row, row ≤ permAir.last_row →
      KeccakfPermAir.constraints.allHold_simplified permAir row)
    (h_bus7_balanced : InteractionList.is_balanced (combinedBus7Trace opAir permAir))
    (h_bus7_length : (combinedBus7Trace opAir permAir).length < BB_prime)
    {chips : List (WFChip μ)} {lb rb : List FBB}
    (h_opAir_chip : wfc_opAir h_opAllHold h_opAxioms h_opWfAssume ∈ chips)
    (h_bus_length : 2 * (execution_bus chips).length +
                    2 * (memory_bus chips).length + 2 < BB_prime)
    (h_exec_balanced : InteractionList.is_balanced
      ([((1 : FBB), lb)] ++
       InteractionList.rising_bus μ (execution_bus chips)
         (execution_bus_is_rising_bus chips) ++
       [((-1 : FBB), rb)])) :
    ∀ row, row ≤ opAir.last_row →
      wf_propertiesToAssertPerRow opAir row ∧
      (RowDisabledAndInert opAir row ∨
        (is_valid opAir row = 1 ∧ RowMatchesPureSpec opAir row)) := sorry

end ComparatorGate

end Keccakf
