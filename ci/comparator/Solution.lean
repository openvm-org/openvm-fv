/-
  Comparator SOLUTION module.

  Real proof(s) for the frozen statement(s) in `Challenge.lean`. Each theorem
  here must have the SAME name and SAME statement as its `Challenge.lean`
  counterpart; its proof delegates to the actual VmExtensions theorem. The
  comparator kernel-checks that this proof establishes the Challenge statement
  using only the permitted axioms — no `sorry`, no `native_decide`.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Block.Soundness
import VmExtensions.Soundness.Keccakf.Main

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints
open Sha2BlockHasherVmAir_sha256.BlockSpec

namespace ComparatorGate

/-- Proof of the frozen `sha2_block_soundness` statement, delegating to the
    upstream VmExtensions theorem. -/
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
    blockCompressionSpec air start :=
  Sha2BlockHasherVmAir_sha256.BlockSpec.sha2_block_soundness
    air start hstart hsel hrot hc h_raw_perm htrace_fit h_bus_wf

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

/-- Proof of the frozen `keccakf_matches_spec` statement, delegating to the
    upstream VmExtensions theorem. -/
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
        (is_valid opAir row = 1 ∧ RowMatchesPureSpec opAir row)) :=
  Keccakf.Soundness.keccakf_matches_spec
    opAir permAir h_opAllHold h_opAxioms h_opWfAssume h_permAllHold
    h_bus7_balanced h_bus7_length h_opAir_chip h_bus_length h_exec_balanced

end ComparatorGate

end Keccakf
