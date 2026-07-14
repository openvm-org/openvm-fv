/-
  Comparator SOLUTION module.

  Real proof(s) for the frozen statement(s) in `Challenge.lean`. Each theorem
  here must have the SAME name and SAME statement as its `Challenge.lean`
  counterpart; its proof delegates to the actual VmExtensions theorem. The
  comparator kernel-checks that this proof establishes the Challenge statement
  using only the permitted axioms — no `sorry`, no `native_decide`.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Block.Soundness

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
