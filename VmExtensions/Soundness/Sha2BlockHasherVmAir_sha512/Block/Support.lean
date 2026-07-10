/- 
Block-level soundness support.

This module collects the helper theorems used by the final theorem in
`VmExtensions/Soundness/Sha2BlockHasherVmAir_sha512/Block/Soundness.lean`.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Bus.Facts
import VmExtensions.Constraints.Sha2BlockHasherSubAirBus_sha512
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Block.Window
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.TraceFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.MessageSchedule.Correctness
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.RoundStep.RowChain
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Block.Digest
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Bus.PrivateChaining

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints
open Sha2BlockHasherVmAir_sha512.Soundness.BusFacts

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

theorem compression_output (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (hcarry : roundCarryRangeOnBlock air start) :
    let initialState := blockStartState air start
    let messageWords := blockInputWords air start
    let schedule := expandSchedule messageWords
    carriedState air (start + 19) = (compressionTrace initialState schedule)[80]! := by
  have hrow : blockStateRow air start 20 = start + 19 := by
    simpa using blockStateRow_succ air start 19
  simpa [hrow] using
    compression_trace_final air start hwindow hrot hshape hc hcarry

theorem digest_matches_spec (air : C FBB ExtF) (start : ℕ)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (huniq_send : uniqueDigestSenderByNextGlobalBlockIdx air)
    (htrace_fit : traceLengthFitsField air)
    (hcarry : roundCarryRangeOnBlock air start)
    (h_bus_wf : ∀ mult a b c op,
      (mult, [a, b, c, op]) ∈ Circuit.buses air Sha2BitwiseBus →
      mult = 1 → a.val < 256 ∧ b.val < 256) :
    let initialState := blockStartState air start
    let messageWords := blockInputWords air start
    let schedule := expandSchedule messageWords
    let finalState := (compressionTrace initialState schedule)[80]!
    digestPrevHashState air (start + 20) = initialState ∧
    digestFinalHashState air (start + 20) = initialState.add finalState := by
  dsimp
  have h_wf_prev :=
    Sha2BlockHasherVmAir_sha512.constraints.bitwise_lookup_send_properties_of_bus_wf
      air (start + 19)
    (by unfold blockWindowSupported at hwindow; omega)
    (constrain_interactions_of_extraction air hc.constrain_interactions) h_bus_wf
  rcases digest_row_correct air start hwindow hrot hshape hc
      h_raw_perm huniq_send htrace_fit h_wf_prev with
    ⟨hprev, hfinal⟩
  refine ⟨hprev, ?_⟩
  simpa [compression_output air start hwindow hrot hshape hc hcarry] using hfinal

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
