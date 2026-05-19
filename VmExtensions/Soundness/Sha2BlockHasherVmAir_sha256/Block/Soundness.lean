/-
Final assembly for SHA-256 block soundness.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Block.Support
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.BitsFacts

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints
open Sha2BlockHasherVmAir_sha256.Soundness.BusFacts

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

theorem sha2_block_soundness
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
    blockCompressionSpec air start := by
  have hci := constrain_interactions_of_extraction air hc.constrain_interactions
  have hwindow := blockWindowSupported_of_start_le air start hstart hsel hrot hc
  have hshape := blockWindowHasShape_of_constraints air start hwindow hsel hrot hc
  have hcarry : roundCarryRangeOnBlock air start := by
    intro offset hoffset
    intro slot limb hslot hlimb
    have hrow := block_round_rows air start offset hoffset hwindow hrot hc hsel
    have h_wf_row := bitwise_lookup_send_properties_of_bus_wf air (start + offset)
      (by unfold blockWindowSupported at hwindow; omega) hci h_bus_wf
    exact carry_range_of_bus air (start + offset) slot limb hslot hlimb hrow.2.1 h_wf_row
  have huniq_send :=
    uniqueDigestSenderByNextGlobalBlockIdx_of_constraints air htrace_fit hrot hc
  have hdig := digest_matches_spec air start hwindow hrot hshape hc
    h_raw_perm huniq_send htrace_fit hcarry h_bus_wf
  unfold blockCompressionSpec
  exact ⟨hshape, hdig.1, hdig.2⟩

/-- Proof-friendly block-side boundary for SHA-256 opcode
packaging. It exposes exactly the local window, schedule, and compression facts
needed by the opcode layer, so callers no longer have to restate the raw block
soundness assumptions directly. -/
def blockCompressionBoundarySpec (air : C FBB ExtF) (start : ℕ) : Prop :=
  blockWindowSupported air start ∧
  rotation_consistent air ∧
  scheduleBitsBooleanOnBlock air start ∧
  blockCompressionSpec air start

theorem blockCompressionBoundarySpec_of_soundness_assumptions
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
    blockCompressionBoundarySpec air start := by
  have hwindow := blockWindowSupported_of_start_le air start hstart hsel hrot hc
  have hsched_bits := scheduleBitsBooleanOnBlock_of_start air start hstart hsel hrot hc
  have hblock :=
    sha2_block_soundness air start hstart hsel hrot hc h_raw_perm htrace_fit h_bus_wf
  exact ⟨hwindow, hrot, hsched_bits, hblock⟩

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
