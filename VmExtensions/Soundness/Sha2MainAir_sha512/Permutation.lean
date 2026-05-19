import VmExtensions.Soundness.Sha2MainAir_sha512.PermutationMultiplicity

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace Sha2CompressionBridge_sha512

open BabyBear
open Sha2MainAir_sha512.Soundness
open Sha2BlockHasherVmAir_sha512.BlockSpec

section SharedBridge

open Sha2BlockHasherVmAir_sha512.constraints

variable {CMain CBlock : Type → Type → Type} {ExtF : Type}
  [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]

private theorem exists_start_msg1_alignment_of_rawPermutationSemantics
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row : ℕ)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (h_enabled : Sha2MainAir_sha512.constraints.is_enabled mainAir row = 1)
    (hmain_rot : rotation_consistent mainAir)
    (hmain_trace_fit : traceLengthFitsField mainAir)
    (hrow : row ≤ Circuit.last_row mainAir)
    (hc : blockHasherConstraints blockAir)
    (h_raw_perm : sharedWrapperRawPermutationSemantics mainAir blockAir) :
    ∃ start,
      start ≤ Circuit.last_row blockAir ∧
      encoder_selector_idx blockAir start = 0 ∧
      Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir start =
        Sha2MainAir_sha512.constraints.request_id mainAir row ∧
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).toRaw.2 =
        (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir row).toRaw.2 := by
  let data := (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir row).toRaw.2
  have hmain_mult :
      InteractionList.get_multiplicity
        (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data = 1 := by
    simpa [data] using
      mainMsg1_trace_getMultiplicity_eq_one
        mainAir row hmainc hmain_rot hmain_trace_fit hrow h_enabled
  have hblock_mult :
      InteractionList.get_multiplicity
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data = -1 := by
    have hsum :
        InteractionList.get_multiplicity
          (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data +
        InteractionList.get_multiplicity
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data = 0 := by
      simpa [sharedWrapperTraceEntries, InteractionList.get_multiplicity_append, data] using
        h_raw_perm data
    have hsum' :
        1 +
          InteractionList.get_multiplicity
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data = 0 := by
      simpa [hmain_mult] using hsum
    have htmp :
        1 +
          InteractionList.get_multiplicity
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data =
          1 + (-1 : FBB) := by
      simpa using hsum'
    exact add_left_cancel htmp
  have hexists :
      ∃ start,
        start ≤ Circuit.last_row blockAir ∧
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).multiplicity = -1 ∧
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).toRaw.2 = data := by
    by_contra hno
    have hkind : List.head? data = some 1 := by
      simpa [data] using mainWrapperMsg1_raw_head mainAir row
    have hzero :
        InteractionList.get_multiplicity
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data = 0 := by
      apply blockMsg1_trace_getMultiplicity_zero_of_no_active_match blockAir hc data hkind
      intro r hr_valid hEq hactive
      exact hno ⟨r, hr_valid, hactive, hEq⟩
    rw [hblock_mult] at hzero
    exact (by decide : (-1 : FBB) ≠ 0) hzero
  rcases hexists with ⟨start, hstart, hactive, hraw⟩
  have hf_start : flag_constraints blockAir start := (hc start).1
  have hsel_start : encoder_selector_idx blockAir start = 0 :=
    blockWrapperMsg1_active_implies_selector_zero blockAir start hf_start hactive
  have hreq_opt :
      some (Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir start) =
        some (Sha2MainAir_sha512.constraints.request_id mainAir row) := by
    simpa [data, blockWrapperMsg1_raw_request, mainWrapperMsg1_raw_request] using
      congrArg (fun payload => List.head? (List.tail payload)) hraw
  exact ⟨start, hstart, hsel_start, Option.some.inj hreq_opt, by simpa [data] using hraw⟩

private theorem main_state_raw_of_start_request_id_of_rawPermutation
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (h_enabled : Sha2MainAir_sha512.constraints.is_enabled mainAir row = 1)
    (hmain_rot : rotation_consistent mainAir)
    (hmain_trace_fit : traceLengthFitsField mainAir)
    (hrow : row ≤ Circuit.last_row mainAir)
    (hrot : rotation_consistent blockAir)
    (hc : blockHasherConstraints blockAir)
    (h_raw_perm : sharedWrapperRawPermutationSemantics mainAir blockAir)
    (htrace_fit : traceLengthFitsField blockAir)
    (hstart : start ≤ Circuit.last_row blockAir)
    (hsel : encoder_selector_idx blockAir start = 0)
    (hreq_start :
      Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir start =
        Sha2MainAir_sha512.constraints.request_id mainAir row) :
    (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir row).toRaw.2 =
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).toRaw.2 := by
  have hreq : blockRequestIdStableOnWindow blockAir start :=
    blockRequestIdStableOnWindow_of_constraints blockAir start hstart hsel hrot hc
  let data := (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).toRaw.2
  have hblock_nonzero :
      InteractionList.get_multiplicity
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data ≠ 0 := by
    simpa [data] using
      blockState_trace_getMultiplicity_ne_zero_of_start blockAir start hstart hsel hrot hc htrace_fit
  have hmain_nonzero :
      InteractionList.get_multiplicity
        (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data ≠ 0 := by
    intro hmain0
    have hsum :
        InteractionList.get_multiplicity
          (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data +
        InteractionList.get_multiplicity
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data = 0 := by
      simpa [sharedWrapperTraceEntries, InteractionList.get_multiplicity_append, data] using
        h_raw_perm data
    have hblock0 :
        InteractionList.get_multiplicity
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data = 0 := by
      simpa [hmain0] using hsum
    exact hblock_nonzero hblock0
  have hexists :
      ∃ row',
        row' ≤ Circuit.last_row mainAir ∧
        Sha2MainAir_sha512.constraints.is_enabled mainAir row' = 1 ∧
        (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir row').toRaw.2 = data := by
    by_contra hno
    have hkind : List.head? data = some 0 := by
      simpa [data] using blockWrapperState_raw_head blockAir (start + 20)
    have hmain0 :
        InteractionList.get_multiplicity
          (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data = 0 := by
      apply mainState_trace_getMultiplicity_zero_of_no_sender mainAir hmainc data hkind
      intro r hr_valid hr_enabled
      by_contra hEq
      exact hno ⟨r, hr_valid, hr_enabled, hEq⟩
    exact hmain_nonzero hmain0
  rcases hexists with ⟨row', _, h_enabled_row', hstate_raw'⟩
  have hreq_opt :
      some (Sha2MainAir_sha512.constraints.request_id mainAir row') =
        some (Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir (start + 20)) := by
    simpa [data, mainWrapperState_raw_request, blockWrapperState_raw_request] using
      congrArg (fun payload => List.head? (List.tail payload)) hstate_raw'
  have hreq_row'_20 :
      Sha2MainAir_sha512.constraints.request_id mainAir row' =
        Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir (start + 20) :=
    Option.some.inj hreq_opt
  have hreq_20_start :
      Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir (start + 20) =
        Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir start :=
    block_request_id_eq_start blockAir start 20 (by omega) hstart hsel hrot hc
  have hreq_row'_start :
      Sha2MainAir_sha512.constraints.request_id mainAir row' =
        Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir start :=
    hreq_row'_20.trans hreq_20_start
  have hreq_row'_row :
      Sha2MainAir_sha512.constraints.request_id mainAir row' =
        Sha2MainAir_sha512.constraints.request_id mainAir row :=
    hreq_row'_start.trans hreq_start
  have hrow_eq : row' = row :=
    mainTraceConstraints.enabled_request_id_injective hmainc
      hmain_rot hmain_trace_fit row' row (by omega) hrow h_enabled_row' h_enabled hreq_row'_row
  calc
    (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir row).toRaw.2 =
        (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir row').toRaw.2 := by
          simpa [hrow_eq]
    _ = data := hstate_raw'
    _ = (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).toRaw.2 := rfl

private theorem main_msg2_raw_of_start_request_id_of_rawPermutation
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (h_enabled : Sha2MainAir_sha512.constraints.is_enabled mainAir row = 1)
    (hmain_rot : rotation_consistent mainAir)
    (hmain_trace_fit : traceLengthFitsField mainAir)
    (hrow : row ≤ Circuit.last_row mainAir)
    (hrot : rotation_consistent blockAir)
    (hc : blockHasherConstraints blockAir)
    (h_raw_perm : sharedWrapperRawPermutationSemantics mainAir blockAir)
    (htrace_fit : traceLengthFitsField blockAir)
    (hstart : start ≤ Circuit.last_row blockAir)
    (hsel : encoder_selector_idx blockAir start = 0)
    (hreq_start :
      Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir start =
        Sha2MainAir_sha512.constraints.request_id mainAir row) :
    (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir row).toRaw.2 =
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).toRaw.2 := by
  have hreq : blockRequestIdStableOnWindow blockAir start :=
    blockRequestIdStableOnWindow_of_constraints blockAir start hstart hsel hrot hc
  let data := (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).toRaw.2
  have hblock_nonzero :
      InteractionList.get_multiplicity
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data ≠ 0 := by
    simpa [data] using
      blockMsg2_trace_getMultiplicity_ne_zero_of_start blockAir start hstart hsel hrot hc htrace_fit
  have hmain_nonzero :
      InteractionList.get_multiplicity
        (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data ≠ 0 := by
    intro hmain0
    have hsum :
        InteractionList.get_multiplicity
          (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data +
        InteractionList.get_multiplicity
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data = 0 := by
      simpa [sharedWrapperTraceEntries, InteractionList.get_multiplicity_append, data] using
        h_raw_perm data
    have hblock0 :
        InteractionList.get_multiplicity
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperBus_trace blockAir) data = 0 := by
      simpa [hmain0] using hsum
    exact hblock_nonzero hblock0
  have hexists :
      ∃ row',
        row' ≤ Circuit.last_row mainAir ∧
        Sha2MainAir_sha512.constraints.is_enabled mainAir row' = 1 ∧
        (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir row').toRaw.2 = data := by
    by_contra hno
    have hkind : List.head? data = some 2 := by
      simpa [data] using blockWrapperMsg2_raw_head blockAir (start + 2)
    have hmain0 :
        InteractionList.get_multiplicity
          (Sha2MainAir_sha512.constraints.wrapperBus_trace mainAir) data = 0 := by
      apply mainMsg2_trace_getMultiplicity_zero_of_no_sender mainAir hmainc data hkind
      intro r hr_valid hr_enabled
      by_contra hEq
      exact hno ⟨r, hr_valid, hr_enabled, hEq⟩
    exact hmain_nonzero hmain0
  rcases hexists with ⟨row', _, h_enabled_row', hmsg2_raw'⟩
  have hreq_opt :
      some (Sha2MainAir_sha512.constraints.request_id mainAir row') =
        some (Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir (start + 2)) := by
    simpa [data, mainWrapperMsg2_raw_request, blockWrapperMsg2_raw_request] using
      congrArg (fun payload => List.head? (List.tail payload)) hmsg2_raw'
  have hreq_row'_2 :
      Sha2MainAir_sha512.constraints.request_id mainAir row' =
        Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir (start + 2) :=
    Option.some.inj hreq_opt
  have hreq_2_start :
      Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir (start + 2) =
        Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir start :=
    block_request_id_eq_start blockAir start 2 (by omega) hstart hsel hrot hc
  have hreq_row'_start :
      Sha2MainAir_sha512.constraints.request_id mainAir row' =
        Sha2BlockHasherVmAir_sha512.constraints.request_id blockAir start :=
    hreq_row'_2.trans hreq_2_start
  have hreq_row'_row :
      Sha2MainAir_sha512.constraints.request_id mainAir row' =
        Sha2MainAir_sha512.constraints.request_id mainAir row :=
    hreq_row'_start.trans hreq_start
  have hrow_eq : row' = row :=
    mainTraceConstraints.enabled_request_id_injective hmainc
      hmain_rot hmain_trace_fit row' row (by omega) hrow h_enabled_row' h_enabled hreq_row'_row
  calc
    (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir row).toRaw.2 =
        (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir row').toRaw.2 := by
          simpa [hrow_eq]
    _ = data := hmsg2_raw'
    _ = (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).toRaw.2 := rfl

theorem exists_start_of_sharedWrapperRawPermutationSemantics
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row : ℕ)
    (hmainc : Sha2MainAir_sha512.Soundness.mainTraceConstraints mainAir)
    (h_enabled : Sha2MainAir_sha512.constraints.is_enabled mainAir row = 1)
    (hmain_rot : rotation_consistent mainAir)
    (hmain_trace_fit : traceLengthFitsField mainAir)
    (hrow : row ≤ Circuit.last_row mainAir)
    (hrot : rotation_consistent blockAir)
    (hc : blockHasherConstraints blockAir)
    (h_raw_perm : sharedWrapperRawPermutationSemantics mainAir blockAir)
    (htrace_fit : traceLengthFitsField blockAir) :
    ∃ start,
      start ≤ Circuit.last_row blockAir ∧
      encoder_selector_idx blockAir start = 0 ∧
      sharedWrapperPayloadSpec mainAir blockAir row start := by
  rcases exists_start_msg1_alignment_of_rawPermutationSemantics
      mainAir blockAir row hmainc h_enabled hmain_rot hmain_trace_fit hrow hc h_raw_perm with
    ⟨start, hstart, hsel, hreq_start, hmsg1_raw⟩
  have hstate_raw :=
    main_state_raw_of_start_request_id_of_rawPermutation
      mainAir blockAir row start hmainc h_enabled hmain_rot hmain_trace_fit hrow hrot hc
      h_raw_perm htrace_fit hstart hsel hreq_start
  have hmsg2_raw :=
    main_msg2_raw_of_start_request_id_of_rawPermutation
      mainAir blockAir row start hmainc h_enabled hmain_rot hmain_trace_fit hrow hrot hc
      h_raw_perm htrace_fit hstart hsel hreq_start
  refine ⟨start, hstart, hsel, ?_⟩
  exact sharedWrapperPayloadSpec_of_raw_payload_eqs
    mainAir blockAir row start hstate_raw hmsg1_raw.symm hmsg2_raw

end SharedBridge

end Sha2CompressionBridge_sha512
