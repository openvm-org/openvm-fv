/-
  Private-bus chaining reduction.

  Derives `privateBusChainingSupported` from:
  1. `privateBusRawPermutationSemantics` (bus is balanced),
  2. sender-key uniqueness (`uniqueDigestSenderByNextGlobalBlockIdx`).
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.SpecFacts
import VmExtensions.Constraints.Sha2BlockHasherSubAirBus_sha512
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Block.Window
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.TraceFacts

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints
open Sha2BlockHasherVmAir_sha512.BlockSpec

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## Abstract obligations -/

/-- Row-level consequence of the private-bus permutation check:
    every enabled digest-row receive payload is equal to the send payload of some
    enabled digest row.

    This does not say which digest row supplied the message, only that some
    digest row did. -/
def privateBusReceiveCovered (air : C FBB ExtF) : Prop :=
  ∀ recvRow,
    recvRow ≤ Circuit.last_row air →
    is_digest_row air recvRow = 1 →
    ∃ sendRow,
      sendRow ≤ Circuit.last_row air ∧
      is_digest_row air sendRow = 1 ∧
      privateBus_send_data air sendRow = privateBus_recv_data air recvRow

/-- The in-trace chaining theorem actually needed by the SHA2 block proof.

    This only speaks about supported digest rows, which matches the scope of
    the private-bus permutation semantics. -/
def privateBusChainingSupported (air : C FBB ExtF) : Prop :=
  ∀ r1 r2,
    r1 ≤ Circuit.last_row air →
    r2 ≤ Circuit.last_row air →
    is_digest_row air r1 = 1 →
    is_digest_row air r2 = 1 →
    private_bus_next_gbi air r1 = global_block_idx air r2 →
    privateBus_send_data air r1 = privateBus_recv_data air r2


/-- Uniqueness of digest rows by the send-side key.

    This is the exact uniqueness fact needed to identify the sender row once we
    know the key `private_bus_next_gbi`. -/
def uniqueDigestSenderByNextGlobalBlockIdx (air : C FBB ExtF) : Prop :=
  ∀ r1 r2,
    r1 ≤ Circuit.last_row air →
    r2 ≤ Circuit.last_row air →
    is_digest_row air r1 = 1 →
    is_digest_row air r2 = 1 →
    private_bus_next_gbi air r1 = private_bus_next_gbi air r2 →
    r1 = r2

/-- All private-bus entries contributed by the trace rows of the SHA2 subair. -/
noncomputable def privateBusTraceEntries (air : C FBB ExtF) : List (FBB × List FBB) :=
  privateBus_trace air

/-- The private-bus entries selected by the extraction agree with `privateBus_trace`. -/
lemma privateBusTraceEntries_of_extraction
    (air : C FBB ExtF)
    (h : Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_interactions air) :
    Circuit.buses air Sha2PrivateBus = privateBusTraceEntries air := by
  simpa [privateBusTraceEntries] using privateBus_trace_of_extraction air h

/-- Raw private-bus semantic fact: the flattened trace bus is balanced globally. -/
def privateBusRawPermutationSemantics (air : C FBB ExtF) : Prop :=
  InteractionList.is_balanced (privateBusTraceEntries air)

/-- Drop zero-multiplicity digest rows before applying the generic unitary-bus
    permutation theorem. -/
noncomputable def privateBusEnabledEntries (air : C FBB ExtF) : List (FBB × List FBB) :=
  InteractionList.non_zero (privateBusTraceEntries air)

/-- Receive payloads of the enabled private-bus entries. -/
noncomputable def privateBusEnabledReceives (air : C FBB ExtF) : List (List FBB) :=
  List.filterMap (fun x ↦ if x.1 = -1 then some x.2 else none) (privateBusEnabledEntries air)

/-- Send payloads of the enabled private-bus entries. -/
noncomputable def privateBusEnabledSends (air : C FBB ExtF) : List (List FBB) :=
  List.filterMap (fun x ↦ if x.1 = 1 then some x.2 else none) (privateBusEnabledEntries air)

/-- Size bound needed to apply the generic permutation theorem after zero
    multiplicities are removed. -/
def privateBusEnabledEntriesFitField (air : C FBB ExtF) : Prop :=
  (privateBusEnabledEntries air).length < BB_prime

/-! ## Generic list helpers for the interaction-level bridge -/

private theorem mem_filterMap_of_mem_some
    {α β : Type}
    (f : α → Option β)
    {l : List α} {a : α} {b : β}
    (ha : a ∈ l)
    (hf : f a = some b) :
    b ∈ l.filterMap f := by
  simpa using (List.mem_filterMap.2 ⟨a, ha, hf⟩)

private theorem exists_mem_eq_some_of_mem_filterMap
    {α β : Type}
    (f : α → Option β)
    {l : List α} {b : β}
    (hb : b ∈ l.filterMap f) :
    ∃ a ∈ l, f a = some b := by
  simpa using (List.mem_filterMap.1 hb)

private theorem mem_privateBusTraceEntries_iff
    (air : C FBB ExtF)
    (entry : FBB × List FBB) :
    entry ∈ privateBusTraceEntries air ↔
      ∃ row, row ≤ Circuit.last_row air ∧ entry ∈ privateBus_row air row := by
  constructor
  · intro hentry
    rw [privateBusTraceEntries, privateBus_trace] at hentry
    rcases List.mem_flatMap.mp hentry with ⟨row, hrow_mem, hentry_row⟩
    exact ⟨row, Nat.lt_succ_iff.mp (List.mem_range.mp hrow_mem), hentry_row⟩
  · rintro ⟨row, hvalid, hentry_row⟩
    rw [privateBusTraceEntries, privateBus_trace]
    exact List.mem_flatMap.mpr ⟨row, List.mem_range.mpr (Nat.lt_succ_of_le hvalid), hentry_row⟩

/-! ## Derived sender-key uniqueness from the row constraints -/

private theorem digest_row_send_key_one_implies_next_padding
    (air : C FBB ExtF) (row : ℕ)
    (htrace_fit : traceLengthFitsField air)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hdigest : is_digest_row air row = 1)
    (hkey : private_bus_next_gbi air row = 1) :
    next_padding_flag air row = 1 := by
  have hrow_lt : row < Circuit.last_row air := digest_row_lt_last_row air row hc hrow hdigest
  have ht : trace_shape_constraints air row :=
    trace_shape_constraints_of_blockHasherConstraints air hc row
  have hnext_digest0 : is_digest_row air (nextRow air row) = 0 :=
    digest_implies_next_not_digest air row hrow hrot ht hdigest
  have hf_next : flag_constraints air (nextRow air row) :=
    flag_constraints_of_blockHasherConstraints air hc (nextRow air row)
  rcases is_round_row_boolean air (nextRow air row) hf_next with hnext_round0 | hnext_round1
  · have hnext_round0' : next_is_round_row air row = 0 := by
      simpa [next_is_round_row_eq_nextRow air hrot row hrow] using hnext_round0
    have hnext_digest0' : next_is_digest_row air row = 0 := by
      simpa [next_is_digest_row_eq_nextRow air hrot row hrow] using hnext_digest0
    simp [next_padding_flag, hnext_round0', hnext_digest0']
  · have hnext_pad0 : next_padding_flag air row = 0 := by
      have hnext_round1' : next_is_round_row air row = 1 := by
        simpa [next_is_round_row_eq_nextRow air hrot row hrow] using hnext_round1
      have hnext_digest0' : next_is_digest_row air row = 0 := by
        simpa [next_is_digest_row_eq_nextRow air hrot row hrow] using hnext_digest0
      simp [next_padding_flag, hnext_round1', hnext_digest0']
    have hgbi_eq_zero : global_block_idx air row = 0 := by
      have hkey' : global_block_idx air row + 1 = 0 + 1 := by
        simpa [private_bus_next_gbi, hnext_pad0] using hkey
      exact add_right_cancel hkey'
    exact False.elim
      (supported_real_row_global_block_idx_ne_zero air htrace_fit hrot hc row hrow (Or.inr hdigest)
        hgbi_eq_zero)

private theorem digest_row_key_ne_one_implies_next_padding_zero
    (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hdigest : is_digest_row air row = 1)
    (hkey_ne : private_bus_next_gbi air row ≠ 1) :
    next_padding_flag air row = 0 := by
  have hrow_lt : row < Circuit.last_row air := digest_row_lt_last_row air row hc hrow hdigest
  have ht : trace_shape_constraints air row :=
    trace_shape_constraints_of_blockHasherConstraints air hc row
  have hnext_digest0 : is_digest_row air (nextRow air row) = 0 :=
    digest_implies_next_not_digest air row hrow hrot ht hdigest
  have hf_next : flag_constraints air (nextRow air row) :=
    flag_constraints_of_blockHasherConstraints air hc (nextRow air row)
  rcases is_round_row_boolean air (nextRow air row) hf_next with hnext_round0 | hnext_round1
  · have hkey_one : private_bus_next_gbi air row = 1 := by
      have hnext_round0' : next_is_round_row air row = 0 := by
        simpa [next_is_round_row_eq_nextRow air hrot row hrow] using hnext_round0
      have hnext_digest0' : next_is_digest_row air row = 0 := by
        simpa [next_is_digest_row_eq_nextRow air hrot row hrow] using hnext_digest0
      simp [private_bus_next_gbi, next_padding_flag, hnext_round0', hnext_digest0']
    exact False.elim (hkey_ne hkey_one)
  · have hnext_round1' : next_is_round_row air row = 1 := by
      simpa [next_is_round_row_eq_nextRow air hrot row hrow] using hnext_round1
    have hnext_digest0' : next_is_digest_row air row = 0 := by
      simpa [next_is_digest_row_eq_nextRow air hrot row hrow] using hnext_digest0
    simp [next_padding_flag, hnext_round1', hnext_digest0']

private theorem digest_sender_key_eq_impossible_of_lt
    (air : C FBB ExtF)
    (htrace_fit : traceLengthFitsField air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    ∀ r1 r2,
      r1 < r2 →
      r1 ≤ Circuit.last_row air →
      r2 ≤ Circuit.last_row air →
      is_digest_row air r1 = 1 →
      is_digest_row air r2 = 1 →
      private_bus_next_gbi air r1 = private_bus_next_gbi air r2 →
      False := by
  intro r1 r2 hlt hr1 hr2 hd1 hd2 hkey
  have hr1_lt_last : r1 < Circuit.last_row air := digest_row_lt_last_row air r1 hc hr1 hd1
  have ht1 : trace_shape_constraints air r1 :=
    trace_shape_constraints_of_blockHasherConstraints air hc r1
  have hnext_digest0 : is_digest_row air (r1 + 1) = 0 := by
    simpa [nextRow, hr1_lt_last.ne] using
      digest_implies_next_not_digest air r1 hr1 hrot ht1 hd1
  have hgap : r1 + 1 < r2 := by
    by_contra hnot
    have hsucc : r1 + 1 = r2 := by omega
    have : is_digest_row air (r1 + 1) = 1 := by simpa [hsucc] using hd2
    exact False.elim ((by decide : (0 : FBB) ≠ 1) (hnext_digest0 ▸ this))
  have hnext_real : is_round_row air (r1 + 1) = 1 ∨ is_digest_row air (r1 + 1) = 1 :=
    row_before_supported_real_row_is_real air (r1 + 1) r2 hgap hr2 hrot hc (Or.inr hd2)
  have hnext_round1 : is_round_row air (r1 + 1) = 1 := by
    rcases hnext_real with hround | hdigest
    · exact hround
    · have : (0 : FBB) = 1 := by simpa [hnext_digest0] using hdigest
      exact False.elim ((by decide : (0 : FBB) ≠ 1) this)
  have hnext_round1' : next_is_round_row air r1 = 1 := by
    calc
      next_is_round_row air r1 = is_round_row air (nextRow air r1) :=
        next_is_round_row_eq_nextRow air hrot r1 hr1
      _ = is_round_row air (r1 + 1) := by simp [nextRow, hr1_lt_last.ne]
      _ = 1 := hnext_round1
  have hnext_digest0' : next_is_digest_row air r1 = 0 := by
    calc
      next_is_digest_row air r1 = is_digest_row air (nextRow air r1) :=
        next_is_digest_row_eq_nextRow air hrot r1 hr1
      _ = is_digest_row air (r1 + 1) := by simp [nextRow, hr1_lt_last.ne]
      _ = 0 := hnext_digest0
  have hkey1_ne : private_bus_next_gbi air r1 ≠ 1 := by
    intro hkey1
    have hnext_pad1 :=
      digest_row_send_key_one_implies_next_padding air r1 htrace_fit hr1 hrot hc hd1 hkey1
    have : next_padding_flag air r1 = 0 := by
      simp [next_padding_flag, hnext_round1', hnext_digest0']
    exact False.elim ((by decide : (0 : FBB) ≠ 1) (this ▸ hnext_pad1))
  have hnext_pad1_zero :=
    digest_row_key_ne_one_implies_next_padding_zero air r1 hr1 hrot hc hd1 hkey1_ne
  have hkey2_ne : private_bus_next_gbi air r2 ≠ 1 := by
    intro hkey2
    exact hkey1_ne (hkey.trans hkey2)
  have hnext_pad2_zero :=
    digest_row_key_ne_one_implies_next_padding_zero air r2 hr2 hrot hc hd2 hkey2_ne
  have hgbi_eq : global_block_idx air r1 = global_block_idx air r2 := by
    have hsend1 : private_bus_next_gbi air r1 = global_block_idx air r1 + 1 := by
      simp [private_bus_next_gbi, hnext_pad1_zero]
    have hsend2 : private_bus_next_gbi air r2 = global_block_idx air r2 + 1 := by
      simp [private_bus_next_gbi, hnext_pad2_zero]
    have hplus : global_block_idx air r1 + 1 = global_block_idx air r2 + 1 := by
      calc
        global_block_idx air r1 + 1 = private_bus_next_gbi air r1 := hsend1.symm
        _ = private_bus_next_gbi air r2 := hkey
        _ = global_block_idx air r2 + 1 := hsend2
    exact add_right_cancel hplus
  exact digest_row_same_gbi_impossible_of_lt air htrace_fit hrot hc
    r1 r2 hlt hr1 hr2 hd1 hd2 hgbi_eq

/-- The private-bus sender key is derivable from the constraint system: on
    supported digest rows the send-side `private_bus_next_gbi` values are
    unique once `global_block_idx` is shown to be injective on digest rows and
    the wrapped `key = 1` case is identified as the unique final digest row. -/
theorem uniqueDigestSenderByNextGlobalBlockIdx_of_constraints
    (air : C FBB ExtF)
    (htrace_fit : traceLengthFitsField air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    uniqueDigestSenderByNextGlobalBlockIdx air := by
  intro r1 r2 hr1 hr2 hd1 hd2 hkey
  rcases lt_trichotomy r1 r2 with hlt | rfl | hgt
  · exact False.elim
      (digest_sender_key_eq_impossible_of_lt air htrace_fit hrot hc r1 r2 hlt hr1 hr2 hd1 hd2 hkey)
  · rfl
  · exact False.elim
      (digest_sender_key_eq_impossible_of_lt air htrace_fit hrot hc r2 r1 hgt hr2 hr1 hd2 hd1 hkey.symm)

/-! ## Helper lemmas on the serialized private-bus messages -/

/-- The send payload ends with the sender's `private_bus_next_gbi`. -/
@[simp] theorem privateBus_send_data_get?_key
    (air : C FBB ExtF) (row : ℕ) :
    List.getLast? (privateBus_send_data air row) = some (private_bus_next_gbi air row) := by
  simp [privateBus_send_data]

/-- The receive payload ends with the receiver's `global_block_idx`. -/
@[simp] theorem privateBus_recv_data_get?_key
    (air : C FBB ExtF) (row : ℕ) :
    List.getLast? (privateBus_recv_data air row) = some (global_block_idx air row) := by
  simp [privateBus_recv_data]

/-- Equality of a send payload and a receive payload forces equality of their keys. -/
theorem privateBus_send_eq_recv_implies_key_eq
    (air : C FBB ExtF) (sendRow recvRow : ℕ)
    (hmsg : privateBus_send_data air sendRow = privateBus_recv_data air recvRow) :
    private_bus_next_gbi air sendRow = global_block_idx air recvRow := by
  have hkey := congrArg (fun xs => List.getLast? xs) hmsg
  simpa using hkey

/-! ## Interaction-level bridge lemmas -/

private theorem privateBusTraceEntries_unitary_with_zero
    (air : C FBB ExtF)
    (hc : blockHasherConstraints air) :
    InteractionList.unitary_with_zero (privateBusTraceEntries air) := by
  intro entry hentry
  rcases (mem_privateBusTraceEntries_iff (air := air) (entry := entry)).mp hentry with
    ⟨row, _hvalid, hentry_row⟩
  have hflags : flagsWellFormed air row :=
    flagsWellFormed_of_flag_constraints air row
      (flag_constraints_of_blockHasherConstraints air hc row)
  have hdigest_bool : is_digest_row air row = 0 ∨ is_digest_row air row = 1 := hflags.2.2.1
  rcases hdigest_bool with hdigest0 | hdigest1
  · simp [privateBus_row, privateBus_send_entry, privateBus_recv_entry, hdigest0] at hentry_row
    rcases hentry_row with hsend | hrecv
    · right
      left
      simpa [hsend]
    · right
      left
      simpa [hrecv]
  · simp [privateBus_row, privateBus_send_entry, privateBus_recv_entry, hdigest1] at hentry_row
    rcases hentry_row with hsend | hrecv
    · right
      right
      simpa [hsend]
    · left
      simpa [hrecv]

private theorem recv_payload_mem_privateBusEnabledReceives
    (air : C FBB ExtF)
    (recvRow : ℕ)
    (hvalid : recvRow ≤ Circuit.last_row air)
    (hdigest : is_digest_row air recvRow = 1) :
    privateBus_recv_data air recvRow ∈ privateBusEnabledReceives air := by
  have hentry_enabled : privateBus_recv_entry air recvRow ∈ privateBusEnabledEntries air := by
    rw [privateBusEnabledEntries, InteractionList.non_zero]
    apply List.mem_filter.mpr
    constructor
    · exact (mem_privateBusTraceEntries_iff (air := air)
        (entry := privateBus_recv_entry air recvRow)).mpr
          ⟨recvRow, hvalid, by simp [privateBus_row]⟩
    · simp [privateBus_recv_entry, hdigest]
  exact mem_filterMap_of_mem_some
    (f := fun x : FBB × List FBB ↦ if x.1 = -1 then some x.2 else none)
    hentry_enabled
    (by simp [privateBus_recv_entry, hdigest])

private theorem exists_digest_sender_of_mem_privateBusEnabledSends
    (air : C FBB ExtF)
    (hc : blockHasherConstraints air)
    {data : List FBB}
    (hdata : data ∈ privateBusEnabledSends air) :
    ∃ sendRow,
      sendRow ≤ Circuit.last_row air ∧
      is_digest_row air sendRow = 1 ∧
      privateBus_send_data air sendRow = data := by
  rcases exists_mem_eq_some_of_mem_filterMap
      (f := fun x : FBB × List FBB ↦ if x.1 = 1 then some x.2 else none) hdata with
    ⟨entry, hentry_enabled, hentry_some⟩
  rcases entry with ⟨m, payload⟩
  have hm : m = 1 := by
    by_cases h : m = 1
    · exact h
    · simp [h] at hentry_some
  have hpayload : payload = data := by
    simpa [hm] using hentry_some
  have hentry_trace : (m, payload) ∈ privateBusTraceEntries air := by
    rw [privateBusEnabledEntries, InteractionList.non_zero] at hentry_enabled
    exact List.mem_of_mem_filter hentry_enabled
  rcases (mem_privateBusTraceEntries_iff (air := air) (entry := (m, payload))).mp hentry_trace with
    ⟨row, hvalid, hentry_row⟩
  have hflags : flagsWellFormed air row :=
    flagsWellFormed_of_flag_constraints air row
      (flag_constraints_of_blockHasherConstraints air hc row)
  have hdigest_bool : is_digest_row air row = 0 ∨ is_digest_row air row = 1 := hflags.2.2.1
  have hentry_cases :
      (m, payload) = privateBus_send_entry air row ∨
      (m, payload) = privateBus_recv_entry air row := by
    simpa [privateBus_row] using hentry_row
  rcases hentry_cases with hsend | hrecv
  · refine ⟨row, hvalid, ?_, ?_⟩
    · simpa [privateBus_send_entry, hm] using congrArg Prod.fst hsend
    · have hsend_payload : payload = privateBus_send_data air row := by
        simpa [privateBus_send_entry] using congrArg Prod.snd hsend
      calc
        privateBus_send_data air row = payload := hsend_payload.symm
        _ = data := hpayload
  · rcases hdigest_bool with hdigest0 | hdigest1
    · simp [privateBus_recv_entry, hm, hdigest0] at hrecv
    · simp [privateBus_recv_entry, hm, hdigest1] at hrecv

private theorem privateBusEnabledEntries_eq_digestRows_flatMap
    (air : C FBB ExtF)
    (hc : blockHasherConstraints air) :
    privateBusEnabledEntries air =
      (((List.range (Circuit.last_row air + 1)).filter
        (fun row => decide (is_digest_row air row = 1))).flatMap (privateBus_row air)) := by
  unfold privateBusEnabledEntries privateBusTraceEntries privateBus_trace InteractionList.non_zero
  induction List.range (Circuit.last_row air + 1) with
  | nil =>
      simp
  | cons row rows ih =>
      have hflags : flagsWellFormed air row :=
        flagsWellFormed_of_flag_constraints air row
          (flag_constraints_of_blockHasherConstraints air hc row)
      have hdigest_bool : is_digest_row air row = 0 ∨ is_digest_row air row = 1 := hflags.2.2.1
      rcases hdigest_bool with hdigest0 | hdigest1
      · simp [ih, privateBus_row, privateBus_send_entry, privateBus_recv_entry, hdigest0]
      · simp [ih, privateBus_row, privateBus_send_entry, privateBus_recv_entry, hdigest1]

private theorem privateBus_row_flatMap_length
    (air : C FBB ExtF) :
    ∀ rows : List ℕ,
      (rows.flatMap (privateBus_row air)).length = 2 * rows.length
  | [] => by simp
  | _ :: rows => by
      simp [privateBus_row, privateBus_row_flatMap_length air rows]
      omega

private theorem digestRows_chain_gap
    (air : C FBB ExtF)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    (((List.range (Circuit.last_row air + 1)).filter
      (fun row => decide (is_digest_row air row = 1)))).IsChain
      (fun a b => a + 1 < b) := by
  let digestRows :=
    ((List.range (Circuit.last_row air + 1)).filter
      (fun row => decide (is_digest_row air row = 1)))
  have hdigest_pairwise_lt : digestRows.Pairwise (· < ·) := by
    dsimp [digestRows]
    simpa using (List.pairwise_lt_range :
      (List.range (Circuit.last_row air + 1)).Pairwise (· < ·)).filter
      (fun row => decide (is_digest_row air row = 1))
  have hdigest_chain_lt : digestRows.IsChain (· < ·) := hdigest_pairwise_lt.isChain
  refine hdigest_chain_lt.imp_of_mem_imp ?_
  intro a b ha hb hab
  have ha_range : a < Circuit.last_row air + 1 := by
    exact List.mem_range.mp ((List.mem_filter.mp ha).1)
  have ha_valid : a ≤ Circuit.last_row air := Nat.lt_succ_iff.mp ha_range
  have ha_digest : is_digest_row air a = 1 := by
    simpa using (List.mem_filter.mp ha).2
  have hb_digest : is_digest_row air b = 1 := by
    simpa using (List.mem_filter.mp hb).2
  have ha_lt_last : a < Circuit.last_row air := digest_row_lt_last_row air a hc ha_valid ha_digest
  have hnext_digest0 : is_digest_row air (a + 1) = 0 := by
    have ht : trace_shape_constraints air a :=
      trace_shape_constraints_of_blockHasherConstraints air hc a
    calc
      is_digest_row air (a + 1) = is_digest_row air (nextRow air a) := by
        simp [nextRow, ha_lt_last.ne]
      _ = 0 := digest_implies_next_not_digest air a ha_valid hrot ht ha_digest
  have hsucc_ne : b ≠ a + 1 := by
    intro hsucc
    have : (0 : FBB) = 1 := by simpa [hsucc, hnext_digest0] using hb_digest
    exact (by decide : (0 : FBB) ≠ 1) this
  omega

private theorem digestRows_half_lt
    (air : C FBB ExtF)
    (hc : blockHasherConstraints air) :
    ∀ row ∈ ((List.range (Circuit.last_row air + 1)).filter
      (fun row => decide (is_digest_row air row = 1))),
      row / 2 < (Circuit.last_row air + 1) / 2 := by
  intro row hrow
  have hrow_range : row < Circuit.last_row air + 1 := by
    exact List.mem_range.mp ((List.mem_filter.mp hrow).1)
  have hrow_valid : row ≤ Circuit.last_row air := Nat.lt_succ_iff.mp hrow_range
  have hrow_digest : is_digest_row air row = 1 := by
    simpa using (List.mem_filter.mp hrow).2
  have hrow_lt_last : row < Circuit.last_row air := digest_row_lt_last_row air row hc hrow_valid hrow_digest
  omega

/-- The non-zero private-bus entries are short enough for the generic balanced-bus
    permutation theorem once trace length fits in `BabyBear`. -/
theorem privateBusEnabledEntriesFitField_of_traceLengthFitsField
    (air : C FBB ExtF)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (htrace_fit : traceLengthFitsField air) :
    privateBusEnabledEntriesFitField air := by
  let digestRows :=
    ((List.range (Circuit.last_row air + 1)).filter
      (fun row => decide (is_digest_row air row = 1)))
  have henabled_eq :
      privateBusEnabledEntries air = digestRows.flatMap (privateBus_row air) := by
    simpa [digestRows] using privateBusEnabledEntries_eq_digestRows_flatMap air hc
  have hdigest_chain_gap : digestRows.IsChain (fun a b => a + 1 < b) := by
    simpa [digestRows] using digestRows_chain_gap air hrot hc
  have hdigest_half_lt : ∀ row ∈ digestRows, row / 2 < (Circuit.last_row air + 1) / 2 := by
    simpa [digestRows] using digestRows_half_lt air hc
  let halfDigestRows : List (Fin ((Circuit.last_row air + 1) / 2)) :=
    digestRows.pmap (fun row hlt => ⟨row / 2, hlt⟩) hdigest_half_lt
  have hhalf_chain : halfDigestRows.IsChain (· < ·) := by
    dsimp [halfDigestRows]
    refine List.isChain_pmap_of_isChain ?_ hdigest_chain_gap hdigest_half_lt
    intro a b ha hb hab
    have hab_half : a / 2 < b / 2 := by
      omega
    simpa using hab_half
  have hhalf_nodup : halfDigestRows.Nodup := hhalf_chain.pairwise.nodup
  have hdigest_len_le : digestRows.length ≤ (Circuit.last_row air + 1) / 2 := by
    simpa [halfDigestRows, Fintype.card_fin] using List.Nodup.length_le_card hhalf_nodup
  have henabled_len_eq :
      (privateBusEnabledEntries air).length = 2 * digestRows.length := by
    calc
      (privateBusEnabledEntries air).length = (digestRows.flatMap (privateBus_row air)).length := by
        simpa [henabled_eq]
      _ = 2 * digestRows.length := privateBus_row_flatMap_length air digestRows
  have henabled_len_le : (privateBusEnabledEntries air).length ≤ Circuit.last_row air + 1 := by
    rw [henabled_len_eq]
    omega
  exact lt_of_le_of_lt henabled_len_le htrace_fit

/-! ## Main reduction theorem -/

/-- On supported digest rows, receive coverage and sender-key uniqueness are
    already enough to recover the block proof's chaining fact. -/
theorem privateBusChainingSupported_of_receiveCoverage_and_unique_sender_keys
    (air : C FBB ExtF)
    (hcover : privateBusReceiveCovered air)
    (huniq_send : uniqueDigestSenderByNextGlobalBlockIdx air) :
    privateBusChainingSupported air := by
  intro r1 r2 hr1_valid hr2_valid hd1 hd2 hkey
  rcases hcover r2 hr2_valid hd2 with ⟨sendRow, hsend_valid, hsend_dig, hmsg⟩
  have hsend_key : private_bus_next_gbi air sendRow = global_block_idx air r2 := by
    exact privateBus_send_eq_recv_implies_key_eq (air := air) (sendRow := sendRow)
      (recvRow := r2) hmsg
  have hsame_key : private_bus_next_gbi air r1 = private_bus_next_gbi air sendRow := by
    calc
      private_bus_next_gbi air r1 = global_block_idx air r2 := hkey
      _ = private_bus_next_gbi air sendRow := hsend_key.symm
  have hr1 : r1 = sendRow := huniq_send r1 sendRow hr1_valid hsend_valid hd1 hsend_dig hsame_key
  simpa [hr1] using hmsg

/-! ## Permutation and chaining from raw bus semantics -/

/-- The enabled receive payloads are a permutation of the enabled send payloads. -/
theorem privateBusEnabledReceiveSendPerm_of_rawPermutationSemantics
    (air : C FBB ExtF)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (htrace_fit : traceLengthFitsField air) :
    (privateBusEnabledReceives air).Perm (privateBusEnabledSends air) := by
  have h_balanced_enabled : InteractionList.is_balanced (privateBusEnabledEntries air) := by
    exact (InteractionList.non_zero_inv_is_balanced (privateBusTraceEntries air)).mp h_raw_perm
  have h_unitary_enabled : InteractionList.unitary (privateBusEnabledEntries air) := by
    exact InteractionList.unitary_zero_mult_non_zero_is_unitary (privateBusTraceEntries air)
      (privateBusTraceEntries_unitary_with_zero air hc)
  have h_bus_size : privateBusEnabledEntriesFitField air :=
    privateBusEnabledEntriesFitField_of_traceLengthFitsField air hrot hc htrace_fit
  simpa [privateBusEnabledReceives, privateBusEnabledSends] using
    (InteractionList.unitary_balanced_recvs_perm_sends
      (bus := privateBusEnabledEntries air)
      h_unitary_enabled h_balanced_enabled h_bus_size)

/-- Every digest-row receive payload is covered by some digest-row send payload. -/
theorem privateBusReceiveCovered_of_permutation
    (air : C FBB ExtF)
    (hc : blockHasherConstraints air)
    (h_recv_send_perm :
      (privateBusEnabledReceives air).Perm (privateBusEnabledSends air)) :
    privateBusReceiveCovered air := by
  intro recvRow hvalid_recv hdigest
  have hrecv_mem : privateBus_recv_data air recvRow ∈ privateBusEnabledReceives air := by
    exact recv_payload_mem_privateBusEnabledReceives air recvRow hvalid_recv hdigest
  have hsend_mem : privateBus_recv_data air recvRow ∈ privateBusEnabledSends air := by
    exact (List.Perm.mem_iff h_recv_send_perm).mp hrecv_mem
  rcases exists_digest_sender_of_mem_privateBusEnabledSends air hc hsend_mem with
    ⟨sendRow, hvalid_send, hsend_dig, hmsg⟩
  exact ⟨sendRow, hvalid_send, hsend_dig, hmsg⟩

/-- Raw permutation semantics plus sender-key uniqueness imply block chaining. -/
theorem privateBusChainingSupported_of_rawPermutationSemantics
    (air : C FBB ExtF)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (h_raw_perm : privateBusRawPermutationSemantics air)
    (htrace_fit : traceLengthFitsField air)
    (huniq_send : uniqueDigestSenderByNextGlobalBlockIdx air) :
    privateBusChainingSupported air := by
  have hperm :=
    privateBusEnabledReceiveSendPerm_of_rawPermutationSemantics air hrot hc h_raw_perm htrace_fit
  have hcover := privateBusReceiveCovered_of_permutation air hc hperm
  exact privateBusChainingSupported_of_receiveCoverage_and_unique_sender_keys air hcover huniq_send

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
