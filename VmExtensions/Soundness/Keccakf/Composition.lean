/-
  Keccak-f cross-AIR composition: definitions and composition theorem.

  This file defines the logup bus-balance predicate and supporting definitions
  for composing the opcode-side (KeccakfOpAir) and permutation-side
  (KeccakfPermAir) AIRs via the shared keccak state bus (bus 7).

  The composition is row-native: it works directly with `export_flag = 1` rows
  on the perm side, bypassing the structural `exportedBlocks` layer entirely.
  No `h_exportFlagBridge` assumption is needed.
-/
import VmExtensions.Soundness.Keccakf.Soundness
import VmExtensions.Soundness.Keccakf.Wireup
import VmExtensions.Soundness.Keccakf.OpTimestampUnique
import VmExtensions.Soundness.KeccakfOpAir.Connect
import VmExtensions.Soundness.KeccakfPermAir.BlockSoundness
import VmExtensions.Soundness.KeccakfPermAir.BusFacts
import VmExtensions.Constraints.KeccakfStateBus
import VmExtensions.Airs.KeccakfPermAirViews
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false

open Keccakf.Interface
open BabyBear

namespace Keccakf.Soundness

open Keccakf.Soundness.Concrete
open Keccakf.constraints
open Consistency
open KeccakfOpAir
open KeccakfOpAir.Views
open KeccakfOpAir.constraints
open KeccakfOpAir.Soundness
open KeccakfOpAir.WFC
open KeccakfPermAir
open KeccakfPermAir.constraints

variable {ExtF : Type} [Field ExtF]

/-- Extract send payloads from a serialized bus trace: entries with multiplicity = 1. -/
noncomputable def sendPayloads (trace : List (FBB × List FBB)) : List (List FBB) :=
  trace.filterMap (fun x => if x.1 = 1 then some x.2 else none)

/-- Extract receive payloads from a serialized bus trace: entries with multiplicity = -1. -/
noncomputable def receivePayloads (trace : List (FBB × List FBB)) : List (List FBB) :=
  trace.filterMap (fun x => if x.1 = -1 then some x.2 else none)

/-- The actual perm-side bus-7 trace: raw constrained output from all rows.
    Each row contributes two (multiplicity, payload) entries via bus_7Bus_row,
    where multiplicity = -(export_flag permAir row). -/
noncomputable def actualPermBus7Trace
    (permAir : Valid_KeccakfPermAir FBB ExtF) : List (FBB × List FBB) :=
  (List.range (permAir.last_row + 1)).flatMap (bus_7Bus_row permAir)

/-- Logup send/receive payload balance on the keccak state bus (bus 7):
    the multiset of send payloads (multiplicity = 1) from the op-side equals
    the multiset of receive payloads (multiplicity = -1) from the perm-side,
    after filtering by multiplicity sign from actual constrained traces.
    Op-side: all entries have multiplicity 1, so all are sends.
    Perm-side: multiplicity = -(export_flag): ef=1 rows are receives (-1),
    ef=0 rows have zero multiplicity and are filtered out. -/
def LogupBusBalance
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF) : Prop :=
  List.Perm
    (sendPayloads (opStateBusTrace opAir (enabledRows opAir)))
    (receivePayloads (actualPermBus7Trace permAir))

/-- Combined bus-7 trace from both AIRs: op-side sends ++ perm-side receives.
    Op-side uses `enabledRows` (is_valid = 1 only); perm-side uses all rows. -/
noncomputable def combinedBus7Trace
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF) : List (FBB × List FBB) :=
  opStateBusTrace opAir (enabledRows opAir) ++ actualPermBus7Trace permAir

/-! ## Per-row receive-payload classification -/

-- filterMap distributes over flatMap.
private lemma filterMap_flatMap {α β γ : Type}
    (f : β → Option γ) (g : α → List β) (l : List α) :
    (l.flatMap g).filterMap f = l.flatMap (fun a => (g a).filterMap f) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.filterMap_append, ih]

-- export_flag is 0 or 1, derived from constraint_248 (ef * (ef - 1) = 0).
private lemma ef_zero_or_one
    {permAir : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h : allHold_simplified permAir row) :
    export_flag permAir row = 0 ∨ export_flag permAir row = 1 := by
  have h_bool := KeccakfPermAir.Soundness.export_flag_boolean h
  rcases mul_eq_zero.mp h_bool with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

-- When ef=0, bus_7Bus_row contributes zero-multiplicity entries excluded by receivePayloads.
private lemma receivePayloads_bus_7Bus_row_zero
    (permAir : Valid_KeccakfPermAir FBB ExtF) (row : ℕ)
    (h : export_flag permAir row = 0) :
    receivePayloads (bus_7Bus_row permAir row) = [] := by
  unfold receivePayloads
  rw [bus_7Bus_row_eq_payloads, h]
  simp

-- When ef=1, bus_7Bus_row contributes multiplicity=-1 entries kept by receivePayloads.
private lemma receivePayloads_bus_7Bus_row_one
    (permAir : Valid_KeccakfPermAir FBB ExtF) (row : ℕ)
    (h : export_flag permAir row = 1) :
    receivePayloads (bus_7Bus_row permAir row) =
      [busPrePayload permAir row, busPostPayload permAir row] := by
  unfold receivePayloads
  rw [bus_7Bus_row_eq_payloads, h]
  simp

/-! ## Framework-shaped bus balance → LogupBusBalance derivation -/

-- Op-side entries all have multiplicity 1.
private lemma opStateBusRow_mult_one
    (opAir : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (entry : FBB × List FBB) (h : entry ∈ opStateBusRow opAir row) :
    entry.1 = 1 := by
  simp [opStateBusRow, Keccakf.constraints.serialiseToList,
    opStateBusEntries, opPreEntry, opPostEntry, msgToAssertEntry] at h
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

private lemma opStateBusTrace_mult_one
    (opAir : Valid_KeccakfOpAir FBB ExtF) (rows : List ℕ)
    (entry : FBB × List FBB) (h : entry ∈ opStateBusTrace opAir rows) :
    entry.1 = 1 := by
  rw [opStateBusTrace_eq_flatMap_row] at h
  rcases List.mem_flatMap.mp h with ⟨row, _, h_in⟩
  exact opStateBusRow_mult_one opAir row entry h_in

-- Perm-side entries have multiplicity -(ef) ∈ {0, -1}.
private lemma bus_7Bus_row_mult
    {permAir : Valid_KeccakfPermAir FBB ExtF} {row : ℕ}
    (h_hold : allHold_simplified permAir row)
    (entry : FBB × List FBB) (h : entry ∈ bus_7Bus_row permAir row) :
    entry.1 = 0 ∨ entry.1 = -1 := by
  rw [bus_7Bus_row_eq_payloads] at h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases ef_zero_or_one h_hold with h0 | h1
  · rcases h with rfl | rfl <;> simp [h0]
  · rcases h with rfl | rfl <;> simp [h1]

private lemma actualPermBus7Trace_mult
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_permAllHold : ∀ row, row ≤ permAir.last_row →
      allHold_simplified permAir row)
    (entry : FBB × List FBB) (h : entry ∈ actualPermBus7Trace permAir) :
    entry.1 = 0 ∨ entry.1 = -1 := by
  simp only [actualPermBus7Trace] at h
  rcases List.mem_flatMap.mp h with ⟨row, h_row_mem, h_in⟩
  have h_row : row ≤ permAir.last_row := by
    simp only [List.mem_range] at h_row_mem; omega
  exact bus_7Bus_row_mult (h_permAllHold row h_row) entry h_in

-- Combined trace is unitary_with_zero: all multiplicities ∈ {-1, 0, 1}.
private lemma combinedBus7Trace_unitary_with_zero
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_permAllHold : ∀ row, row ≤ permAir.last_row →
      allHold_simplified permAir row) :
    InteractionList.unitary_with_zero (combinedBus7Trace opAir permAir) := by
  intro entry h_mem
  simp only [combinedBus7Trace, List.mem_append] at h_mem
  rcases h_mem with h_op | h_perm
  · exact Or.inr (Or.inr (opStateBusTrace_mult_one opAir _ entry h_op))
  · rcases actualPermBus7Trace_mult permAir h_permAllHold entry h_perm with h0 | h1
    · exact Or.inr (Or.inl h0)
    · exact Or.inl h1

-- sendPayloads of the perm trace is empty (mult ∈ {0,-1}, never 1).
private lemma actualPermBus7Trace_sendPayloads_nil
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_permAllHold : ∀ row, row ≤ permAir.last_row →
      allHold_simplified permAir row) :
    sendPayloads (actualPermBus7Trace permAir) = [] := by
  have h_dist : sendPayloads (actualPermBus7Trace permAir) =
    (List.range (permAir.last_row + 1)).flatMap
      (fun row => sendPayloads (bus_7Bus_row permAir row)) := by
    unfold actualPermBus7Trace sendPayloads
    exact filterMap_flatMap _ _ _
  rw [h_dist]
  apply List.flatMap_eq_nil_iff.mpr
  intro row h_row_mem
  have h_row : row ≤ permAir.last_row := by
    simp only [List.mem_range] at h_row_mem; omega
  unfold sendPayloads
  rw [bus_7Bus_row_eq_payloads]
  rcases ef_zero_or_one (h_permAllHold row h_row) with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

-- receivePayloads of the op trace is empty (mult = 1, never -1).
private lemma opStateBusTrace_receivePayloads_nil
    (opAir : Valid_KeccakfOpAir FBB ExtF) (rows : List ℕ) :
    receivePayloads (opStateBusTrace opAir rows) = [] := by
  exact opStateBusTrace_recvs_nil_on opAir rows

-- sendPayloads/receivePayloads are invariant under non_zero pre-filtering:
-- non_zero removes mult=0; sends/recvs only keep mult=±1 (non-zero).
-- General: filterMap is invariant under pre-filtering when the filter
-- cannot remove elements that filterMap would keep.
-- General: filterMap is invariant under pre-filtering when the filter
-- cannot remove elements that filterMap would keep.
private lemma filterMap_filter_invariant {α β : Type}
    (f : α → Option β) (p : α → Bool) (l : List α)
    (hfp : ∀ x, f x ≠ none → p x = true) :
    (l.filter p).filterMap f = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases hp : p x with
    | false =>
      have hf : f x = none := by by_contra hne; simp [hfp x hne] at hp
      simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte,
        List.filterMap_cons, hf, ih]
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, List.filterMap_cons]
      cases f x with
      | none => exact ih
      | some b => exact congrArg (b :: ·) ih

private lemma sendPayloads_non_zero_eq (bus : List (FBB × List FBB)) :
    sendPayloads (InteractionList.non_zero bus) = sendPayloads bus := by
  show (InteractionList.non_zero bus).filterMap _ = bus.filterMap _
  exact filterMap_filter_invariant _ _ _ (fun ⟨m, d⟩ h => by
    have hm : m = 1 := by by_contra hne; simp [hne] at h
    simp [hm])

private lemma receivePayloads_non_zero_eq (bus : List (FBB × List FBB)) :
    receivePayloads (InteractionList.non_zero bus) = receivePayloads bus := by
  show (InteractionList.non_zero bus).filterMap _ = bus.filterMap _
  exact filterMap_filter_invariant _ _ _ (fun ⟨m, d⟩ h => by
    have hm : m = -1 := by by_contra hne; simp [hne] at h
    simp [hm])

/-- From framework-shaped bus balance, derive LogupBusBalance via the chain:
    non_zero_inv_is_balanced → unitary_zero_mult_non_zero_is_unitary →
    unitary_balanced_recvs_perm_sends. -/
lemma bus7_balanced_implies_logup
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_permAllHold : ∀ row, row ≤ permAir.last_row →
      allHold_simplified permAir row)
    (h_bus7_balanced : InteractionList.is_balanced (combinedBus7Trace opAir permAir))
    (h_bus7_length : (combinedBus7Trace opAir permAir).length < BB_prime) :
    LogupBusBalance opAir permAir := by
  -- Step 1: Framework chain on non_zero combined trace
  have h_uwz := combinedBus7Trace_unitary_with_zero opAir permAir h_permAllHold
  set nz := InteractionList.non_zero (combinedBus7Trace opAir permAir)
  have h_nz_unitary : InteractionList.unitary nz :=
    InteractionList.unitary_zero_mult_non_zero_is_unitary _ h_uwz
  have h_nz_balanced : InteractionList.is_balanced nz :=
    (InteractionList.non_zero_inv_is_balanced _).mp h_bus7_balanced
  have h_nz_len : nz.length < BB_prime :=
    lt_of_le_of_lt (List.length_filter_le _ _) h_bus7_length
  have h_perm := InteractionList.unitary_balanced_recvs_perm_sends
    h_nz_unitary h_nz_balanced h_nz_len
  -- h_perm : recvs(nz).Perm sends(nz) where sends/recvs are let-bound filterMaps
  -- Step 2: Bridge sends(nz) = sendPayloads(opTrace) and recvs(nz) = receivePayloads(permTrace)
  have h_sends : sendPayloads nz = sendPayloads (opStateBusTrace opAir (enabledRows opAir)) := by
    rw [sendPayloads_non_zero_eq]
    unfold sendPayloads combinedBus7Trace
    rw [List.filterMap_append]
    have := actualPermBus7Trace_sendPayloads_nil permAir h_permAllHold
    unfold sendPayloads at this
    rw [this, List.append_nil]
  have h_recvs : receivePayloads nz =
      receivePayloads (actualPermBus7Trace permAir) := by
    rw [receivePayloads_non_zero_eq]
    unfold receivePayloads combinedBus7Trace
    rw [List.filterMap_append]
    have := opStateBusTrace_receivePayloads_nil opAir (enabledRows opAir)
    unfold receivePayloads at this
    rw [this, List.nil_append]
  -- Step 3: Conclude LogupBusBalance
  show List.Perm
    (sendPayloads (opStateBusTrace opAir (enabledRows opAir)))
    (receivePayloads (actualPermBus7Trace permAir))
  rw [← h_sends, ← h_recvs]
  -- h_perm is: (nz.filterMap recvFilter).Perm (nz.filterMap sendFilter)
  -- which is: receivePayloads nz .Perm sendPayloads nz
  exact h_perm.symm

/-! ## Row-native receive-payload decomposition -/

-- Decompose membership in receivePayloads(actualPermBus7Trace) into:
-- exists perm row with ef=1 and payload = busPrePayload or busPostPayload.
-- Does NOT use h_exportFlagBridge.
lemma mem_receivePayloads_actualPermBus7Trace
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_permAllHold : ∀ row, row ≤ permAir.last_row →
      allHold_simplified permAir row)
    {payload : List FBB}
    (h : payload ∈ receivePayloads (actualPermBus7Trace permAir)) :
    ∃ row, row ≤ permAir.last_row ∧ export_flag permAir row = 1 ∧
      (payload = busPrePayload permAir row ∨ payload = busPostPayload permAir row) := by
  -- Step 1: distribute filterMap over flatMap
  have h_dist : receivePayloads (actualPermBus7Trace permAir) =
    (List.range (permAir.last_row + 1)).flatMap
      (fun row => receivePayloads (bus_7Bus_row permAir row)) := by
    unfold actualPermBus7Trace receivePayloads
    exact filterMap_flatMap _ _ _
  rw [h_dist] at h
  -- Step 2: h says payload is in the flatMap; extract the contributing row
  rcases List.mem_flatMap.mp h with ⟨row, h_row_mem, h_payload_mem⟩
  have h_row : row ≤ permAir.last_row := by
    simp only [List.mem_range] at h_row_mem; omega
  -- Step 3: classify ef at this row
  rcases ef_zero_or_one (h_permAllHold row h_row) with h0 | h1
  · -- ef=0: row contributes [], contradicts membership
    rw [receivePayloads_bus_7Bus_row_zero permAir row h0] at h_payload_mem
    simp at h_payload_mem
  · -- ef=1: row contributes [busPrePayload, busPostPayload]
    rw [receivePayloads_bus_7Bus_row_one permAir row h1] at h_payload_mem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_payload_mem
    exact ⟨row, h_row, h1, h_payload_mem⟩

-- From logup, each enabled op pre-payload is in receivePayloads(actualPermBus7Trace).
lemma opPrePayload_mem_receivePayloads
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_logup : LogupBusBalance opAir permAir)
    {row : ℕ} (h_row : row ≤ opAir.last_row) (h_valid : is_valid opAir row = 1) :
    msgPayloadList (preMsgOfColumns opAir row) ∈
      receivePayloads (actualPermBus7Trace permAir) := by
  have h_send_eq :
      sendPayloads (opStateBusTrace opAir (enabledRows opAir)) = opPayloadTrace opAir := by
    simpa [sendPayloads] using opStateBusTrace_sends_eq_payloadTrace opAir
  have h_logup' : List.Perm (opPayloadTrace opAir)
      (receivePayloads (actualPermBus7Trace permAir)) := by
    rw [← h_send_eq]; exact h_logup
  exact h_logup'.mem_iff.mp (opPayloadTrace_pre_mem opAir h_row h_valid)

-- From logup, each enabled op post-payload is in receivePayloads(actualPermBus7Trace).
lemma opPostPayload_mem_receivePayloads
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_logup : LogupBusBalance opAir permAir)
    {row : ℕ} (h_row : row ≤ opAir.last_row) (h_valid : is_valid opAir row = 1) :
    msgPayloadList (postMsgOfColumns opAir row) ∈
      receivePayloads (actualPermBus7Trace permAir) := by
  have h_send_eq :
      sendPayloads (opStateBusTrace opAir (enabledRows opAir)) = opPayloadTrace opAir := by
    simpa [sendPayloads] using opStateBusTrace_sends_eq_payloadTrace opAir
  have h_logup' : List.Perm (opPayloadTrace opAir)
      (receivePayloads (actualPermBus7Trace permAir)) := by
    rw [← h_send_eq]; exact h_logup
  exact h_logup'.mem_iff.mp (opPayloadTrace_post_mem opAir h_row h_valid)

set_option maxHeartbeats 800000

/-- Unpack the op-side keccak bus assertion into the concrete pre/post payload
    flag and limb bounds used to transfer u16 wellformedness across the payload
    equalities in `logup_derives_row_pairing`. -/
private lemma opAssert_row_pre_post_wf
    {ExtF : Type} [Field ExtF]
    (opAir : Valid_KeccakfOpAir FBB ExtF) (row : ℕ)
    (h : wf_propertiesToAssertPerOpRow opAir row) :
    (((msgPayload (preMsgOfColumns opAir row))[0] = 0 ∨
        (msgPayload (preMsgOfColumns opAir row))[0] = 1) ∧
      ∀ i : Fin 100, ((msgPayload (preMsgOfColumns opAir row))[i.val + 2]).val < 2 ^ 16)
    ∧
    (((msgPayload (postMsgOfColumns opAir row))[0] = 0 ∨
        (msgPayload (postMsgOfColumns opAir row))[0] = 1) ∧
      ∀ i : Fin 100, ((msgPayload (postMsgOfColumns opAir row))[i.val + 2]).val < 2 ^ 16) := by
  simp only [wf_propertiesToAssertPerOpRow, Keccakf.constraints.propertiesToAssert,
    opStateBusEntries] at h
  constructor
  · exact h.1 (by simp [opPreEntry, msgToAssertEntry])
  · exact h.2 (by simp [opPostEntry, msgToAssertEntry])

/-! ## Row-native flag discrimination helpers -/

-- A post-message payload carries flag 1, so it cannot equal a
-- permPreRowEntry payload whose flag is definitionally 0.
private lemma post_payload_ne_permPreRowEntry
    {ExtF : Type} [Field ExtF]
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (row permRow : ℕ)
    (h_eq : msgPayload (postMsgOfColumns opAir row) = (permPreRowEntry permAir permRow).payload) :
    False := by
  have h_flag := congrArg (fun v => v[0]) h_eq
  have h_post_flag := msgPayload_flag (postMsgOfColumns opAir row)
  rw [post_flag] at h_post_flag
  have h_permPre_flag : ((permPreRowEntry permAir permRow).payload[0]) = 0 := by
    simp [permPreRowEntry]
  have h10 : (1 : FBB) = 0 := by
    calc (1 : FBB) = (msgPayload (postMsgOfColumns opAir row))[0] := by
          simpa [flagField] using h_post_flag.symm
      _ = ((permPreRowEntry permAir permRow).payload[0]) := h_flag
      _ = 0 := h_permPre_flag
  exact absurd h10.symm (by intro h; have := congrArg Fin.val h; simp at this)

-- A pre-message payload carries flag 0, so it cannot equal a
-- permPostRowEntry payload whose flag is definitionally 1.
private lemma pre_payload_ne_permPostRowEntry
    {ExtF : Type} [Field ExtF]
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (row permRow : ℕ)
    (h_eq : msgPayload (preMsgOfColumns opAir row) = (permPostRowEntry permAir permRow).payload) :
    False := by
  have h_flag := congrArg (fun v => v[0]) h_eq
  have h_pre_flag := msgPayload_flag (preMsgOfColumns opAir row)
  rw [pre_flag] at h_pre_flag
  have h_permPost_flag : ((permPostRowEntry permAir permRow).payload[0]) = 1 := by
    simp [permPostRowEntry]
  have h01 : (0 : FBB) = 1 := by
    calc (0 : FBB) = (msgPayload (preMsgOfColumns opAir row))[0] := by
          simpa [flagField] using h_pre_flag.symm
      _ = ((permPostRowEntry permAir permRow).payload[0]) := h_flag
      _ = 1 := h_permPost_flag
  exact absurd h01 (by intro h; have := congrArg Fin.val h; simp at this)

-- busPrePayload at a row equals (permPreRowEntry.payload).toList.
set_option maxRecDepth 1024 in
set_option maxHeartbeats 1600000 in
private lemma busPrePayload_eq_permPreRowEntry_toList
    (air : Valid_KeccakfPermAir FBB ExtF) (row : ℕ) :
    busPrePayload air row = ((permPreRowEntry air row).payload).toList := by
  simp only [busPrePayload, permPreRowEntry, Vector.toList_ofFn, List.ofFn]
  rfl

-- busPostPayload at a row equals (permPostRowEntry.payload).toList.
set_option maxRecDepth 1024 in
set_option maxHeartbeats 1600000 in
private lemma busPostPayload_eq_permPostRowEntry_toList
    (air : Valid_KeccakfPermAir FBB ExtF) (row : ℕ) :
    busPostPayload air row = ((permPostRowEntry air row).payload).toList := by
  simp only [busPostPayload, permPostRowEntry, Vector.toList_ofFn, List.ofFn]
  rfl

/-! ## Helper lemmas for OpTimestampUnique-based step 6 argument -/

-- Decompose membership in opPayloadTrace: every element comes from a specific
-- enabled row as either the pre or post payload.
private lemma mem_opPayloadTrace_decompose
    (opAir : Valid_KeccakfOpAir FBB ExtF) {p : List FBB}
    (h : p ∈ opPayloadTrace opAir) :
    ∃ row, row ≤ opAir.last_row ∧ is_valid opAir row = 1 ∧
      (p = msgPayloadList (preMsgOfColumns opAir row) ∨
       p = msgPayloadList (postMsgOfColumns opAir row)) := by
  unfold opPayloadTrace at h
  rcases List.mem_flatMap.mp h with ⟨row, h_row_mem, h_p_mem⟩
  have ⟨h_row, h_valid⟩ := (mem_enabledRows opAir row).mp h_row_mem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_p_mem
  exact ⟨row, h_row, h_valid, h_p_mem⟩

-- enabledRows has Nodup (filter of range, which is Nodup).
private lemma enabledRows_nodup (opAir : Valid_KeccakfOpAir FBB ExtF) :
    (enabledRows opAir).Nodup := by
  unfold enabledRows
  exact List.Nodup.filter _ (List.nodup_range)

-- Equal payloads from enabled rows with matching timestamps → equal timestamps.
private lemma payload_eq_implies_ts_val_eq
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    {msg₁ msg₂ : KeccakStateMsg}
    {row₁ row₂ : ℕ}
    (h1 : msg₁.timestamp = (KeccakfOpAir.constraints.timestamp opAir row₁).val)
    (h2 : msg₂.timestamp = (KeccakfOpAir.constraints.timestamp opAir row₂).val)
    (h_eq : msgPayloadList msg₁ = msgPayloadList msg₂) :
    (KeccakfOpAir.constraints.timestamp opAir row₁).val =
      (KeccakfOpAir.constraints.timestamp opAir row₂).val := by
  have h_payload := Vector.toList_inj.mp (by simpa [msgPayloadList] using h_eq)
  have h_fbb := msgPayload_eq_implies_timestamp_field_eq h_payload
  rw [h1, h2] at h_fbb
  exact fbb_natCast_inj_of_lt
    (KeccakfOpAir.constraints.timestamp opAir row₁).isLt
    (KeccakfOpAir.constraints.timestamp opAir row₂).isLt h_fbb

-- Pre and post payloads from the same row are different (flag 0 ≠ 1).
private lemma pre_ne_post_same_row
    (opAir : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    msgPayloadList (preMsgOfColumns opAir row) ≠ msgPayloadList (postMsgOfColumns opAir row) := by
  intro heq
  have h_payload := Vector.toList_inj.mp (by simpa [msgPayloadList] using heq)
  have h_flag := msgPayload_eq_implies_flagField_eq h_payload
  simp [preMsgOfColumns, mkPreMsg, postMsgOfColumns, mkPostMsg, flagField] at h_flag

-- Build Pairwise from Nodup + universal pairwise predicate with membership context.
private lemma pairwise_of_forall_ne {α : Type} {R : α → α → Prop} {l : List α}
    (h_nd : l.Nodup) (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b) :
    l.Pairwise R := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons hd tl ih =>
    rw [List.nodup_cons] at h_nd
    rw [List.pairwise_cons]
    constructor
    · intro b hb
      exact h hd (by simp) b (List.mem_cons_of_mem _ hb) (fun hc => h_nd.1 (hc ▸ hb))
    · exact ih h_nd.2 (fun a ha b hb =>
        h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))

-- A payload appearing in contributions from two different enabled rows is impossible.
-- Uses equality chaining (h1.symm.trans h2) instead of rfl-substitution to avoid
-- expensive WHNF expansion in the large context.
private lemma opPayload_ne_across_rows
    (opAir : Valid_KeccakfOpAir FBB ExtF) (h_opUnique : OpTimestampUnique opAir)
    {a b : ℕ} (ha1 : a ≤ opAir.last_row) (hb1 : b ≤ opAir.last_row)
    (ha2 : is_valid opAir a = 1) (hb2 : is_valid opAir b = 1)
    (hab : a ≠ b) {p : List FBB}
    (hp1 : p = msgPayloadList (preMsgOfColumns opAir a) ∨
           p = msgPayloadList (postMsgOfColumns opAir a))
    (hp2 : p = msgPayloadList (preMsgOfColumns opAir b) ∨
           p = msgPayloadList (postMsgOfColumns opAir b)) : False := by
  have h_ts : (KeccakfOpAir.constraints.timestamp opAir a).val =
      (KeccakfOpAir.constraints.timestamp opAir b).val := by
    rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2 <;>
      exact payload_eq_implies_ts_val_eq opAir rfl rfl (h1.symm.trans h2)
  exact hab (h_opUnique a b ha1 hb1 ha2 hb2 h_ts)

-- The send list (opPayloadTrace) has no duplicates when OpTimestampUnique holds.
private lemma opPayloadTrace_nodup
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (h_opUnique : OpTimestampUnique opAir) :
    (opPayloadTrace opAir).Nodup := by
  unfold opPayloadTrace
  rw [List.nodup_flatMap]
  constructor
  · intro row _
    simp only [List.nodup_cons, List.mem_cons, or_false,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
    exact pre_ne_post_same_row opAir row
  · apply pairwise_of_forall_ne (enabledRows_nodup opAir)
    intro a ha b hb hab p hp1 hp2
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp1 hp2
    have ⟨ha1, ha2⟩ := (mem_enabledRows opAir a).mp ha
    have ⟨hb1, hb2⟩ := (mem_enabledRows opAir b).mp hb
    exact opPayload_ne_across_rows opAir h_opUnique ha1 hb1 ha2 hb2 hab hp1 hp2

-- The receive list (receivePayloads of actualPermBus7Trace) equals a flatMap
-- decomposition over all rows.
private lemma recvs_eq_flatMap
    (permAir : Valid_KeccakfPermAir FBB ExtF) :
    receivePayloads (actualPermBus7Trace permAir) =
      (List.range (permAir.last_row + 1)).flatMap
        (fun row => receivePayloads (bus_7Bus_row permAir row)) := by
  unfold actualPermBus7Trace receivePayloads
  exact filterMap_flatMap _ _ _

-- If a perm row has ef=1, its busPrePayload is in the receive list.
private lemma busPrePayload_mem_recvs_of_ef
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    {row : ℕ} (h_row : row ≤ permAir.last_row)
    (h_ef : export_flag permAir row = 1) :
    busPrePayload permAir row ∈
      receivePayloads (actualPermBus7Trace permAir) := by
  rw [recvs_eq_flatMap]
  apply List.mem_flatMap.mpr
  refine ⟨row, List.mem_range.mpr (by omega), ?_⟩
  rw [receivePayloads_bus_7Bus_row_one permAir row h_ef]
  simp

-- When busPrePayload equals msgPayloadList of a preMsgOfColumns, the perm
-- timestamp (natural number) equals the op timestamp (natural number).
-- Bridges through permPreRowEntry and msgPayload_timestamp.
-- When busPrePayload matches a msgPayloadList of a preMsgOfColumns, the perm
-- timestamp equals the op timestamp (as natural numbers).
-- Bridges through permPreRowEntry ↔ msgPayload at index 1 (the timestamp field).
set_option maxHeartbeats 3200000 in
private lemma busPrePayload_pre_match_ts
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    {permRow opRow : ℕ}
    (h : busPrePayload permAir permRow = msgPayloadList (preMsgOfColumns opAir opRow)) :
    (KeccakfPermAir.constraints.timestamp permAir permRow).val =
      (KeccakfOpAir.constraints.timestamp opAir opRow).val := by
  -- Bridge: busPrePayload = permPreRowEntry.payload.toList
  have h_vec : (permPreRowEntry permAir permRow).payload =
      msgPayload (preMsgOfColumns opAir opRow) := by
    apply Vector.toList_inj.mp
    rw [← busPrePayload_eq_permPreRowEntry_toList]
    simpa [msgPayloadList] using h
  -- Extract element at index 1 from the Vector equality
  have h1 := congrFun (congrArg Vector.get h_vec) ⟨1, by omega⟩
  -- LHS: permPreRowEntry.payload = Vector.ofFn f, so .get ⟨1, _⟩ = f ⟨1, _⟩ = perm_ts
  conv at h1 => lhs; rw [show (permPreRowEntry permAir permRow).payload =
    Vector.ofFn (fun i : Fin 102 =>
      if i.val = 0 then 0
      else if i.val = 1 then KeccakfPermAir.constraints.timestamp permAir permRow
      else KeccakfPermAir.constraints.preimage permAir (i.val - 2) permRow) from rfl]
  rw [Vector.get_ofFn] at h1
  simp only [show ¬((1 : ℕ) = 0) from by omega, ite_false, ite_true] at h1
  -- RHS: msgPayload[1] = (msg.timestamp : FBB) by msgPayload_timestamp
  have h_rhs := msgPayload_timestamp (preMsgOfColumns opAir opRow)
  -- msgPayload_timestamp uses [1] notation; we need .get ⟨1, _⟩ form
  -- Both are definitionally equal via GetElem
  rw [show (msgPayload (preMsgOfColumns opAir opRow)).get ⟨1, by omega⟩ =
      (msgPayload (preMsgOfColumns opAir opRow))[1] from rfl,
      h_rhs, show (preMsgOfColumns opAir opRow).timestamp =
      (KeccakfOpAir.constraints.timestamp opAir opRow).val from rfl] at h1
  -- h1 : perm_ts = ((op_ts.val : ℕ) : FBB)
  have := congrArg Fin.val h1
  rwa [fbb_val_natCast (KeccakfOpAir.constraints.timestamp opAir opRow).isLt] at this

-- Two distinct elements of a Nodup list contributing a shared element to a
-- flatMap make the result not Nodup.
private lemma flatMap_not_nodup_of_shared_element
    {α β : Type} [DecidableEq β]
    {l : List α} {f : α → List β}
    {a₁ a₂ : α} {b : β}
    (h₁ : a₁ ∈ l) (h₂ : a₂ ∈ l) (hne : a₁ ≠ a₂) (hnd : l.Nodup)
    (hb₁ : b ∈ f a₁) (hb₂ : b ∈ f a₂) :
    ¬ (l.flatMap f).Nodup := by
  induction l with
  | nil => simp at h₁
  | cons hd tl ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.flatMap_cons]
    intro h_nodup
    simp only [List.mem_cons] at h₁ h₂
    rcases h₁ with rfl | h₁'
    · rcases h₂ with rfl | h₂'
      · exact absurd rfl hne
      · -- b ∈ f hd and b ∈ tl.flatMap f → contradicts append Nodup
        have h_in_right : b ∈ tl.flatMap f := List.mem_flatMap.mpr ⟨a₂, h₂', hb₂⟩
        exact absurd h_in_right (List.disjoint_of_nodup_append h_nodup hb₁)
    · rcases h₂ with rfl | h₂'
      · have h_in_right : b ∈ tl.flatMap f := List.mem_flatMap.mpr ⟨a₁, h₁', hb₁⟩
        exact absurd h_in_right (List.disjoint_of_nodup_append h_nodup hb₂)
      · exact ih h₁' h₂' hnd.2 ((List.nodup_append.mp h_nodup).2.1)

set_option maxHeartbeats 8000000

/-- Derives shared-bus row pairing from logup by matching each
    enabled op payload to a perm row with ef=1, transferring u16 bounds, bridging
    to row-native message views, and using Op-side timestamp uniqueness. -/
lemma logup_derives_row_pairing
    {ExtF : Type} [Field ExtF]
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_logup : LogupBusBalance opAir permAir)
    (h_permAllHold : ∀ row, row ≤ permAir.last_row →
      allHold_simplified permAir row)
    (h_opAssert : ∀ row, row ≤ opAir.last_row → is_valid opAir row = 1 →
      wf_propertiesToAssertPerOpRow opAir row)
    (h_opTsBound : ∀ row, row ≤ opAir.last_row → is_valid opAir row = 1 →
      (preMsgOfColumns opAir row).timestamp < timestampBound
      ∧ (postMsgOfColumns opAir row).timestamp < timestampBound)
    (h_opUnique : OpTimestampUnique opAir) :
    KeccakStateBusRowPairing opAir permAir := by
  intro row h_row h_valid

  -- Step 0: from logup, the pre/post payloads land in the perm receive trace.
  have h_pre_mem := opPrePayload_mem_receivePayloads opAir permAir h_logup h_row h_valid
  have h_post_mem := opPostPayload_mem_receivePayloads opAir permAir h_logup h_row h_valid

  -- Step 1: decompose — get perm rows with ef=1 and payload match.
  rcases mem_receivePayloads_actualPermBus7Trace permAir h_permAllHold h_pre_mem with
    ⟨r_pre, h_r_pre_le, h_r_pre_ef, h_pre_payload⟩
  rcases mem_receivePayloads_actualPermBus7Trace permAir h_permAllHold h_post_mem with
    ⟨r_post, h_r_post_le, h_r_post_ef, h_post_payload⟩

  -- Step 2: flag discrimination — case-split on pre payload match.
  rcases h_pre_payload with h_pre_eq | h_pre_eq_post
  · -- pre op payload = busPrePayload r_pre → bridge to permPreRowEntry
    rw [busPrePayload_eq_permPreRowEntry_toList] at h_pre_eq
    have h_pre_payload_eq :
        msgPayload (preMsgOfColumns opAir row) = (permPreRowEntry permAir r_pre).payload :=
      Vector.toList_inj.mp (by simpa [msgPayloadList] using h_pre_eq)

    -- Case-split on post payload match.
    rcases h_post_payload with h_post_eq_pre | h_post_eq
    · -- post op payload = busPrePayload r_post → contradiction (flag 1 ≠ 0)
      rw [busPrePayload_eq_permPreRowEntry_toList] at h_post_eq_pre
      exact False.elim (post_payload_ne_permPreRowEntry opAir permAir row r_post
        (Vector.toList_inj.mp (by simpa [msgPayloadList] using h_post_eq_pre)))
    · -- post op payload = busPostPayload r_post → bridge to permPostRowEntry
      rw [busPostPayload_eq_permPostRowEntry_toList] at h_post_eq
      have h_post_payload_eq :
          msgPayload (postMsgOfColumns opAir row) = (permPostRowEntry permAir r_post).payload :=
        Vector.toList_inj.mp (by simpa [msgPayloadList] using h_post_eq)

      -- Step 3: extract op-side u16 bounds and transfer to perm columns.
      have h_opAssert_wf := opAssert_row_pre_post_wf opAir row (h_opAssert row h_row h_valid)
      have h_pre_wf := h_opAssert_wf.1
      have h_post_wf := h_opAssert_wf.2

      have h_pre_u16 : ∀ i, i < 100 →
          (KeccakfPermAir.constraints.preimage permAir i r_pre).val < 2 ^ 16 := by
        intro i hi
        have h_i := h_pre_wf.2 ⟨i, hi⟩
        rw [h_pre_payload_eq] at h_i
        simpa [permPreRowEntry, Vector.getElem_ofFn,
          show ¬(i + 2 = 0) by omega,
          show ¬(i + 2 = 1) by omega,
          show i + 2 - 2 = i by omega] using h_i

      have h_post_u16 : ∀ i, i < 100 →
          (if i < 4
           then (KeccakfPermAir.constraints.a_ppp_00_limb permAir i r_post).val
           else (KeccakfPermAir.constraints.a_prime_prime permAir i r_post).val) < 2 ^ 16 := by
        intro i hi
        have h_i := h_post_wf.2 ⟨i, hi⟩
        rw [h_post_payload_eq] at h_i
        by_cases h4 : i < 4
        · simpa [permPostRowEntry, Vector.getElem_ofFn,
            show ¬(i + 2 = 0) by omega,
            show ¬(i + 2 = 1) by omega,
            show i + 2 - 2 = i by omega, h4] using h_i
        · simpa [permPostRowEntry, Vector.getElem_ofFn,
            show ¬(i + 2 = 0) by omega,
            show ¬(i + 2 = 1) by omega,
            show i + 2 - 2 = i by omega, h4] using h_i

      -- Step 4: bridge raw perm payloads back to row-native perm messages.
      have h_pre_bridge :
          msgPayload (rowPreMsg permAir r_pre) = (permPreRowEntry permAir r_pre).payload :=
        msgPayload_rowPreMsg_eq_permPreRowEntry permAir r_pre h_pre_u16
      have h_post_bridge :
          msgPayload (rowPostMsg permAir r_post) = (permPostRowEntry permAir r_post).payload :=
        msgPayload_rowPostMsg_eq_permPostRowEntry permAir r_post h_post_u16

      -- Step 5: timestamp equality and message injectivity.
      have h_pre_payload_msg :
          msgPayload (preMsgOfColumns opAir row) = msgPayload (rowPreMsg permAir r_pre) :=
        h_pre_payload_eq.trans h_pre_bridge.symm
      have h_post_payload_msg :
          msgPayload (postMsgOfColumns opAir row) = msgPayload (rowPostMsg permAir r_post) :=
        h_post_payload_eq.trans h_post_bridge.symm
      have h_pre_payload_list :
          msgPayloadList (preMsgOfColumns opAir row) =
            msgPayloadList (rowPreMsg permAir r_pre) := by
        simp only [msgPayloadList]; exact congrArg _ h_pre_payload_msg
      have h_post_payload_list :
          msgPayloadList (postMsgOfColumns opAir row) =
            msgPayloadList (rowPostMsg permAir r_post) := by
        simp only [msgPayloadList]; exact congrArg _ h_post_payload_msg
      have h_ts := h_opTsBound row h_row h_valid
      have h_pre_ts_eq :
          (preMsgOfColumns opAir row).timestamp = (rowPreMsg permAir r_pre).timestamp := by
        apply fbb_natCast_inj_of_lt
          (lt_trans h_ts.1 timestampBound_lt_BBPrime)
          (by simp [rowPreMsg])
        exact msgPayload_eq_implies_timestamp_field_eq h_pre_payload_msg
      have h_post_ts_eq :
          (postMsgOfColumns opAir row).timestamp = (rowPostMsg permAir r_post).timestamp := by
        apply fbb_natCast_inj_of_lt
          (lt_trans h_ts.2 timestampBound_lt_BBPrime)
          (by simp [rowPostMsg])
        exact msgPayload_eq_implies_timestamp_field_eq h_post_payload_msg
      have h_pre_perm_ts_lt : (rowPreMsg permAir r_pre).timestamp < timestampBound :=
        h_pre_ts_eq ▸ h_ts.1
      have h_post_perm_ts_lt : (rowPostMsg permAir r_post).timestamp < timestampBound :=
        h_post_ts_eq ▸ h_ts.2
      have h_pre_msg_eq : preMsgOfColumns opAir row = rowPreMsg permAir r_pre :=
        msgPayloadList_inj_of_timestamp_lt h_ts.1 h_pre_perm_ts_lt h_pre_payload_list
      have h_post_msg_eq : postMsgOfColumns opAir row = rowPostMsg permAir r_post :=
        msgPayloadList_inj_of_timestamp_lt h_ts.2 h_post_perm_ts_lt h_post_payload_list

      -- Step 6: same-row matching via OpTimestampUnique + bus Nodup.
      -- By contradiction: assume r_pre ≠ r_post. Both have ef=1 and contribute
      -- busPrePayloads to recvs. Via the bus permutation + OpTimestampUnique,
      -- both busPrePayloads equal the op pre-payload → duplicate in recvs
      -- contradicts Nodup (from sends Nodup via Perm).
      have h_same_row : r_pre = r_post := by
        by_contra h_ne
        -- Recvs is Nodup (from Perm + sends Nodup via OpTimestampUnique)
        have h_sends_nd := opPayloadTrace_nodup opAir h_opUnique
        have h_send_eq : sendPayloads (opStateBusTrace opAir (enabledRows opAir)) =
            opPayloadTrace opAir := by
          simpa [sendPayloads] using opStateBusTrace_sends_eq_payloadTrace opAir
        have h_recvs_nd : (receivePayloads (actualPermBus7Trace permAir)).Nodup := by
          rw [← h_send_eq] at h_sends_nd
          exact h_logup.nodup_iff.mp h_sends_nd
        -- r_post has ef=1, so busPrePayload(r_post) is in receives
        have h_bp_in_recvs := busPrePayload_mem_recvs_of_ef permAir h_r_post_le h_r_post_ef
        -- By Perm, busPrePayload(r_post) is in sends = opPayloadTrace
        have h_bp_in_sends : busPrePayload permAir r_post ∈ opPayloadTrace opAir := by
          rw [← h_send_eq]
          exact h_logup.symm.mem_iff.mp h_bp_in_recvs
        -- Decompose: busPrePayload(r_post) = pre or post payload of some op row
        rcases mem_opPayloadTrace_decompose opAir h_bp_in_sends with
          ⟨opRow, h_opRow_le, h_opRow_valid, h_match⟩
        rcases h_match with h_pre_match | h_post_match
        · -- Case: busPrePayload(r_post) = msgPayloadList(preMsgOfColumns opAir opRow)
          -- Show opRow = row via OpTimestampUnique on the timestamp chain:
          -- perm_ts(r_post) = op_ts(opRow) [from payload equality, via helper]
          -- op_ts(row) = perm_ts(r_post)   [from step 5]
          have h_opRow_eq : opRow = row := by
            apply h_opUnique opRow row h_opRow_le h_row h_opRow_valid h_valid
            -- perm ts(r_post).val = op ts(opRow).val (from busPrePayload/msgPayloadList match)
            have h_a := busPrePayload_pre_match_ts permAir opAir h_pre_match
            -- op ts(row).val = perm ts(r_post).val (from step 5)
            have h_b : (KeccakfOpAir.constraints.timestamp opAir row).val =
                (KeccakfPermAir.constraints.timestamp permAir r_post).val :=
              h_post_ts_eq
            omega
          -- So busPrePayload(r_post) = busPrePayload(r_pre) (both = op pre-payload at row)
          rw [h_opRow_eq] at h_pre_match
          -- h_pre_match : busPrePayload r_post = msgPayloadList(pre row)
          -- h_pre_eq : msgPayloadList(pre row) = permPreRowEntry(r_pre).payload.toList
          -- (busPrePayload_eq_permPreRowEntry_toList r_pre).symm bridges back
          have h_bp_eq : busPrePayload permAir r_post = busPrePayload permAir r_pre :=
            h_pre_match.trans (h_pre_eq.trans
              (busPrePayload_eq_permPreRowEntry_toList permAir r_pre).symm)
          -- Duplicate in recvs contradicts Nodup
          rw [recvs_eq_flatMap] at h_recvs_nd
          exact flatMap_not_nodup_of_shared_element
            (b := busPrePayload permAir r_pre)
            (List.mem_range.mpr (by omega : r_pre < permAir.last_row + 1))
            (List.mem_range.mpr (by omega : r_post < permAir.last_row + 1))
            h_ne (List.nodup_range)
            (by rw [receivePayloads_bus_7Bus_row_one permAir r_pre h_r_pre_ef]
                exact List.Mem.head _)
            (by rw [receivePayloads_bus_7Bus_row_one permAir r_post h_r_post_ef, h_bp_eq]
                exact List.Mem.head _)
            h_recvs_nd
        · -- Case: busPrePayload(r_post) = msgPayloadList(postMsgOfColumns opAir opRow)
          -- Contradiction: busPrePayload flag=0 vs postMsg flag=1
          -- Bridge through permPreRowEntry and reuse post_payload_ne_permPreRowEntry
          rw [busPrePayload_eq_permPreRowEntry_toList] at h_post_match
          exact post_payload_ne_permPreRowEntry opAir permAir opRow r_post
            (Vector.toList_inj.mp (by simpa [msgPayloadList] using h_post_match.symm))

      -- Step 7: assemble the row pairing witness.
      exact ⟨r_pre, h_r_pre_le, h_r_pre_ef, h_pre_msg_eq, h_same_row ▸ h_post_msg_eq⟩

  · -- pre op payload = busPostPayload r_pre → contradiction (flag 0 ≠ 1)
    rw [busPostPayload_eq_permPostRowEntry_toList] at h_pre_eq_post
    exact False.elim (pre_payload_ne_permPostRowEntry opAir permAir row r_pre
      (Vector.toList_inj.mp (by simpa [msgPayloadList] using h_pre_eq_post)))

/-- Converts the derived row-based pairing into the spec-facing
    row statement by pulling back the perm-side permutation fact through the
    matched pre/post messages and the opcode row's decode links. -/
lemma pairing_gives_spec_row
    {ExtF : Type} [Field ExtF]
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    {row : ℕ} (h_row : row ≤ opAir.last_row) (h_valid : is_valid opAir row = 1)
    (h_opContract : KeccakfOpRowLocalContract opAir row)
    (h_perm : KeccakfPermRowProperty permAir)
    (h_pairing : KeccakStateBusRowPairing opAir permAir) :
    keccakf_row_matches_spec opAir row := by
  rcases h_pairing row h_row h_valid with ⟨permRow, h_permRow_le, h_ef, h_pre_eq, h_post_eq⟩
  have h_permutes := h_perm permRow h_permRow_le h_ef
  have h_bus :
      decodeBusState (postMsgOfColumns opAir row).state =
        Keccak.keccakF (decodeBusState (preMsgOfColumns opAir row).state) := by
    simpa [Keccakf.Interface.BusKeccakPermutes, h_pre_eq, h_post_eq] using h_permutes
  rcases h_opContract with ⟨h_local, h_input_decode, h_output_decode⟩
  have h_postimage :
      (outputOfColumns decodeBusState opAir row).postimage =
        (KeccakfOp.Spec.execute (inputOfColumns decodeBusState opAir row)).postimage := by
    calc
      (outputOfColumns decodeBusState opAir row).postimage
          = decodeBusState (postMsgOfColumns opAir row).state := h_output_decode
      _ = Keccak.keccakF (decodeBusState (preMsgOfColumns opAir row).state) := h_bus
      _ = Keccak.keccakF ((inputOfColumns decodeBusState opAir row).preimage) := by
        rw [← h_input_decode]
      _ = (KeccakfOp.Spec.execute (inputOfColumns decodeBusState opAir row)).postimage := by
        simp [KeccakfOp.Spec.execute]
  dsimp [keccakf_row_matches_spec, outputOfColumns, inputOfColumns, KeccakfOp.Spec.execute]
  rw [KeccakfOp.Spec.KeccakfOpOutput.mk.injEq]
  exact ⟨h_local.execution.next_pc,
    h_local.execution.end_timestamp,
    h_postimage⟩

/-- Primary composition: obtain opcode-side assertion and row-contract facts from
    `row_soundness`, derive row-native shared-bus pairing from logup, derive the
    row-native perm-side permutation property from constraints, and conclude the
    spec match on each enabled opcode row via `pairing_gives_spec_row`.
    `h_bus7_balanced` replaces the former ad-hoc `h_logup : LogupBusBalance`
    with a framework-shaped `InteractionList.is_balanced` on the combined trace. -/
theorem keccakf_row_soundness
    {ExtF : Type} [Field ExtF]
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF)
    (h_opAllHold : ∀ row (h_row : row ≤ opAir.last_row),
      allHold_simplified opAir row h_row)
    (h_opAxioms : ∀ row, row ≤ opAir.last_row →
      axiomsPerRow opAir row)
    (h_opWfAssume : ∀ row, row ≤ opAir.last_row →
      wf_propertiesToAssumePerRow opAir row)
    (h_permAllHold : ∀ row, row ≤ permAir.last_row →
      allHold_simplified permAir row)
    (h_bus7_balanced : InteractionList.is_balanced (combinedBus7Trace opAir permAir))
    (h_bus7_length : (combinedBus7Trace opAir permAir).length < BB_prime)
    -- Execution bus balance (framework-shaped, abstract chip list)
    {chips : List (WFChip μ)} {lb rb : List FBB}
    (h_opAir_chip : KeccakfOpAir.WFC.wfc_opAir h_opAllHold h_opAxioms h_opWfAssume ∈ chips)
    (h_bus_length : 2 * (execution_bus chips).length +
                    2 * (memory_bus chips).length + 2 < BB_prime)
    (h_exec_balanced : InteractionList.is_balanced
      ([((1 : FBB), lb)] ++
       InteractionList.rising_bus μ (execution_bus chips)
         (execution_bus_is_rising_bus chips) ++
       [((-1 : FBB), rb)])) :
    ∀ row, row ≤ opAir.last_row →
      is_valid opAir row = 0 ∨ keccakf_row_matches_spec opAir row := by
  -- Derive LogupBusBalance from framework-shaped bus balance
  have h_logup : LogupBusBalance opAir permAir :=
    bus7_balanced_implies_logup opAir permAir h_permAllHold h_bus7_balanced h_bus7_length
  have h_opAssert : ∀ row, row ≤ opAir.last_row → is_valid opAir row = 1 →
      wf_propertiesToAssertPerOpRow opAir row := by
    intro row h_row h_valid
    have h_sound :=
      row_soundness opAir row h_row
        (rows_of_allHold_simplified (h_opAllHold row h_row))
        (h_opAxioms row h_row)
        (h_opWfAssume row h_row)
    have h_pre_entry :
        opPreEntry opAir row = KeccakfOpAir.constraints._keccakfStateBus_pre_entry opAir row := by
      simp [opPreEntry, KeccakfOpAir.constraints._keccakfStateBus_pre_entry, msgToAssertEntry, h_valid]
    have h_post_entry :
        opPostEntry opAir row = KeccakfOpAir.constraints._keccakfStateBus_post_entry opAir row := by
      simp [opPostEntry, KeccakfOpAir.constraints._keccakfStateBus_post_entry,
        msgToAssertEntry, h_valid]
    unfold wf_propertiesToAssertPerOpRow Keccakf.constraints.propertiesToAssert opStateBusEntries
    rw [h_pre_entry, h_post_entry]
    simpa [Keccakf.constraints.propertiesToAssert,
      KeccakfOpAir.constraints._keccakfStateBus_row] using h_sound.1.2.2.2.2.2
  have h_opTsBound : ∀ row, row ≤ opAir.last_row → is_valid opAir row = 1 →
      (preMsgOfColumns opAir row).timestamp < timestampBound
      ∧ (postMsgOfColumns opAir row).timestamp < timestampBound := by
    intro row h_row h_valid
    have h_ts := timestamp_bound opAir row (h_opAxioms row h_row) h_valid
    exact ⟨by simpa [preMsgOfColumns] using h_ts,
      by simpa [postMsgOfColumns] using h_ts⟩
  have h_opUnique : OpTimestampUnique opAir :=
    op_timestamp_unique opAir h_opAllHold h_opAxioms h_opWfAssume
      h_opAir_chip h_bus_length h_exec_balanced
  have h_pairing : KeccakStateBusRowPairing opAir permAir :=
    logup_derives_row_pairing opAir permAir h_logup h_permAllHold
      h_opAssert h_opTsBound h_opUnique
  have h_perm : KeccakfPermRowProperty permAir :=
    KeccakfPermAir.Soundness.BlockSoundness.keccakf_perm_row_soundness permAir h_permAllHold
  intro row h_row
  have h_sound :=
    row_soundness opAir row h_row
      (rows_of_allHold_simplified (h_opAllHold row h_row))
      (h_opAxioms row h_row)
      (h_opWfAssume row h_row)
  rcases h_sound.2 with h_disabled | h_enabled
  · exact Or.inl h_disabled.1
  · have h_opContract : KeccakfOpRowLocalContract opAir row :=
        row_local_contract opAir row h_enabled.2
    exact Or.inr <|
      pairing_gives_spec_row opAir permAir h_row h_enabled.1 h_opContract h_perm h_pairing

end Keccakf.Soundness
