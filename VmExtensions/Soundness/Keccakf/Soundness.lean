/-
  This file contains composition-level definitions and lemmas that pair the
  opcode-side (`KeccakfOpAir`) and permutation-side (`KeccakfPermAir`) AIRs
  via the shared keccak state bus.
-/
import VmExtensions.Airs.KeccakfOpAir
import VmExtensions.Airs.KeccakfOpAirViews
import VmExtensions.Airs.KeccakfPermAir
import VmExtensions.Airs.KeccakfPermAirViews
import VmExtensions.Constraints.KeccakfStateBus
import VmExtensions.Soundness.Keccakf.Wireup
import OpenvmFv.Fundamentals.BabyBear
import OpenvmFv.Fundamentals.Interaction

set_option autoImplicit false

open Keccakf.Interface
open BabyBear

namespace Keccakf.Soundness.Concrete

open Keccakf.Soundness
open KeccakfOpAir
open KeccakfOpAir.Views
open KeccakfOpAir.constraints
open KeccakfPermAir
open Keccakf.constraints
open KeccakfPermAir.constraints

variable {ExtF : Type} [Field ExtF]

/-! ## Column-native enabled-row list -/

/-- Enabled rows: row indices within bounds where `is_valid = 1`.
    Replaces the removed `validRows` field with a local column-native helper. -/
noncomputable def enabledRows
    (opAir : Valid_KeccakfOpAir FBB ExtF) : List ℕ :=
  (List.range (opAir.last_row + 1)).filter (fun row => decide (is_valid opAir row = 1))

lemma mem_enabledRows (opAir : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    row ∈ enabledRows opAir ↔ row ≤ opAir.last_row ∧ is_valid opAir row = 1 := by
  simp [enabledRows, List.mem_filter, List.mem_range, decide_eq_true_eq]
  omega

/-! ## Helper: payload-list representation of keccak state messages -/

noncomputable def msgPayloadList (msg : KeccakStateMsg) : List FBB :=
  (msgPayload msg).toList

/-! ## Per-AIR payload traces -/

noncomputable def opPayloadTrace
    (opAir : Valid_KeccakfOpAir FBB ExtF) : List (List FBB) :=
  (enabledRows opAir).flatMap fun row =>
    [msgPayloadList (preMsgOfColumns opAir row), msgPayloadList (postMsgOfColumns opAir row)]

noncomputable def permPayloadTrace
    (permAir : Valid_KeccakfPermAir FBB ExtF) : List (List FBB) :=
  permAir.exportedBlocks.flatMap fun block =>
    [(permPreEntry permAir block).payload.toList, (permPostEntry permAir block).payload.toList]

/-! ## Payload-list injectivity -/

lemma msgPayloadList_inj_of_timestamp_lt
    {msg₁ msg₂ : KeccakStateMsg}
    (h₁ : msg₁.timestamp < timestampBound)
    (h₂ : msg₂.timestamp < timestampBound)
    (h_payload : msgPayloadList msg₁ = msgPayloadList msg₂) :
    msg₁ = msg₂ := by
  apply msgPayload_inj_of_timestamp_lt h₁ h₂
  exact (Vector.toList_inj.mp h_payload)

/-! ## Payload-trace membership -/

lemma opPayloadTrace_pre_mem
    (opAir : Valid_KeccakfOpAir FBB ExtF) {row : ℕ}
    (h_row : row ≤ opAir.last_row) (h_valid : is_valid opAir row = 1) :
    msgPayloadList (preMsgOfColumns opAir row) ∈ opPayloadTrace opAir := by
  unfold opPayloadTrace
  apply List.mem_flatMap.2
  refine ⟨row, (mem_enabledRows opAir row).mpr ⟨h_row, h_valid⟩, ?_⟩
  simp [msgPayloadList]

lemma opPayloadTrace_post_mem
    (opAir : Valid_KeccakfOpAir FBB ExtF) {row : ℕ}
    (h_row : row ≤ opAir.last_row) (h_valid : is_valid opAir row = 1) :
    msgPayloadList (postMsgOfColumns opAir row) ∈ opPayloadTrace opAir := by
  unfold opPayloadTrace
  apply List.mem_flatMap.2
  refine ⟨row, (mem_enabledRows opAir row).mpr ⟨h_row, h_valid⟩, ?_⟩
  simp [msgPayloadList]

lemma mem_permPayloadTrace
    (permAir : Valid_KeccakfPermAir FBB ExtF) {payload : List FBB} :
    payload ∈ permPayloadTrace permAir ↔
      ∃ block ∈ permAir.exportedBlocks,
        payload = (permPreEntry permAir block).payload.toList ∨
          payload = (permPostEntry permAir block).payload.toList := by
  unfold permPayloadTrace
  constructor
  · intro h
    rcases List.mem_flatMap.mp h with ⟨block, h_block_mem, h_payload_mem⟩
    simp at h_payload_mem
    exact ⟨block, h_block_mem, h_payload_mem⟩
  · rintro ⟨block, h_block_mem, h_eq | h_eq⟩
    · apply List.mem_flatMap.2
      refine ⟨block, h_block_mem, ?_⟩
      simp [h_eq]
    · apply List.mem_flatMap.2
      refine ⟨block, h_block_mem, ?_⟩
      simp [h_eq]

/-! ## Serialisation helpers -/

lemma serialiseToList_flatMap {α β : Type} [Interaction.BusEntry FBB α]
    (xs : List β) (f : β → List α) :
    serialiseToList (xs.flatMap f) = xs.flatMap (fun x => serialiseToList (f x)) := by
  induction xs with
  | nil =>
      simp [serialiseToList]
  | cons x xs ih =>
      simp [serialiseToList]

/-! ## Per-row / per-block bus-trace decomposition -/

lemma opStateBusTrace_eq_flatMap_row
    (opAir : Valid_KeccakfOpAir FBB ExtF) (rows : List ℕ) :
    opStateBusTrace opAir rows = rows.flatMap (fun row => opStateBusRow opAir row) := by
  unfold opStateBusTrace opStateBusEntryTrace
  exact serialiseToList_flatMap rows (fun row => opStateBusEntries opAir row)

lemma permStateBusTrace_eq_flatMap_block
    (permAir : Valid_KeccakfPermAir FBB ExtF) (blocks : List ℕ) :
    permStateBusTrace permAir blocks = blocks.flatMap (fun block => permStateBusBlock permAir block) := by
  unfold permStateBusTrace permStateBusEntryTrace
  exact serialiseToList_flatMap blocks (fun block => permStateBusEntries permAir block)

/-! ## Send/receive filtering per row/block -/

lemma opStateBusRow_recvs_nil
    (opAir : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List.filterMap (fun x => if x.1 = -1 then some x.2 else none)
      (opStateBusRow opAir row) = [] := by
  simp [opStateBusRow, serialiseToList, opStateBusEntries, opPreEntry, opPostEntry,
    msgToAssertEntry]

lemma opStateBusRow_sends
    (opAir : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List.filterMap (fun x => if x.1 = 1 then some x.2 else none)
      (opStateBusRow opAir row) =
      [msgPayloadList (preMsgOfColumns opAir row), msgPayloadList (postMsgOfColumns opAir row)] := by
  simp [opStateBusRow, serialiseToList, opStateBusEntries, opPreEntry, opPostEntry,
    msgToAssertEntry, msgPayloadList]

lemma permStateBusBlock_sends_nil
    (permAir : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
    List.filterMap (fun x => if x.1 = 1 then some x.2 else none)
      (permStateBusBlock permAir block) = [] := by
  simp [permStateBusBlock, serialiseToList, permStateBusEntries, permPreEntry, permPostEntry]

lemma permStateBusBlock_recvs
    (permAir : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
    List.filterMap (fun x => if x.1 = -1 then some x.2 else none)
      (permStateBusBlock permAir block) =
      [(permPreEntry permAir block).payload.toList, (permPostEntry permAir block).payload.toList] := by
  simp [permStateBusBlock, serialiseToList, permStateBusEntries, permPreEntry, permPostEntry]

/-! ## Whole-trace send/receive aggregation -/

lemma opStateBusTrace_recvs_nil_on
    (opAir : Valid_KeccakfOpAir FBB ExtF) (rows : List ℕ) :
    List.filterMap (fun x => if x.1 = -1 then some x.2 else none)
      (opStateBusTrace opAir rows) = [] := by
  rw [opStateBusTrace_eq_flatMap_row]
  induction rows with
  | nil =>
      simp
  | cons row rows ih =>
      rw [List.flatMap_cons, List.filterMap_append, opStateBusRow_recvs_nil, ih]
      simp

lemma permStateBusTrace_sends_nil_on
    (permAir : Valid_KeccakfPermAir FBB ExtF) (blocks : List ℕ) :
    List.filterMap (fun x => if x.1 = 1 then some x.2 else none)
      (permStateBusTrace permAir blocks) = [] := by
  rw [permStateBusTrace_eq_flatMap_block]
  induction blocks with
  | nil =>
      simp
  | cons block blocks ih =>
      rw [List.flatMap_cons, List.filterMap_append, permStateBusBlock_sends_nil, ih]
      simp

lemma opStateBusTrace_sends_eq_payloadTrace_on
    (opAir : Valid_KeccakfOpAir FBB ExtF) (rows : List ℕ) :
    List.filterMap (fun x => if x.1 = 1 then some x.2 else none)
      (opStateBusTrace opAir rows) =
      rows.flatMap (fun row =>
        [msgPayloadList (preMsgOfColumns opAir row), msgPayloadList (postMsgOfColumns opAir row)]) := by
  rw [opStateBusTrace_eq_flatMap_row]
  induction rows with
  | nil =>
      simp
  | cons row rows ih =>
      rw [List.flatMap_cons, List.filterMap_append, opStateBusRow_sends, ih]
      simp

lemma permStateBusTrace_recvs_eq_payloadTrace_on
    (permAir : Valid_KeccakfPermAir FBB ExtF) (blocks : List ℕ) :
    List.filterMap (fun x => if x.1 = -1 then some x.2 else none)
      (permStateBusTrace permAir blocks) =
      blocks.flatMap (fun block =>
        [(permPreEntry permAir block).payload.toList, (permPostEntry permAir block).payload.toList]) := by
  rw [permStateBusTrace_eq_flatMap_block]
  induction blocks with
  | nil =>
      simp
  | cons block blocks ih =>
      rw [List.flatMap_cons, List.filterMap_append, permStateBusBlock_recvs, ih]
      simp

-- Specialized to the column-native enabled-row list.
lemma opStateBusTrace_recvs_nil
    (opAir : Valid_KeccakfOpAir FBB ExtF) :
    List.filterMap (fun x => if x.1 = -1 then some x.2 else none)
      (opStateBusTrace opAir (enabledRows opAir)) = [] :=
  opStateBusTrace_recvs_nil_on opAir (enabledRows opAir)

lemma permStateBusTrace_sends_nil
    (permAir : Valid_KeccakfPermAir FBB ExtF) :
    List.filterMap (fun x => if x.1 = 1 then some x.2 else none)
      (permStateBusTrace permAir permAir.exportedBlocks) = [] :=
  permStateBusTrace_sends_nil_on permAir permAir.exportedBlocks

lemma opStateBusTrace_sends_eq_payloadTrace
    (opAir : Valid_KeccakfOpAir FBB ExtF) :
    List.filterMap (fun x => if x.1 = 1 then some x.2 else none)
      (opStateBusTrace opAir (enabledRows opAir)) = opPayloadTrace opAir := by
  simpa [opPayloadTrace] using opStateBusTrace_sends_eq_payloadTrace_on opAir (enabledRows opAir)

lemma permStateBusTrace_recvs_eq_payloadTrace
    (permAir : Valid_KeccakfPermAir FBB ExtF) :
    List.filterMap (fun x => if x.1 = -1 then some x.2 else none)
      (permStateBusTrace permAir permAir.exportedBlocks) = permPayloadTrace permAir := by
  simpa [permPayloadTrace] using
    permStateBusTrace_recvs_eq_payloadTrace_on permAir permAir.exportedBlocks

end Keccakf.Soundness.Concrete
