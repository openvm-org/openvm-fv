/-
  Bus-derived facts for KeccakfPermAir soundness (FBB-specialized).

  Bridges raw bus assumptions (wf_propertiesToAssumePerPermBlock) to usable
  per-block proof terms, and proves the full BlockBusMatch by bridging the
  raw-entry layer to the message-view layer via UInt16 roundtrip.

  The 2-element bus entry list [permPreEntry, permPostEntry] is extracted
  via direct And.left/And.right elimination (plan §11 choice).
-/
import VmExtensions.Soundness.KeccakfPermAir.RowProperties
import VmExtensions.Airs.KeccakfPermAirViews
import OpenvmFv.Fundamentals.BabyBear
import OpenvmFv.Fundamentals.Interaction

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfPermAir.Soundness.BusFacts

open KeccakfPermAir.constraints
open KeccakfPermAir
open Keccakf.Interface
open Keccakf.constraints
open BabyBear

variable {ExtF : Type} [Field ExtF]

/-! ## FBB / UInt16 Roundtrip Helpers -/

-- For any FBB value v, casting v.val back to FBB gives v.
private lemma fbb_natCast_val_eq_self (v : FBB) : (v.val : FBB) = v := by
  ext
  exact Nat.mod_eq_of_lt v.isLt

-- UInt16.ofNat n followed by .toNat recovers n when n < 2^16.
private lemma uint16_ofNat_toNat_of_lt {n : ℕ} (h : n < 2 ^ 16) :
    (UInt16.ofNat n).toNat = n := by
  simp only [UInt16.ofNat, UInt16.toNat, BitVec.toNat_ofNat]
  omega

-- Combined roundtrip: for an FBB value v with v.val < 2^16,
-- applying UInt16.ofNat then .toNat then FBB cast recovers v.
-- This is the key lemma bridging raw column values to message-view state limbs.
private lemma fbb_uint16_roundtrip (v : FBB) (hv : v.val < 2 ^ 16) :
    ((UInt16.ofNat v.val).toNat : FBB) = v := by
  rw [uint16_ofNat_toNat_of_lt hv]
  exact fbb_natCast_val_eq_self v

/-! ## Extracting wf_properties from the 2-element bus entry list

wf_propertiesToAssumePerPermBlock unfolds to List.Forall over
[permPreEntry, permPostEntry]. Both have multiplicity = -1, so
wf_assume_cond holds trivially and we get wf_properties for each.
-/

-- Extract wf_properties for the pre-entry. The assume condition
-- (multiplicity = -1) holds definitionally for permPreEntry.
private lemma wf_pre_of_wfPerPermBlock
    {air : Valid_KeccakfPermAir FBB ExtF} {block : ℕ}
    (h_wf : wf_propertiesToAssumePerPermBlock air block) :
    ((permPreEntry air block).payload[0] = 0 ∨
     (permPreEntry air block).payload[0] = 1) ∧
    (∀ i : Fin 100,
     ((permPreEntry air block).payload[i.val + 2]).val < 2 ^ 16) := by
  simp only [wf_propertiesToAssumePerPermBlock, propertiesToAssume,
    permStateBusEntries, List.map_cons, List.map_nil, List.forall_cons,
    List.Forall, id] at h_wf
  -- h_wf : (assume pre) ∧ (assume post) — True was simplified away by simp
  exact h_wf.1 (by simp [permPreEntry])

-- Extract wf_properties for the post-entry.
private lemma wf_post_of_wfPerPermBlock
    {air : Valid_KeccakfPermAir FBB ExtF} {block : ℕ}
    (h_wf : wf_propertiesToAssumePerPermBlock air block) :
    ((permPostEntry air block).payload[0] = 0 ∨
     (permPostEntry air block).payload[0] = 1) ∧
    (∀ i : Fin 100,
     ((permPostEntry air block).payload[i.val + 2]).val < 2 ^ 16) := by
  simp only [wf_propertiesToAssumePerPermBlock, propertiesToAssume,
    permStateBusEntries, List.map_cons, List.map_nil, List.forall_cons,
    List.Forall, id] at h_wf
  -- h_wf.2 is (assume post) — a function (wf_assume_cond → wf_properties)
  exact h_wf.2 (by simp [permPostEntry])

/-! ## Per-block u16 Range Lemmas -/

-- Each preimage column value at the export row has val < 2^16.
-- Derived from wf_properties on the raw pre-entry: payload[i+2] maps to
-- preimage air i (export row), and wf_properties gives val < 2^16.
theorem preimage_u16_of_wfPerPermBlock
    {air : Valid_KeccakfPermAir FBB ExtF} {block : ℕ}
    (h_wf : wf_propertiesToAssumePerPermBlock air block) :
    ∀ i, i < 100 →
      (preimage air i (air.blockExportRow block)).val < 2 ^ 16 := by
  intro i hi
  have ⟨_, h_limbs⟩ := wf_pre_of_wfPerPermBlock h_wf
  have h := h_limbs ⟨i, hi⟩
  simp only [permPreEntry, Vector.getElem_ofFn] at h
  simpa using h

-- Each output column value at the export row has val < 2^16.
-- Output columns: a_ppp_00_limb for indices 0-3, a_prime_prime for indices 4-99.
-- Derived from wf_properties on the raw post-entry.
theorem output_u16_of_wfPerPermBlock
    {air : Valid_KeccakfPermAir FBB ExtF} {block : ℕ}
    (h_wf : wf_propertiesToAssumePerPermBlock air block) :
    ∀ i, i < 100 →
      (if i < 4
       then (a_ppp_00_limb air i (air.blockExportRow block)).val
       else (a_prime_prime air i (air.blockExportRow block)).val) < 2 ^ 16 := by
  intro i hi
  have ⟨_, h_limbs⟩ := wf_post_of_wfPerPermBlock h_wf
  have h := h_limbs ⟨i, hi⟩
  simp only [permPostEntry, Vector.getElem_ofFn] at h
  -- Simplify the nested ifs (i+2 ≠ 0, i+2 ≠ 1, i+2-2 = i)
  have h0 : ¬ (i + 2 = 0) := by omega
  have h1 : ¬ (i + 2 = 1) := by omega
  simp only [h0, h1, ↓reduceIte, show i + 2 - 2 = i from by omega] at h
  by_cases h4 : i < 4
  · simp only [h4, ↓reduceIte] at h ⊢; exact h
  · simp only [show ¬(i < 4) from h4, ↓reduceIte] at h ⊢; exact h

/-! ## BlockBusMatch Proof

Bridges raw-column bus entries to column-native message views.
The proof uses:
1. u16 lemmas in this file → raw column values have val < 2^16
2. UInt16 roundtrip under < 2^16 → msgPayload matches raw bus payload
3. export_flag = 1
-/

-- Vector equality between msgPayload of blockPreMsg and permPreEntry's payload.
-- The two vectors have the same structure; the roundtrip makes state limbs match.
set_option maxHeartbeats 800000 in
lemma msgPayload_blockPreMsg_eq_permPreEntry
    (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ)
    (h_u16 : ∀ i, i < 100 →
      (preimage air i (air.blockExportRow block)).val < 2 ^ 16) :
    msgPayload (blockPreMsg air block) = (permPreEntry air block).payload := by
  refine Vector.ext (fun i hi => ?_)
  simp only [msgPayload, blockPreMsg, permPreEntry, flagField,
    Vector.getElem_ofFn, Vector.get_ofFn]
  by_cases h0 : i = 0
  · subst h0; simp
  · by_cases h1 : i = 1
    · subst h1; simp
    · -- i ≥ 2: reduce dite/ite ifs, then apply the UInt16 roundtrip
      simp only [dif_neg h0, dif_neg h1, if_neg h0, if_neg h1]
      exact fbb_uint16_roundtrip _ (h_u16 (i - 2) (by omega))

-- Vector equality between msgPayload of blockPostMsg and permPostEntry's payload.
set_option maxHeartbeats 800000 in
lemma msgPayload_blockPostMsg_eq_permPostEntry
    (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ)
    (h_u16 : ∀ i, i < 100 →
      (if i < 4
       then (a_ppp_00_limb air i (air.blockExportRow block)).val
       else (a_prime_prime air i (air.blockExportRow block)).val) < 2 ^ 16) :
    msgPayload (blockPostMsg air block) = (permPostEntry air block).payload := by
  refine Vector.ext (fun i hi => ?_)
  simp only [msgPayload, blockPostMsg, permPostEntry, flagField,
    Vector.getElem_ofFn, Vector.get_ofFn]
  by_cases h0 : i = 0
  · subst h0; simp
  · by_cases h1 : i = 1
    · subst h1; simp
    · have h_idx : i - 2 < 100 := by omega
      simp only [dif_neg h0, dif_neg h1, if_neg h0, if_neg h1]
      by_cases h4 : i - 2 < 4
      · have h_bound := h_u16 (i - 2) h_idx
        simp only [if_pos h4] at h_bound ⊢
        exact fbb_uint16_roundtrip _ h_bound
      · have h_bound := h_u16 (i - 2) h_idx
        simp only [if_neg h4] at h_bound ⊢
        exact fbb_uint16_roundtrip _ h_bound

-- busPrePayload as a literal list equals (permPreEntry.payload).toList.
-- Both produce the same 102-element list of column values.
set_option maxRecDepth 1024 in
set_option maxHeartbeats 1600000 in
private lemma busPrePayload_eq_permPreEntry_toList
    (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
    busPrePayload air (air.blockExportRow block) =
      ((permPreEntry air block).payload).toList := by
  simp only [busPrePayload, permPreEntry, Vector.toList_ofFn, List.ofFn]
  rfl

-- busPostPayload as a literal list equals (permPostEntry.payload).toList.
set_option maxRecDepth 1024 in
set_option maxHeartbeats 1600000 in
private lemma busPostPayload_eq_permPostEntry_toList
    (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
    busPostPayload air (air.blockExportRow block) =
      ((permPostEntry air block).payload).toList := by
  simp only [busPostPayload, permPostEntry, Vector.toList_ofFn, List.ofFn]
  rfl

-- Helper: busPrePayload matches msgPayload of blockPreMsg when u16 bounds hold.
-- Combines the vector roundtrip equality with the definitional list equality.
private lemma pre_payload_eq_of_u16
    (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ)
    (h_u16 : ∀ i, i < 100 →
      (preimage air i (air.blockExportRow block)).val < 2 ^ 16) :
    busPrePayload air (air.blockExportRow block) =
      (msgPayload (blockPreMsg air block)).toList := by
  rw [msgPayload_blockPreMsg_eq_permPreEntry air block h_u16]
  exact busPrePayload_eq_permPreEntry_toList air block

-- Helper: busPostPayload matches msgPayload of blockPostMsg when u16 bounds hold.
private lemma post_payload_eq_of_u16
    (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ)
    (h_u16 : ∀ i, i < 100 →
      (if i < 4
       then (a_ppp_00_limb air i (air.blockExportRow block)).val
       else (a_prime_prime air i (air.blockExportRow block)).val) < 2 ^ 16) :
    busPostPayload air (air.blockExportRow block) =
      (msgPayload (blockPostMsg air block)).toList := by
  rw [msgPayload_blockPostMsg_eq_permPostEntry air block h_u16]
  exact busPostPayload_eq_permPostEntry_toList air block

-- The full bus-match bridge: raw bus entries match serialized message views
-- at export rows, using explicit export_flag = 1 and bus WF u16 bounds.
theorem blockBusMatch
    {air : Valid_KeccakfPermAir FBB ExtF} {block : ℕ}
    (h_wf : wf_propertiesToAssumePerPermBlock air block)
    (h_flag : export_flag air (air.blockExportRow block) = 1) :
    BlockBusMatch air block where
  export_flag_eq := h_flag
  pre_payload_eq :=
    pre_payload_eq_of_u16 air block (preimage_u16_of_wfPerPermBlock h_wf)
  post_payload_eq :=
    post_payload_eq_of_u16 air block (output_u16_of_wfPerPermBlock h_wf)

-- Raw bus_7Bus_row at an export row equals permStateBusBlock (serialized typed entries).
-- Bridges the constraint-level bus row to the typed bus-entry layer.
-- Multiplicities: -(export_flag) = -1 from h_export. Payloads: definitional via
-- busPrePayload_eq_permPreEntry_toList / busPostPayload_eq_permPostEntry_toList.
set_option maxRecDepth 1024 in
set_option maxHeartbeats 1600000 in
theorem bus_7Bus_row_eq_permStateBusBlock
    (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ)
    (h_export : export_flag air (air.blockExportRow block) = 1) :
    bus_7Bus_row air (air.blockExportRow block) = permStateBusBlock air block := by
  rw [bus_7Bus_row_eq_payloads]
  simp only [permStateBusBlock, permStateBusEntries, serialiseToList, List.map,
    Interaction.BusEntry.serialiseToList]
  rw [busPrePayload_eq_permPreEntry_toList, busPostPayload_eq_permPostEntry_toList]
  simp [permPreEntry, permPostEntry, h_export]

end KeccakfPermAir.Soundness.BusFacts
