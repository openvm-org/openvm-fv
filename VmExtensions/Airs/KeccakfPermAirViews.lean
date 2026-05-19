import VmExtensions.Constraints.KeccakfPermAirBus
import VmExtensions.Constraints.KeccakfStateBus
import OpenvmFv.Fundamentals.BabyBear

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfPermAir.constraints

open Keccakf.Interface
open Keccakf.constraints
open KeccakfPermAir
open BabyBear

/-! ## Section A: Bus payload extraction from columns

`busPrePayload` and `busPostPayload` extract the payload lists (without multiplicity)
from `keccakStateBus_pre_entry` and `keccakStateBus_post_entry` respectively.
-/

section payload_defs
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  /-- Pre-state bus payload: [0, timestamp, preimage[0], ..., preimage[99]] -/
  def busPrePayload (c : C F ExtF) (row : ℕ) : List F :=
    [0,
     timestamp c row,
     preimage c 0 row, preimage c 1 row, preimage c 2 row, preimage c 3 row,
     preimage c 4 row, preimage c 5 row, preimage c 6 row, preimage c 7 row,
     preimage c 8 row, preimage c 9 row, preimage c 10 row, preimage c 11 row,
     preimage c 12 row, preimage c 13 row, preimage c 14 row, preimage c 15 row,
     preimage c 16 row, preimage c 17 row, preimage c 18 row, preimage c 19 row,
     preimage c 20 row, preimage c 21 row, preimage c 22 row, preimage c 23 row,
     preimage c 24 row, preimage c 25 row, preimage c 26 row, preimage c 27 row,
     preimage c 28 row, preimage c 29 row, preimage c 30 row, preimage c 31 row,
     preimage c 32 row, preimage c 33 row, preimage c 34 row, preimage c 35 row,
     preimage c 36 row, preimage c 37 row, preimage c 38 row, preimage c 39 row,
     preimage c 40 row, preimage c 41 row, preimage c 42 row, preimage c 43 row,
     preimage c 44 row, preimage c 45 row, preimage c 46 row, preimage c 47 row,
     preimage c 48 row, preimage c 49 row, preimage c 50 row, preimage c 51 row,
     preimage c 52 row, preimage c 53 row, preimage c 54 row, preimage c 55 row,
     preimage c 56 row, preimage c 57 row, preimage c 58 row, preimage c 59 row,
     preimage c 60 row, preimage c 61 row, preimage c 62 row, preimage c 63 row,
     preimage c 64 row, preimage c 65 row, preimage c 66 row, preimage c 67 row,
     preimage c 68 row, preimage c 69 row, preimage c 70 row, preimage c 71 row,
     preimage c 72 row, preimage c 73 row, preimage c 74 row, preimage c 75 row,
     preimage c 76 row, preimage c 77 row, preimage c 78 row, preimage c 79 row,
     preimage c 80 row, preimage c 81 row, preimage c 82 row, preimage c 83 row,
     preimage c 84 row, preimage c 85 row, preimage c 86 row, preimage c 87 row,
     preimage c 88 row, preimage c 89 row, preimage c 90 row, preimage c 91 row,
     preimage c 92 row, preimage c 93 row, preimage c 94 row, preimage c 95 row,
     preimage c 96 row, preimage c 97 row, preimage c 98 row, preimage c 99 row]

  /-- Post-state bus payload: [1, timestamp, a_ppp_00_limb[0..3], a_prime_prime[4..99]] -/
  def busPostPayload (c : C F ExtF) (row : ℕ) : List F :=
    [1,
     timestamp c row,
     a_ppp_00_limb c 0 row, a_ppp_00_limb c 1 row,
     a_ppp_00_limb c 2 row, a_ppp_00_limb c 3 row,
     a_prime_prime c 4 row, a_prime_prime c 5 row,
     a_prime_prime c 6 row, a_prime_prime c 7 row,
     a_prime_prime c 8 row, a_prime_prime c 9 row,
     a_prime_prime c 10 row, a_prime_prime c 11 row,
     a_prime_prime c 12 row, a_prime_prime c 13 row,
     a_prime_prime c 14 row, a_prime_prime c 15 row,
     a_prime_prime c 16 row, a_prime_prime c 17 row,
     a_prime_prime c 18 row, a_prime_prime c 19 row,
     a_prime_prime c 20 row, a_prime_prime c 21 row,
     a_prime_prime c 22 row, a_prime_prime c 23 row,
     a_prime_prime c 24 row, a_prime_prime c 25 row,
     a_prime_prime c 26 row, a_prime_prime c 27 row,
     a_prime_prime c 28 row, a_prime_prime c 29 row,
     a_prime_prime c 30 row, a_prime_prime c 31 row,
     a_prime_prime c 32 row, a_prime_prime c 33 row,
     a_prime_prime c 34 row, a_prime_prime c 35 row,
     a_prime_prime c 36 row, a_prime_prime c 37 row,
     a_prime_prime c 38 row, a_prime_prime c 39 row,
     a_prime_prime c 40 row, a_prime_prime c 41 row,
     a_prime_prime c 42 row, a_prime_prime c 43 row,
     a_prime_prime c 44 row, a_prime_prime c 45 row,
     a_prime_prime c 46 row, a_prime_prime c 47 row,
     a_prime_prime c 48 row, a_prime_prime c 49 row,
     a_prime_prime c 50 row, a_prime_prime c 51 row,
     a_prime_prime c 52 row, a_prime_prime c 53 row,
     a_prime_prime c 54 row, a_prime_prime c 55 row,
     a_prime_prime c 56 row, a_prime_prime c 57 row,
     a_prime_prime c 58 row, a_prime_prime c 59 row,
     a_prime_prime c 60 row, a_prime_prime c 61 row,
     a_prime_prime c 62 row, a_prime_prime c 63 row,
     a_prime_prime c 64 row, a_prime_prime c 65 row,
     a_prime_prime c 66 row, a_prime_prime c 67 row,
     a_prime_prime c 68 row, a_prime_prime c 69 row,
     a_prime_prime c 70 row, a_prime_prime c 71 row,
     a_prime_prime c 72 row, a_prime_prime c 73 row,
     a_prime_prime c 74 row, a_prime_prime c 75 row,
     a_prime_prime c 76 row, a_prime_prime c 77 row,
     a_prime_prime c 78 row, a_prime_prime c 79 row,
     a_prime_prime c 80 row, a_prime_prime c 81 row,
     a_prime_prime c 82 row, a_prime_prime c 83 row,
     a_prime_prime c 84 row, a_prime_prime c 85 row,
     a_prime_prime c 86 row, a_prime_prime c 87 row,
     a_prime_prime c 88 row, a_prime_prime c 89 row,
     a_prime_prime c 90 row, a_prime_prime c 91 row,
     a_prime_prime c 92 row, a_prime_prime c 93 row,
     a_prime_prime c 94 row, a_prime_prime c 95 row,
     a_prime_prime c 96 row, a_prime_prime c 97 row,
     a_prime_prime c 98 row, a_prime_prime c 99 row]

end payload_defs

/-! ## Section B: Structural decomposition

`bus_7Bus_row` decomposes into multiplicity-payload pairs using the payload helpers.
-/

section structural
  variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

  theorem bus_7Bus_row_eq_payloads (c : C F ExtF) (row : ℕ) :
      bus_7Bus_row c row =
        [(-(export_flag c row), busPrePayload c row),
         (-(export_flag c row), busPostPayload c row)] := by
    rfl

end structural

/-! ## Section C: Column-native message views

`blockPreMsg` and `blockPostMsg` construct `KeccakStateMsg` objects directly from
export-row column values. These are the message-level objects that
`KeccakfPermBlockContract` and `BusKeccakPermutes` consume.

State limbs use `UInt16.ofNat` of the raw column value — lossless when the raw
value satisfies `val < 2^16` (proved in BusFacts via bus wf_properties).
-/

section message_views
  variable {ExtF : Type} [Field ExtF]

  -- Column-native pre-state message at an exported block's export row.
  -- isPost is hardcoded false; timestamp is the Nat value of the timestamp column;
  -- state limbs are UInt16.ofNat of the preimage columns.
  noncomputable def blockPreMsg
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) : KeccakStateMsg :=
    { isPost := false
    , timestamp := (timestamp air (air.blockExportRow block)).val
    , state := Vector.ofFn (fun (i : Fin 100) =>
        UInt16.ofNat (preimage air i.val (air.blockExportRow block)).val) }

  -- Column-native post-state message at an exported block's export row.
  -- isPost is hardcoded true; timestamp is the same column as pre-state (definitional
  -- same_timestamp); state limbs are UInt16.ofNat of the output columns
  -- (a_ppp_00_limb for indices 0-3, a_prime_prime for indices 4-99).
  noncomputable def blockPostMsg
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) : KeccakStateMsg :=
    { isPost := true
    , timestamp := (timestamp air (air.blockExportRow block)).val
    , state := Vector.ofFn (fun (i : Fin 100) =>
        UInt16.ofNat (if i.val < 4
          then (a_ppp_00_limb air i.val (air.blockExportRow block)).val
          else (a_prime_prime air i.val (air.blockExportRow block)).val)) }

end message_views

/-! ## Section D: Bridge predicates

These predicates connect column values at export rows to the column-native
message views, bridging the raw bus payload layer to the message-view layer.
-/

section bridge
  variable {ExtF : Type} [Field ExtF]

  structure BlockBusMatch (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) : Prop where
    export_flag_eq : export_flag air (air.blockExportRow block) = 1
    pre_payload_eq :
      busPrePayload air (air.blockExportRow block) =
        (msgPayload (blockPreMsg air block)).toList
    post_payload_eq :
      busPostPayload air (air.blockExportRow block) =
        (msgPayload (blockPostMsg air block)).toList

  /-- Non-export rows have zero export flag. -/
  def NonExportRowsZero (air : Valid_KeccakfPermAir FBB ExtF) : Prop :=
    ∀ row, row ≤ air.last_row →
      (∀ block, air.isExportedBlock block → air.blockExportRow block ≠ row) →
      export_flag air row = 0

  /-- All exported blocks satisfy the bus match predicate. -/
  def AllBlocksBusMatch (air : Valid_KeccakfPermAir FBB ExtF) : Prop :=
    ∀ block, air.isExportedBlock block → BlockBusMatch air block

end bridge

/-! ## Section E: Permutation-side Typed Keccak State-Bus Entries (raw-column)

These definitions construct bus entries from raw column accessors (NOT from
message views). Their payloads contain raw FBB column
values without UInt16.ofNat truncation. Bus WF (wf_propertiesToAssumePerPermBlock)
proves val < 2^16 on these raw values — the bridge to message views is in BusFacts.
-/

section perm_bus_entries
  variable {ExtF : Type} [Field ExtF]

  -- Raw-column pre-state bus entry: multiplicity -1, payload is [0, timestamp, preimage[0..99]].
  -- Constructed from raw column accessors, NOT from blockPreMsg.
  noncomputable def permPreEntry
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
      Interaction.KeccakfStateBusEntry FBB where
    multiplicity := -1
    payload := Vector.ofFn fun (i : Fin 102) =>
      if i.val = 0 then (0 : FBB)
      else if i.val = 1 then timestamp air (air.blockExportRow block)
      else preimage air (i.val - 2) (air.blockExportRow block)

  -- Raw-column post-state bus entry: multiplicity -1, payload is
  -- [1, timestamp, a_ppp_00_limb[0..3], a_prime_prime[4..99]].
  -- Constructed from raw column accessors, NOT from blockPostMsg.
  noncomputable def permPostEntry
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
      Interaction.KeccakfStateBusEntry FBB where
    multiplicity := -1
    payload := Vector.ofFn fun (i : Fin 102) =>
      if i.val = 0 then (1 : FBB)
      else if i.val = 1 then timestamp air (air.blockExportRow block)
      else if i.val - 2 < 4 then a_ppp_00_limb air (i.val - 2) (air.blockExportRow block)
      else a_prime_prime air (i.val - 2) (air.blockExportRow block)

  @[simp]
  noncomputable def permStateBusEntries
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
      List (Interaction.KeccakfStateBusEntry FBB) :=
    [permPreEntry air block, permPostEntry air block]

  @[simp]
  theorem permStateBusEntries_length
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
      (permStateBusEntries air block).length = 2 := by
    simp [permStateBusEntries]

  @[simp]
  noncomputable def permStateBusBlock
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
      List (FBB × List FBB) :=
    serialiseToList (permStateBusEntries air block)

  @[simp]
  noncomputable def axiomsPerPermBlock
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
      Prop :=
    axioms (permStateBusEntries air block)

  @[simp]
  noncomputable def wf_propertiesToAssumePerPermBlock
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) : Prop :=
    propertiesToAssume (permStateBusEntries air block)

end perm_bus_entries

/-! ## Section F: Aggregated Permutation-side Keccak State-Bus Traces -/

section perm_bus_traces
  variable {ExtF : Type} [Field ExtF]

  @[simp]
  noncomputable def permStateBusEntryTrace
      (air : Valid_KeccakfPermAir FBB ExtF) (blocks : List ℕ) :
      List (Interaction.KeccakfStateBusEntry FBB) :=
    blocks.flatMap (fun block => permStateBusEntries air block)

  @[simp]
  noncomputable def permStateBusTrace
      (air : Valid_KeccakfPermAir FBB ExtF) (blocks : List ℕ) :
      List (FBB × List FBB) :=
    serialiseToList (permStateBusEntryTrace air blocks)

  @[simp]
  noncomputable def axiomsOnPermBlocks
      (air : Valid_KeccakfPermAir FBB ExtF) (blocks : List ℕ) : Prop :=
    axioms (permStateBusEntryTrace air blocks)

  @[simp]
  noncomputable def wf_propertiesToAssumeOnPermBlocks
      (air : Valid_KeccakfPermAir FBB ExtF) (blocks : List ℕ) : Prop :=
    propertiesToAssume (permStateBusEntryTrace air blocks)

end perm_bus_traces

/-! ## Section G: Key consequence lemmas

Under the bridge predicates, raw bus rows equal typed bus blocks,
and non-export rows produce zero-multiplicity entries.
-/

section consequences
  variable {ExtF : Type} [Field ExtF]

  /-- Non-export rows produce zero-multiplicity bus entries. -/
  theorem bus_7Bus_row_zero_of_not_export
      (air : Valid_KeccakfPermAir FBB ExtF) (row : ℕ)
      (h_zero : export_flag air row = 0) :
      bus_7Bus_row air row = [(0, busPrePayload air row), (0, busPostPayload air row)] := by
    rw [bus_7Bus_row_eq_payloads, h_zero]
    simp

end consequences

/-! ## Section H: Row-native message views

`rowPreMsg` and `rowPostMsg` are identical to `blockPreMsg`/`blockPostMsg` but
take a raw `row : ℕ` instead of a block index.  The block-indexed versions are
definitionally equal to the row-indexed versions at `air.blockExportRow block`.
-/

section row_message_views
  variable {ExtF : Type} [Field ExtF]

  -- Row-native pre-state message: reads columns at `row` directly.
  noncomputable def rowPreMsg (air : Valid_KeccakfPermAir FBB ExtF) (row : ℕ) :
      KeccakStateMsg :=
    { isPost := false
    , timestamp := (timestamp air row).val
    , state := Vector.ofFn (fun (i : Fin 100) =>
        UInt16.ofNat (preimage air i.val row).val) }

  -- Row-native post-state message: reads output columns at `row` directly.
  noncomputable def rowPostMsg (air : Valid_KeccakfPermAir FBB ExtF) (row : ℕ) :
      KeccakStateMsg :=
    { isPost := true
    , timestamp := (timestamp air row).val
    , state := Vector.ofFn (fun (i : Fin 100) =>
        UInt16.ofNat (if i.val < 4
          then (a_ppp_00_limb air i.val row).val
          else (a_prime_prime air i.val row).val)) }

  -- Bridge: blockPreMsg is rowPreMsg at the block's export row (definitional)
  theorem blockPreMsg_eq_rowPreMsg (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
      blockPreMsg air block = rowPreMsg air (air.blockExportRow block) :=
    rfl

  -- Bridge: blockPostMsg is rowPostMsg at the block's export row (definitional)
  theorem blockPostMsg_eq_rowPostMsg (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
      blockPostMsg air block = rowPostMsg air (air.blockExportRow block) :=
    rfl

end row_message_views

/-! ## Section I: Row-native typed Keccak State-Bus entries

`permPreRowEntry` and `permPostRowEntry` are identical to `permPreEntry`/`permPostEntry`
but take a raw `row : ℕ` instead of a block index.
-/

section row_bus_entries
  variable {ExtF : Type} [Field ExtF]

  -- Row-native pre-state bus entry: multiplicity -1, payload [0, timestamp, preimage[0..99]].
  noncomputable def permPreRowEntry
      (air : Valid_KeccakfPermAir FBB ExtF) (row : ℕ) :
      Interaction.KeccakfStateBusEntry FBB where
    multiplicity := -1
    payload := Vector.ofFn fun (i : Fin 102) =>
      if i.val = 0 then (0 : FBB)
      else if i.val = 1 then timestamp air row
      else preimage air (i.val - 2) row

  -- Row-native post-state bus entry: multiplicity -1,
  -- payload [1, timestamp, a_ppp_00_limb[0..3], a_prime_prime[4..99]].
  noncomputable def permPostRowEntry
      (air : Valid_KeccakfPermAir FBB ExtF) (row : ℕ) :
      Interaction.KeccakfStateBusEntry FBB where
    multiplicity := -1
    payload := Vector.ofFn fun (i : Fin 102) =>
      if i.val = 0 then (1 : FBB)
      else if i.val = 1 then timestamp air row
      else if i.val - 2 < 4 then a_ppp_00_limb air (i.val - 2) row
      else a_prime_prime air (i.val - 2) row

  -- Bridge: block-indexed pre-entry = row-indexed pre-entry at export row (definitional)
  theorem permPreEntry_eq_permPreRowEntry
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
      permPreEntry air block = permPreRowEntry air (air.blockExportRow block) :=
    rfl

  -- Bridge: block-indexed post-entry = row-indexed post-entry at export row (definitional)
  theorem permPostEntry_eq_permPostRowEntry
      (air : Valid_KeccakfPermAir FBB ExtF) (block : ℕ) :
      permPostEntry air block = permPostRowEntry air (air.blockExportRow block) :=
    rfl

end row_bus_entries

/-! ## Section J: Row-native payload-to-message bridges

Under u16 bounds on column values, `msgPayload (rowPreMsg air row)` equals
`(permPreRowEntry air row).payload` (and likewise for post).
-/

section row_payload_bridge
  variable {ExtF : Type} [Field ExtF]

  -- FBB / UInt16 roundtrip helpers used by the payload bridge.
  private lemma fbb_natCast_val_eq_self' (v : FBB) : (v.val : FBB) = v := by
    ext; exact Nat.mod_eq_of_lt v.isLt

  private lemma uint16_ofNat_toNat_of_lt' {n : ℕ} (h : n < 2 ^ 16) :
      (UInt16.ofNat n).toNat = n := by
    simp only [UInt16.ofNat, UInt16.toNat, BitVec.toNat_ofNat]
    omega

  private lemma fbb_uint16_roundtrip' (v : FBB) (hv : v.val < 2 ^ 16) :
      ((UInt16.ofNat v.val).toNat : FBB) = v := by
    rw [uint16_ofNat_toNat_of_lt' hv]
    exact fbb_natCast_val_eq_self' v

  set_option maxHeartbeats 800000 in
  lemma msgPayload_rowPreMsg_eq_permPreRowEntry
      (air : Valid_KeccakfPermAir FBB ExtF) (row : ℕ)
      (h_u16 : ∀ i, i < 100 →
        (preimage air i row).val < 2 ^ 16) :
      msgPayload (rowPreMsg air row) = (permPreRowEntry air row).payload := by
    refine Vector.ext (fun i hi => ?_)
    simp only [msgPayload, rowPreMsg, permPreRowEntry, flagField,
      Vector.getElem_ofFn, Vector.get_ofFn]
    by_cases h0 : i = 0
    · subst h0; simp
    · by_cases h1 : i = 1
      · subst h1; simp
      · simp only [dif_neg h0, dif_neg h1, if_neg h0, if_neg h1]
        exact fbb_uint16_roundtrip' _ (h_u16 (i - 2) (by omega))

  set_option maxHeartbeats 800000 in
  lemma msgPayload_rowPostMsg_eq_permPostRowEntry
      (air : Valid_KeccakfPermAir FBB ExtF) (row : ℕ)
      (h_u16 : ∀ i, i < 100 →
        (if i < 4
         then (a_ppp_00_limb air i row).val
         else (a_prime_prime air i row).val) < 2 ^ 16) :
      msgPayload (rowPostMsg air row) = (permPostRowEntry air row).payload := by
    refine Vector.ext (fun i hi => ?_)
    simp only [msgPayload, rowPostMsg, permPostRowEntry, flagField,
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
          exact fbb_uint16_roundtrip' _ h_bound
        · have h_bound := h_u16 (i - 2) h_idx
          simp only [if_neg h4] at h_bound ⊢
          exact fbb_uint16_roundtrip' _ h_bound

end row_payload_bridge

end KeccakfPermAir.constraints
