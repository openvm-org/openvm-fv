/-
  Concrete subset of the Keccak state-bus infrastructure.

  Contains: generic bus-entry helpers, message payload serialization,
  and typed bus entry/block definitions needed by both
  `KeccakfPermAirViews.lean` and `KeccakfOpAir` composition.
-/
import Mathlib
import VmExtensions.Airs.KeccakfOpAir
import VmExtensions.Airs.KeccakfOpAirViews
import OpenvmFv.Fundamentals.BabyBear
import OpenvmFv.Fundamentals.Interaction

set_option autoImplicit false

namespace Interaction

structure KeccakfStateBusEntry (F : Type) where
  multiplicity : F
  payload : Vector F 102
deriving DecidableEq, Inhabited

@[simp]
def KeccakfStateBusEntry.deserialise
    (entry : FBB × Vector FBB 102) : KeccakfStateBusEntry FBB where
  multiplicity := entry.1
  payload := entry.2

instance KeccakfStateBusEntryInstance :
    BusEntry FBB (KeccakfStateBusEntry FBB) where
  multiplicity := fun entry => entry.multiplicity
  data_length := 102
  data := fun entry => entry.payload
  axioms := fun _ => True
  wf_properties := fun entry =>
    (entry.payload[0] = 0 ∨ entry.payload[0] = 1) ∧
      ∀ i : Fin 100, entry.payload.get ⟨i.val + 2, by omega⟩ < (2 : FBB) ^ 16
  wf_assume_cond := fun entry => entry.multiplicity = -1
  wf_assert_cond := fun entry => entry.multiplicity = 1
  deserialise := KeccakfStateBusEntry.deserialise
  inv_ser_deser := by
    intro x
    cases x
    rfl
  inv_deser_ser := by
    intro x
    cases x
    rfl

@[simp]
theorem KeccakfStateBusEntry.serialiseToList_eq
    (entry : KeccakfStateBusEntry FBB) :
    BusEntry.serialiseToList entry = (entry.multiplicity, entry.payload.toList) := by
  rfl

end Interaction

namespace Keccakf.constraints

open Keccakf.Interface
open KeccakfOpAir
open KeccakfOpAir.Views
open BabyBear

/-! ## Generic Bus Entry Helpers -/

@[simp]
def serialiseToList {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) :
    List (FBB × List FBB) :=
  rowData.map Interaction.BusEntry.serialiseToList

@[simp]
def axioms {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
  List.Forall id (rowData.map (Interaction.BusEntry.axioms FBB))

@[simp]
def propertiesToAssume {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
  List.Forall id (rowData.map (Interaction.BusEntry.assume FBB))

@[simp]
def propertiesToAssert {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
  List.Forall id (rowData.map (Interaction.BusEntry.assert FBB))

/-! ## Message Serialization -/

open BabyBear in
private lemma fbb_val_natCast {n : ℕ} (h : n < BB_prime) :
    (n : FBB).val = n := by
  simp [Nat.mod_eq_of_lt h]

lemma timestampBound_lt_BBPrime : timestampBound < BB_prime := by
  decide

lemma u16_toNat_lt_BBPrime (u : UInt16) : u.toNat < BB_prime := by
  exact lt_trans u.toNat_lt (by decide)

lemma fbb_natCast_inj_of_lt {m n : ℕ}
    (hm : m < BB_prime) (hn : n < BB_prime)
    (h : (m : FBB) = (n : FBB)) :
    m = n := by
  have hval := congrArg Fin.val h
  simpa [fbb_val_natCast hm, fbb_val_natCast hn] using hval

@[simp]
def flagField (isPost : Bool) : FBB :=
  if isPost then 1 else 0

lemma flagField_injective : Function.Injective flagField := by
  intro b₁ b₂ h
  cases b₁ <;> cases b₂ <;> simp [flagField] at h ⊢

/-- Field-level payload used by `Interaction.KeccakfStateBusEntry`.
    This is the data that future bus-composition proofs will match on before
    lifting back to normalized `KeccakStateMsg`s. -/
noncomputable def msgPayload (msg : KeccakStateMsg) : Vector FBB 102 :=
  Vector.ofFn fun i =>
    if h0 : i.val = 0 then
      flagField msg.isPost
    else if h1 : i.val = 1 then
      (msg.timestamp : FBB)
    else
      let j : Fin 100 := ⟨i.val - 2, by
        have hi : i.val < 102 := i.isLt
        omega⟩
      ((msg.state.get j).toNat : FBB)

def flagIx : Fin 102 := ⟨0, by decide⟩

def timestampIx : Fin 102 := ⟨1, by decide⟩

def stateIx (i : Fin 100) : Fin 102 := ⟨i.val + 2, by omega⟩

@[simp]
theorem msgPayload_flag (msg : KeccakStateMsg) :
    (msgPayload msg)[0] = flagField msg.isPost := by
  simp [msgPayload, flagField]

@[simp]
theorem msgPayload_timestamp (msg : KeccakStateMsg) :
    (msgPayload msg)[1] = (msg.timestamp : FBB) := by
  simp [msgPayload]

@[simp]
theorem msgPayload_state_limb (msg : KeccakStateMsg) (i : Fin 100) :
    (msgPayload msg)[i.val + 2] = ((msg.state.get i).toNat : FBB) := by
  have h1 : ¬ i.val + 2 = 1 := by omega
  simp [msgPayload, h1]

@[simp]
theorem msgPayload_get_flag (msg : KeccakStateMsg) :
    (msgPayload msg).get flagIx = flagField msg.isPost := by
  change (msgPayload msg)[0] = flagField msg.isPost
  exact msgPayload_flag msg

@[simp]
theorem msgPayload_get_timestamp (msg : KeccakStateMsg) :
    (msgPayload msg).get timestampIx = (msg.timestamp : FBB) := by
  change (msgPayload msg)[1] = (msg.timestamp : FBB)
  exact msgPayload_timestamp msg

@[simp]
theorem msgPayload_get_state_limb (msg : KeccakStateMsg) (i : Fin 100) :
    (msgPayload msg).get (stateIx i) = ((msg.state.get i).toNat : FBB) := by
  change (msgPayload msg)[i.val + 2] = ((msg.state.get i).toNat : FBB)
  exact msgPayload_state_limb msg i

/-- Explicit helper property needed by the future bus-composition proof: the
    field-level keccak payload serialization is injective on normalized
    messages once timestamps are known to lie within the VM timestamp bound. -/
def PayloadSerializationInjective : Prop :=
  ∀ {msg₁ msg₂ : KeccakStateMsg},
    msg₁.timestamp < timestampBound →
    msg₂.timestamp < timestampBound →
    msgPayload msg₁ = msgPayload msg₂ →
    msg₁ = msg₂

/-- Send-side keccak state-bus entry for a normalized message. -/
noncomputable def msgToAssertEntry (msg : KeccakStateMsg) :
    Interaction.KeccakfStateBusEntry FBB where
  multiplicity := 1
  payload := msgPayload msg

/-- Receive-side keccak state-bus entry for a normalized message. -/
noncomputable def msgToAssumeEntry (msg : KeccakStateMsg) :
    Interaction.KeccakfStateBusEntry FBB where
  multiplicity := -1
  payload := msgPayload msg

/-- Entry-level form of `PayloadSerializationInjective` for op sends. -/
def AssertEntrySerializationInjective : Prop :=
  ∀ {msg₁ msg₂ : KeccakStateMsg},
    msg₁.timestamp < timestampBound →
    msg₂.timestamp < timestampBound →
    msgToAssertEntry msg₁ = msgToAssertEntry msg₂ →
    msg₁ = msg₂

/-- Entry-level form of `PayloadSerializationInjective` for perm receives. -/
def AssumeEntrySerializationInjective : Prop :=
  ∀ {msg₁ msg₂ : KeccakStateMsg},
    msg₁.timestamp < timestampBound →
    msg₂.timestamp < timestampBound →
    msgToAssumeEntry msg₁ = msgToAssumeEntry msg₂ →
    msg₁ = msg₂

lemma msgPayload_eq_implies_flagField_eq
    {msg₁ msg₂ : KeccakStateMsg}
    (h_payload : msgPayload msg₁ = msgPayload msg₂) :
    flagField msg₁.isPost = flagField msg₂.isPost := by
  have h_eq_at :
      (msgPayload msg₁).get flagIx = (msgPayload msg₂).get flagIx := by
    exact congrArg (fun payload => payload.get flagIx) h_payload
  rw [msgPayload_get_flag, msgPayload_get_flag] at h_eq_at
  exact h_eq_at

lemma msgPayload_eq_implies_isPost_eq
    {msg₁ msg₂ : KeccakStateMsg}
    (h_payload : msgPayload msg₁ = msgPayload msg₂) :
    msg₁.isPost = msg₂.isPost :=
  flagField_injective (msgPayload_eq_implies_flagField_eq h_payload)

lemma msgPayload_eq_implies_timestamp_field_eq
    {msg₁ msg₂ : KeccakStateMsg}
    (h_payload : msgPayload msg₁ = msgPayload msg₂) :
    (msg₁.timestamp : FBB) = (msg₂.timestamp : FBB) := by
  have h_eq_at :
      (msgPayload msg₁).get timestampIx =
        (msgPayload msg₂).get timestampIx := by
    exact congrArg (fun payload => payload.get timestampIx) h_payload
  rw [msgPayload_get_timestamp, msgPayload_get_timestamp] at h_eq_at
  exact h_eq_at

lemma msgPayload_eq_implies_timestamp_eq_of_lt
    {msg₁ msg₂ : KeccakStateMsg}
    (h₁ : msg₁.timestamp < timestampBound)
    (h₂ : msg₂.timestamp < timestampBound)
    (h_payload : msgPayload msg₁ = msgPayload msg₂) :
    msg₁.timestamp = msg₂.timestamp := by
  apply fbb_natCast_inj_of_lt
    (lt_trans h₁ timestampBound_lt_BBPrime)
    (lt_trans h₂ timestampBound_lt_BBPrime)
  exact msgPayload_eq_implies_timestamp_field_eq h_payload

lemma msgPayload_eq_implies_state_limb_field_eq
    {msg₁ msg₂ : KeccakStateMsg}
    (h_payload : msgPayload msg₁ = msgPayload msg₂)
    (i : Fin 100) :
    ((msg₁.state.get i).toNat : FBB) = ((msg₂.state.get i).toNat : FBB) := by
  have h_eq_at :
      (msgPayload msg₁).get (stateIx i) =
        (msgPayload msg₂).get (stateIx i) := by
    exact congrArg (fun payload => payload.get (stateIx i)) h_payload
  rw [msgPayload_get_state_limb, msgPayload_get_state_limb] at h_eq_at
  exact h_eq_at

lemma msgPayload_eq_implies_state_limb_nat_eq
    {msg₁ msg₂ : KeccakStateMsg}
    (h_payload : msgPayload msg₁ = msgPayload msg₂)
    (i : Fin 100) :
    (msg₁.state.get i).toNat = (msg₂.state.get i).toNat := by
  apply fbb_natCast_inj_of_lt
    (u16_toNat_lt_BBPrime (msg₁.state.get i))
    (u16_toNat_lt_BBPrime (msg₂.state.get i))
  exact msgPayload_eq_implies_state_limb_field_eq h_payload i

lemma msgPayload_eq_implies_state_limb_eq
    {msg₁ msg₂ : KeccakStateMsg}
    (h_payload : msgPayload msg₁ = msgPayload msg₂)
    (i : Fin 100) :
    msg₁.state.get i = msg₂.state.get i := by
  apply UInt16.eq_of_toBitVec_eq
  rw [← BitVec.toNat_inj]
  exact msgPayload_eq_implies_state_limb_nat_eq h_payload i

lemma busState_eq_of_limb_eq
    {state₁ state₂ : KeccakBusState}
    (h_limb : ∀ i : Fin 100, state₁.get i = state₂.get i) :
    state₁ = state₂ := by
  apply Vector.ext
  intro i hi
  exact h_limb ⟨i, hi⟩

lemma msgPayload_eq_implies_state_eq
    {msg₁ msg₂ : KeccakStateMsg}
    (h_payload : msgPayload msg₁ = msgPayload msg₂) :
    msg₁.state = msg₂.state :=
  busState_eq_of_limb_eq (fun i => msgPayload_eq_implies_state_limb_eq h_payload i)

theorem msgPayload_inj_of_timestamp_lt
    {msg₁ msg₂ : KeccakStateMsg}
    (h₁ : msg₁.timestamp < timestampBound)
    (h₂ : msg₂.timestamp < timestampBound)
    (h_payload : msgPayload msg₁ = msgPayload msg₂) :
    msg₁ = msg₂ := by
  cases msg₁ with
  | mk isPost₁ timestamp₁ state₁ =>
    cases msg₂ with
    | mk isPost₂ timestamp₂ state₂ =>
      have h_isPost : isPost₁ = isPost₂ :=
        msgPayload_eq_implies_isPost_eq h_payload
      have h_timestamp : timestamp₁ = timestamp₂ :=
        msgPayload_eq_implies_timestamp_eq_of_lt h₁ h₂ h_payload
      have h_state : state₁ = state₂ :=
        msgPayload_eq_implies_state_eq h_payload
      cases h_isPost
      cases h_timestamp
      cases h_state
      rfl

theorem payloadSerializationInjective :
    PayloadSerializationInjective := by
  intro msg₁ msg₂ h₁ h₂ h_payload
  exact msgPayload_inj_of_timestamp_lt h₁ h₂ h_payload

lemma msgToAssertEntry_eq_implies_payload_eq
    {msg₁ msg₂ : KeccakStateMsg}
    (h_entry : msgToAssertEntry msg₁ = msgToAssertEntry msg₂) :
    msgPayload msg₁ = msgPayload msg₂ := by
  unfold msgToAssertEntry at h_entry
  injection h_entry with _ h_payload

theorem msgToAssertEntry_inj_of_timestamp_lt
    {msg₁ msg₂ : KeccakStateMsg}
    (h₁ : msg₁.timestamp < timestampBound)
    (h₂ : msg₂.timestamp < timestampBound)
    (h_entry : msgToAssertEntry msg₁ = msgToAssertEntry msg₂) :
    msg₁ = msg₂ := by
  exact msgPayload_inj_of_timestamp_lt h₁ h₂
    (msgToAssertEntry_eq_implies_payload_eq h_entry)

theorem assertEntrySerializationInjective :
    AssertEntrySerializationInjective := by
  intro msg₁ msg₂ h₁ h₂ h_entry
  exact msgToAssertEntry_inj_of_timestamp_lt h₁ h₂ h_entry

lemma msgToAssumeEntry_eq_implies_payload_eq
    {msg₁ msg₂ : KeccakStateMsg}
    (h_entry : msgToAssumeEntry msg₁ = msgToAssumeEntry msg₂) :
    msgPayload msg₁ = msgPayload msg₂ := by
  unfold msgToAssumeEntry at h_entry
  injection h_entry with _ h_payload

theorem msgToAssumeEntry_inj_of_timestamp_lt
    {msg₁ msg₂ : KeccakStateMsg}
    (h₁ : msg₁.timestamp < timestampBound)
    (h₂ : msg₂.timestamp < timestampBound)
    (h_entry : msgToAssumeEntry msg₁ = msgToAssumeEntry msg₂) :
    msg₁ = msg₂ := by
  exact msgPayload_inj_of_timestamp_lt h₁ h₂
    (msgToAssumeEntry_eq_implies_payload_eq h_entry)

theorem assumeEntrySerializationInjective :
    AssumeEntrySerializationInjective := by
  intro msg₁ msg₂ h₁ h₂ h_entry
  exact msgToAssumeEntry_inj_of_timestamp_lt h₁ h₂ h_entry

@[simp]
theorem wf_msgToAssertEntry (msg : KeccakStateMsg) :
    Interaction.BusEntry.assert FBB (msgToAssertEntry msg) := by
  intro _
  simp only [msgToAssertEntry]
  refine ⟨?_, ?_⟩
  · rw [msgPayload_flag]
    cases msg.isPost <;> simp [flagField]
  · intro i
    change (msgPayload msg)[i.val + 2] < (2:FBB)^16
    rw [msgPayload_state_limb,
      show ((2:FBB)^16) = (((65536 : ℕ) : FBB)) by norm_num, Fin.lt_def,
      fbb_val_natCast (u16_toNat_lt_BBPrime _), fbb_val_natCast (by norm_num)]
    exact (msg.state.get i).toNat_lt

@[simp]
theorem wf_msgToAssumeEntry (msg : KeccakStateMsg) :
    Interaction.BusEntry.assume FBB (msgToAssumeEntry msg) := by
  intro _
  simp only [msgToAssumeEntry]
  refine ⟨?_, ?_⟩
  · rw [msgPayload_flag]
    cases msg.isPost <;> simp [flagField]
  · intro i
    change (msgPayload msg)[i.val + 2] < (2:FBB)^16
    rw [msgPayload_state_limb,
      show ((2:FBB)^16) = (((65536 : ℕ) : FBB)) by norm_num, Fin.lt_def,
      fbb_val_natCast (u16_toNat_lt_BBPrime _), fbb_val_natCast (by norm_num)]
    exact (msg.state.get i).toNat_lt

/-! ## Typed Keccak State-Bus Rows / Blocks -/

noncomputable def opPreEntry {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    Interaction.KeccakfStateBusEntry FBB :=
  msgToAssertEntry (preMsgOfColumns air row)

noncomputable def opPostEntry {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    Interaction.KeccakfStateBusEntry FBB :=
  msgToAssertEntry (postMsgOfColumns air row)

@[simp]
noncomputable def opStateBusEntries {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List (Interaction.KeccakfStateBusEntry FBB) :=
  [opPreEntry air row, opPostEntry air row]

@[simp]
theorem opStateBusEntries_length {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    (opStateBusEntries air row).length = 2 := by
  simp [opStateBusEntries]

@[simp]
noncomputable def opStateBusRow {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List (FBB × List FBB) :=
  serialiseToList (opStateBusEntries air row)

@[simp]
noncomputable def axiomsPerOpRow {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    Prop :=
  axioms (opStateBusEntries air row)

@[simp]
noncomputable def wf_propertiesToAssertPerOpRow {ExtF : Type}
    [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop :=
  propertiesToAssert (opStateBusEntries air row)

/-! ## Aggregated Keccak State-Bus Traces -/

/-- Aggregated op-side keccak state-bus entries for a selected list of rows. -/
@[simp]
noncomputable def opStateBusEntryTrace {ExtF : Type}
    [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (rows : List ℕ) :
    List (Interaction.KeccakfStateBusEntry FBB) :=
  rows.flatMap (fun row => opStateBusEntries air row)

/-- Serialized op-side keccak state-bus slice for a selected list of rows. -/
@[simp]
noncomputable def opStateBusTrace {ExtF : Type}
    [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (rows : List ℕ) :
    List (FBB × List FBB) :=
  serialiseToList (opStateBusEntryTrace air rows)

/-- Axioms for the aggregated op-side keccak state-bus entry list. -/
@[simp]
noncomputable def axiomsOnOpRows {ExtF : Type}
    [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (rows : List ℕ) : Prop :=
  axioms (opStateBusEntryTrace air rows)

/-- Send-side well-formedness for the aggregated op-side keccak trace. -/
@[simp]
noncomputable def wf_propertiesToAssertOnOpRows {ExtF : Type}
    [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (rows : List ℕ) : Prop :=
  propertiesToAssert (opStateBusEntryTrace air rows)

end Keccakf.constraints
