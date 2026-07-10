import VmExtensions.Constraints.Sha2BlockHasherVmAir_sha512
import OpenvmFv.Fundamentals.BabyBear
import OpenvmFv.Fundamentals.Interaction

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace Sha2BlockHasherVmAir_sha512.constraints

open BabyBear

section Helpers

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

/-- The BabyBear `1 / 2` constant used by the extracted selector polynomials. -/
abbrev wrapperBus_choose2_coeff : F := (1006632961 : F)

/-- `x choose 2` expressed in the field exactly as in extraction. -/
noncomputable def wrapperBus_choose2 (x : F) : F :=
  x * (x - 1) * wrapperBus_choose2_coeff

/-- Selector that is `1` exactly on encoder-sum `0` rows. -/
noncomputable def wrapperBus_padding_choose2 (c : C F ExtF) (row : ℕ) : F :=
  let s :=
    encoder_idx c 0 row +
    encoder_idx c 1 row +
    encoder_idx c 2 row +
    encoder_idx c 3 row +
    encoder_idx c 4 row +
    encoder_idx c 5 row
  (2 - s) * (1 - s) * wrapperBus_choose2_coeff

/-- Compose one schedule byte from 8 little-endian bits in a 64-bit schedule word. -/
noncomputable def compose_schedule_byte (c : C F ExtF) (slot byteIdx : ℕ) (row : ℕ) : F :=
  (Finset.range 8).sum (fun bit =>
    msg_schedule_w c slot ((7 - byteIdx) * 8 + bit) row * ((2 : F) ^ bit))

/-- Compose the corresponding rotation-1 schedule byte. -/
noncomputable def compose_next_schedule_byte (c : C F ExtF) (slot byteIdx : ℕ) (row : ℕ) : F :=
  (Finset.range 8).sum (fun bit =>
    next_msg_schedule_w c slot ((7 - byteIdx) * 8 + bit) row * ((2 : F) ^ bit))

end Helpers

section Entries

structure Sha2WrapperBus512StateEntry (F : Type) [Field F] where
  multiplicity : F
  message_type : F
  request_id : F
  prev_state_u16 : Vector F 32
  new_state_bytes : Vector F 64
deriving BEq, DecidableEq, Inhabited

structure Sha2WrapperBus512Msg1Entry (F : Type) [Field F] where
  multiplicity : F
  message_type : F
  request_id : F
  local_msg_bytes : Vector F 32
  next_msg_bytes : Vector F 32
deriving BEq, DecidableEq, Inhabited

structure Sha2WrapperBus512Msg2Entry (F : Type) [Field F] where
  multiplicity : F
  message_type : F
  request_id : F
  local_msg_bytes : Vector F 32
  next_msg_bytes : Vector F 32
deriving BEq, DecidableEq, Inhabited

variable {F : Type} [Field F]

@[simp] def Sha2WrapperBus512StateEntry.toRaw
    (entry : Sha2WrapperBus512StateEntry F) : F × List F :=
  (entry.multiplicity,
    [entry.message_type, entry.request_id] ++
    entry.prev_state_u16.toList ++
    entry.new_state_bytes.toList)

@[simp] def Sha2WrapperBus512Msg1Entry.toRaw
    (entry : Sha2WrapperBus512Msg1Entry F) : F × List F :=
  (entry.multiplicity,
    [entry.message_type, entry.request_id] ++
    entry.local_msg_bytes.toList ++
    entry.next_msg_bytes.toList)

@[simp] def Sha2WrapperBus512Msg2Entry.toRaw
    (entry : Sha2WrapperBus512Msg2Entry F) : F × List F :=
  (entry.multiplicity,
    [entry.message_type, entry.request_id] ++
    entry.local_msg_bytes.toList ++
    entry.next_msg_bytes.toList)

@[simp, grind] def Sha2WrapperBus512StateEntry.deserialise
    (entry : F × Vector F 98) : Sha2WrapperBus512StateEntry F where
  multiplicity := entry.1
  message_type := entry.2[0]
  request_id := entry.2[1]
  prev_state_u16 := Vector.ofFn (fun i => entry.2.get ⟨i.1 + 2, by omega⟩)
  new_state_bytes := Vector.ofFn (fun i => entry.2.get ⟨i.1 + 34, by omega⟩)

@[simp, grind] def Sha2WrapperBus512Msg1Entry.deserialise
    (entry : F × Vector F 66) : Sha2WrapperBus512Msg1Entry F where
  multiplicity := entry.1
  message_type := entry.2[0]
  request_id := entry.2[1]
  local_msg_bytes := Vector.ofFn (fun i => entry.2.get ⟨i.1 + 2, by omega⟩)
  next_msg_bytes := Vector.ofFn (fun i => entry.2.get ⟨i.1 + 34, by omega⟩)

@[simp, grind] def Sha2WrapperBus512Msg2Entry.deserialise
    (entry : F × Vector F 66) : Sha2WrapperBus512Msg2Entry F where
  multiplicity := entry.1
  message_type := entry.2[0]
  request_id := entry.2[1]
  local_msg_bytes := Vector.ofFn (fun i => entry.2.get ⟨i.1 + 2, by omega⟩)
  next_msg_bytes := Vector.ofFn (fun i => entry.2.get ⟨i.1 + 34, by omega⟩)

end Entries

section BusEntryInstances

/-- Bus-entry payload for the state wrapper entry. -/
@[simp] def stateEntryData (entry : Sha2WrapperBus512StateEntry FBB) : Vector FBB 98 :=
  Vector.ofFn (fun i =>
    if h0 : i.1 = 0 then
      entry.message_type
    else if h1 : i.1 = 1 then
      entry.request_id
    else if hprev : i.1 < 34 then
      entry.prev_state_u16.get ⟨i.1 - 2, by omega⟩
    else
      entry.new_state_bytes.get ⟨i.1 - 34, by omega⟩)

theorem stateEntryData_get_message_type
    (entry : Sha2WrapperBus512StateEntry FBB) :
    (stateEntryData entry).get 0 = entry.message_type := by
  simp [stateEntryData]

theorem stateEntryData_get_request_id
    (entry : Sha2WrapperBus512StateEntry FBB) :
    (stateEntryData entry).get 1 = entry.request_id := by
  simp [stateEntryData]

theorem stateEntryData_get_prev
    (entry : Sha2WrapperBus512StateEntry FBB) (i : Fin 32) :
    (stateEntryData entry).get ⟨i.1 + 2, by omega⟩ = entry.prev_state_u16.get i := by
  have h0 : ¬ i.1 + 2 = 0 := by omega
  have h1 : ¬ i.1 + 2 = 1 := by omega
  have hprev : i.1 + 2 < 34 := by omega
  have hsub : i.1 + 2 - 2 = i.1 := by omega
  simp [stateEntryData, h0, h1, hprev, hsub]

theorem stateEntryData_get_new
    (entry : Sha2WrapperBus512StateEntry FBB) (i : Fin 64) :
    (stateEntryData entry).get ⟨i.1 + 34, by omega⟩ = entry.new_state_bytes.get i := by
  have h0 : ¬ i.1 + 34 = 0 := by omega
  have h1 : ¬ i.1 + 34 = 1 := by omega
  have hprev : ¬ i.1 + 34 < 34 := by omega
  have hsub : i.1 + 34 - 34 = i.1 := by omega
  simp [stateEntryData, h0, h1, hprev, hsub]

/-- Bus-entry payload for either 64-byte message wrapper entry. -/
@[simp] def msgEntryData {α : Type} [Field α]
    (message_type : α) (request_id : α)
    (localBytes nextBytes : Vector α 32) : Vector α 66 :=
  Vector.ofFn (fun i =>
    if h0 : i.1 = 0 then
      message_type
    else if h1 : i.1 = 1 then
      request_id
    else if hlocal : i.1 < 34 then
      localBytes.get ⟨i.1 - 2, by omega⟩
    else
      nextBytes.get ⟨i.1 - 34, by omega⟩)

theorem msgEntryData_get_message_type {α : Type} [Field α]
    (message_type request_id : α) (localBytes nextBytes : Vector α 32) :
    (msgEntryData message_type request_id localBytes nextBytes).get 0 = message_type := by
  simp [msgEntryData]

theorem msgEntryData_get_request_id {α : Type} [Field α]
    (message_type request_id : α) (localBytes nextBytes : Vector α 32) :
    (msgEntryData message_type request_id localBytes nextBytes).get 1 = request_id := by
  simp [msgEntryData]

theorem msgEntryData_get_local {α : Type} [Field α]
    (message_type request_id : α) (localBytes nextBytes : Vector α 32) (i : Fin 32) :
    (msgEntryData message_type request_id localBytes nextBytes).get ⟨i.1 + 2, by omega⟩ =
      localBytes.get i := by
  have h0 : ¬ i.1 + 2 = 0 := by omega
  have h1 : ¬ i.1 + 2 = 1 := by omega
  have hlocal : i.1 + 2 < 34 := by omega
  have hsub : i.1 + 2 - 2 = i.1 := by omega
  simp [msgEntryData, h0, h1, hlocal, hsub]

theorem msgEntryData_get_next {α : Type} [Field α]
    (message_type request_id : α) (localBytes nextBytes : Vector α 32) (i : Fin 32) :
    (msgEntryData message_type request_id localBytes nextBytes).get ⟨i.1 + 34, by omega⟩ =
      nextBytes.get i := by
  have h0 : ¬ i.1 + 34 = 0 := by omega
  have h1 : ¬ i.1 + 34 = 1 := by omega
  have hlocal : ¬ i.1 + 34 < 34 := by omega
  have hsub : i.1 + 34 - 34 = i.1 := by omega
  simp [msgEntryData, h0, h1, hlocal, hsub]

private theorem stateEntry_deserialise_serialise
    (entry : Sha2WrapperBus512StateEntry FBB) :
    Sha2WrapperBus512StateEntry.deserialise (entry.multiplicity, stateEntryData entry) = entry := by
  cases entry with
  | mk multiplicity message_type request_id prev_state_u16 new_state_bytes =>
      simp [Sha2WrapperBus512StateEntry.deserialise, stateEntryData]
      constructor
      · refine Vector.ext ?_
        intro i hi
        have h0 : ¬ i + 2 = 0 := by omega
        have h1 : ¬ i + 2 = 1 := by omega
        have hprev : i + 2 < 34 := by omega
        have hsub : i + 2 - 2 = i := by omega
        simp [Sha2WrapperBus512StateEntry.deserialise, stateEntryData, h0, h1, hprev, hsub]
        rfl
      · refine Vector.ext ?_
        intro i hi
        have h0 : ¬ i + 34 = 0 := by omega
        have h1 : ¬ i + 34 = 1 := by omega
        have hprev : ¬ i + 34 < 34 := by omega
        have hsub : i + 34 - 34 = i := by omega
        simp [Sha2WrapperBus512StateEntry.deserialise, stateEntryData, h0, h1, hprev, hsub]
        rfl

private theorem stateEntryData_deserialise_get
    (entry : FBB × Vector FBB 98) (i : ℕ) (hi : i < 98) :
    (stateEntryData (Sha2WrapperBus512StateEntry.deserialise entry))[i] = entry.2[i] := by
  interval_cases i <;> simp [Sha2WrapperBus512StateEntry.deserialise, stateEntryData] <;> rfl

private theorem stateEntry_serialise_deserialise
    (entry : FBB × Vector FBB 98) :
    (entry.1, stateEntryData (Sha2WrapperBus512StateEntry.deserialise entry)) = entry := by
  cases entry with
  | mk multiplicity data =>
      refine Prod.ext rfl ?_
      exact Vector.ext (stateEntryData_deserialise_get (multiplicity, data))

private theorem msg1Entry_deserialise_serialise
    (entry : Sha2WrapperBus512Msg1Entry FBB) :
    Sha2WrapperBus512Msg1Entry.deserialise
        (entry.multiplicity,
          msgEntryData entry.message_type entry.request_id entry.local_msg_bytes entry.next_msg_bytes) =
      entry := by
  cases entry with
  | mk multiplicity message_type request_id local_msg_bytes next_msg_bytes =>
      simp [Sha2WrapperBus512Msg1Entry.deserialise, msgEntryData]
      constructor
      · refine Vector.ext ?_
        intro i hi
        have h0 : ¬ i + 2 = 0 := by omega
        have h1 : ¬ i + 2 = 1 := by omega
        have hlocal : i + 2 < 34 := by omega
        have hsub : i + 2 - 2 = i := by omega
        simp [Sha2WrapperBus512Msg1Entry.deserialise, msgEntryData, h0, h1, hlocal, hsub]
        rfl
      · refine Vector.ext ?_
        intro i hi
        have h0 : ¬ i + 34 = 0 := by omega
        have h1 : ¬ i + 34 = 1 := by omega
        have hlocal : ¬ i + 34 < 34 := by omega
        have hsub : i + 34 - 34 = i := by omega
        simp [Sha2WrapperBus512Msg1Entry.deserialise, msgEntryData, h0, h1, hlocal, hsub]
        rfl

private theorem msg1EntryData_deserialise_get
    (entry : FBB × Vector FBB 66) (i : ℕ) (hi : i < 66) :
    (msgEntryData
      (Sha2WrapperBus512Msg1Entry.deserialise entry).message_type
      (Sha2WrapperBus512Msg1Entry.deserialise entry).request_id
      (Sha2WrapperBus512Msg1Entry.deserialise entry).local_msg_bytes
      (Sha2WrapperBus512Msg1Entry.deserialise entry).next_msg_bytes)[i] =
    entry.2[i] := by
  interval_cases i <;> simp [Sha2WrapperBus512Msg1Entry.deserialise, msgEntryData] <;> rfl

private theorem msg1Entry_serialise_deserialise
    (entry : FBB × Vector FBB 66) :
    (entry.1,
      msgEntryData
        (Sha2WrapperBus512Msg1Entry.deserialise entry).message_type
        (Sha2WrapperBus512Msg1Entry.deserialise entry).request_id
        (Sha2WrapperBus512Msg1Entry.deserialise entry).local_msg_bytes
        (Sha2WrapperBus512Msg1Entry.deserialise entry).next_msg_bytes) = entry := by
  cases entry with
  | mk multiplicity data =>
      refine Prod.ext rfl ?_
      exact Vector.ext (msg1EntryData_deserialise_get (multiplicity, data))

private theorem msg2Entry_deserialise_serialise
    (entry : Sha2WrapperBus512Msg2Entry FBB) :
    Sha2WrapperBus512Msg2Entry.deserialise
        (entry.multiplicity,
          msgEntryData entry.message_type entry.request_id entry.local_msg_bytes entry.next_msg_bytes) =
      entry := by
  cases entry with
  | mk multiplicity message_type request_id local_msg_bytes next_msg_bytes =>
      simp [Sha2WrapperBus512Msg2Entry.deserialise, msgEntryData]
      constructor
      · refine Vector.ext ?_
        intro i hi
        have h0 : ¬ i + 2 = 0 := by omega
        have h1 : ¬ i + 2 = 1 := by omega
        have hlocal : i + 2 < 34 := by omega
        have hsub : i + 2 - 2 = i := by omega
        simp [Sha2WrapperBus512Msg2Entry.deserialise, msgEntryData, h0, h1, hlocal, hsub]
        rfl
      · refine Vector.ext ?_
        intro i hi
        have h0 : ¬ i + 34 = 0 := by omega
        have h1 : ¬ i + 34 = 1 := by omega
        have hlocal : ¬ i + 34 < 34 := by omega
        have hsub : i + 34 - 34 = i := by omega
        simp [Sha2WrapperBus512Msg2Entry.deserialise, msgEntryData, h0, h1, hlocal, hsub]
        rfl

private theorem msg2EntryData_deserialise_get
    (entry : FBB × Vector FBB 66) (i : ℕ) (hi : i < 66) :
    (msgEntryData
      (Sha2WrapperBus512Msg2Entry.deserialise entry).message_type
      (Sha2WrapperBus512Msg2Entry.deserialise entry).request_id
      (Sha2WrapperBus512Msg2Entry.deserialise entry).local_msg_bytes
      (Sha2WrapperBus512Msg2Entry.deserialise entry).next_msg_bytes)[i] =
    entry.2[i] := by
  interval_cases i <;> simp [Sha2WrapperBus512Msg2Entry.deserialise, msgEntryData] <;> rfl

private theorem msg2Entry_serialise_deserialise
    (entry : FBB × Vector FBB 66) :
    (entry.1,
      msgEntryData
        (Sha2WrapperBus512Msg2Entry.deserialise entry).message_type
        (Sha2WrapperBus512Msg2Entry.deserialise entry).request_id
        (Sha2WrapperBus512Msg2Entry.deserialise entry).local_msg_bytes
        (Sha2WrapperBus512Msg2Entry.deserialise entry).next_msg_bytes) = entry := by
  cases entry with
  | mk multiplicity data =>
      refine Prod.ext rfl ?_
      exact Vector.ext (msg2EntryData_deserialise_get (multiplicity, data))

@[simp, grind] instance stateEntryBusEntry :
    Interaction.BusEntry FBB (Sha2WrapperBus512StateEntry FBB) where
  multiplicity := fun entry => entry.multiplicity
  data_length := 98
  data := stateEntryData
  axioms := fun entry => ¬ entry.multiplicity = 0 → entry.message_type = 0
  wf_properties := fun entry =>
    (∀ i : Fin 32, (entry.prev_state_u16.get i).val < 2 ^ 16) ∧
    ∀ i : Fin 64, (entry.new_state_bytes.get i).val < 256
  wf_assume_cond := fun entry => entry.multiplicity = 1
  wf_assert_cond := fun entry => entry.multiplicity = -1
  deserialise := Sha2WrapperBus512StateEntry.deserialise
  inv_deser_ser := by
    intro x
    simpa using stateEntry_deserialise_serialise x
  inv_ser_deser := by
    intro x
    simpa using stateEntry_serialise_deserialise x

@[simp, grind] instance msg1EntryBusEntry :
    Interaction.BusEntry FBB (Sha2WrapperBus512Msg1Entry FBB) where
  multiplicity := fun entry => entry.multiplicity
  data_length := 66
  data := fun entry =>
    msgEntryData entry.message_type entry.request_id entry.local_msg_bytes entry.next_msg_bytes
  axioms := fun entry => ¬ entry.multiplicity = 0 → entry.message_type = 1
  wf_properties := fun entry =>
    (∀ i : Fin 32, (entry.local_msg_bytes.get i).val < 256) ∧
    ∀ i : Fin 32, (entry.next_msg_bytes.get i).val < 256
  wf_assume_cond := fun entry => entry.multiplicity = 1
  wf_assert_cond := fun entry => entry.multiplicity = -1
  deserialise := Sha2WrapperBus512Msg1Entry.deserialise
  inv_deser_ser := by
    intro x
    simpa using msg1Entry_deserialise_serialise x
  inv_ser_deser := by
    intro x
    simpa using msg1Entry_serialise_deserialise x

@[simp, grind] instance msg2EntryBusEntry :
    Interaction.BusEntry FBB (Sha2WrapperBus512Msg2Entry FBB) where
  multiplicity := fun entry => entry.multiplicity
  data_length := 66
  data := fun entry =>
    msgEntryData entry.message_type entry.request_id entry.local_msg_bytes entry.next_msg_bytes
  axioms := fun entry => ¬ entry.multiplicity = 0 → entry.message_type = 2
  wf_properties := fun entry =>
    (∀ i : Fin 32, (entry.local_msg_bytes.get i).val < 256) ∧
    ∀ i : Fin 32, (entry.next_msg_bytes.get i).val < 256
  wf_assume_cond := fun entry => entry.multiplicity = 1
  wf_assert_cond := fun entry => entry.multiplicity = -1
  deserialise := Sha2WrapperBus512Msg2Entry.deserialise
  inv_deser_ser := by
    intro x
    simpa using msg2Entry_deserialise_serialise x
  inv_ser_deser := by
    intro x
    simpa using msg2Entry_serialise_deserialise x

end BusEntryInstances

end Sha2BlockHasherVmAir_sha512.constraints
