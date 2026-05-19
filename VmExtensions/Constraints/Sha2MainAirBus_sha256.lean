import VmExtensions.Constraints.Sha2MainAir_sha256
import OpenvmFv.Fundamentals.BabyBear
import OpenvmFv.Fundamentals.Interaction

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace Sha2MainAir_sha256.constraints

open BabyBear

/-!
Bus-facing definitions for `Sha2MainAir<Sha256Config>`.

This layer keeps the extracted bus numbering used by the main-chip AIR:

* `0`: execution bridge
* `1`: memory bridge
* `2`: program/transpiler payload
* `3`: timestamp-delta range checks
* `6`: pointer high-limb range checks
* `8`: shared SHA-2 wrapper bus
-/

abbrev Sha2MainExecutionBus : ℕ := 0
abbrev Sha2MainMemoryBus : ℕ := 1
abbrev Sha2MainProgramBus : ℕ := 2
abbrev Sha2MainRangeCheckerBus : ℕ := 3
abbrev Sha2MainBitwiseBus : ℕ := 6
abbrev Sha2MainWrapperBus : ℕ := 8

section wrapper_entries

variable (F : Type) [Field F]

structure Sha2MainWrapperStateEntry where
  multiplicity : F
  message_type : F
  request_id : F
  prev_state_u16 : Vector F 16
  new_state_bytes : Vector F 32
deriving BEq, DecidableEq, Inhabited

structure Sha2MainWrapperMsg1Entry where
  multiplicity : F
  message_type : F
  request_id : F
  local_msg_bytes : Vector F 16
  next_msg_bytes : Vector F 16
deriving BEq, DecidableEq, Inhabited

structure Sha2MainWrapperMsg2Entry where
  multiplicity : F
  message_type : F
  request_id : F
  local_msg_bytes : Vector F 16
  next_msg_bytes : Vector F 16
deriving BEq, DecidableEq, Inhabited

@[simp] def Sha2MainWrapperStateEntry.toRaw
    (entry : Sha2MainWrapperStateEntry F) : F × List F :=
  (entry.multiplicity,
    [entry.message_type, entry.request_id] ++
      entry.prev_state_u16.toList ++
      entry.new_state_bytes.toList)

@[simp] def Sha2MainWrapperMsg1Entry.toRaw
    (entry : Sha2MainWrapperMsg1Entry F) : F × List F :=
  (entry.multiplicity,
    [entry.message_type, entry.request_id] ++
      entry.local_msg_bytes.toList ++
      entry.next_msg_bytes.toList)

@[simp] def Sha2MainWrapperMsg2Entry.toRaw
    (entry : Sha2MainWrapperMsg2Entry F) : F × List F :=
  (entry.multiplicity,
    [entry.message_type, entry.request_id] ++
      entry.local_msg_bytes.toList ++
      entry.next_msg_bytes.toList)

end wrapper_entries

section interaction_views

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

private theorem range_loop_sixteen :
    List.range.loop 16 [] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by
  decide

private theorem range_loop_thirtytwo :
    List.range.loop 32 [] =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] := by
  decide

/-- One variable-range-checker bus entry. -/
abbrev rangeCheckEntry (mul val deg : F) : F × List F :=
  (mul, [val, deg])

/-- Timestamp-delta decomposition checks for the three register reads. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def registerRangeCheckerBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  (List.range 3).flatMap fun slot =>
    [
      rangeCheckEntry (is_enabled c row) (register_read_timestamp_lt_aux_0 c slot row) 17,
      rangeCheckEntry (is_enabled c row) (register_read_timestamp_lt_aux_1 c slot row) 12
    ]

/-- Timestamp-delta decomposition checks for the sixteen input-block reads. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def inputRangeCheckerBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  (List.range 16).flatMap fun slot =>
    [
      rangeCheckEntry (is_enabled c row) (input_read_timestamp_lt_aux_0 c slot row) 17,
      rangeCheckEntry (is_enabled c row) (input_read_timestamp_lt_aux_1 c slot row) 12
    ]

/-- Timestamp-delta decomposition checks for the eight previous-state reads. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def stateRangeCheckerBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  (List.range 8).flatMap fun slot =>
    [
      rangeCheckEntry (is_enabled c row) (state_read_timestamp_lt_aux_0 c slot row) 17,
      rangeCheckEntry (is_enabled c row) (state_read_timestamp_lt_aux_1 c slot row) 12
    ]

/-- Timestamp-delta decomposition checks for the eight destination writes. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def writeRangeCheckerBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  (List.range 8).flatMap fun slot =>
    [
      rangeCheckEntry (is_enabled c row) (write_timestamp_lt_aux_0 c slot row) 17,
      rangeCheckEntry (is_enabled c row) (write_timestamp_lt_aux_1 c slot row) 12
    ]

/-- All timestamp-delta range-checker entries emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def rangeCheckerBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  registerRangeCheckerBus_row c row ++
  inputRangeCheckerBus_row c row ++
  stateRangeCheckerBus_row c row ++
  writeRangeCheckerBus_row c row

/-- Execution-bus trace over the whole main-chip table. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def executionBus_trace (c : C F ExtF) : List (F × List F) :=
  (List.range (Circuit.last_row c + 1)).flatMap (executionBus_row c)

/-- Memory-bus trace over the whole main-chip table. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def memoryBus_trace (c : C F ExtF) : List (F × List F) :=
  (List.range (Circuit.last_row c + 1)).flatMap (memoryBus_row c)

/-- Program-bus trace over the whole main-chip table. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def programBus_trace (c : C F ExtF) : List (F × List F) :=
  (List.range (Circuit.last_row c + 1)).flatMap (programBus_row c)

/-- Timestamp range-checker trace over the whole main-chip table. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def rangeCheckerBus_trace (c : C F ExtF) : List (F × List F) :=
  (List.range (Circuit.last_row c + 1)).flatMap (rangeCheckerBus_row c)

/-- Bitwise-lookup trace over the whole main-chip table. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def bitwiseLookupBus_trace (c : C F ExtF) : List (F × List F) :=
  (List.range (Circuit.last_row c + 1)).flatMap (bitwiseLookupBus_row c)

/-- Typed SHA-2 `State` wrapper entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def wrapperStateEntry (c : C F ExtF) (row : ℕ) :
    Sha2MainWrapperStateEntry F where
  multiplicity := is_enabled c row
  message_type := 0
  request_id := request_id c row
  prev_state_u16 := Vector.ofFn (fun i => prev_state_u16 c i.1 row)
  new_state_bytes := Vector.ofFn (fun i => new_state_byte c i.1 row)

/-- Typed SHA-2 `Message1` wrapper entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def wrapperMsg1Entry (c : C F ExtF) (row : ℕ) :
    Sha2MainWrapperMsg1Entry F where
  multiplicity := is_enabled c row
  message_type := 1
  request_id := request_id c row
  local_msg_bytes := Vector.ofFn (fun i => message_byte c i.1 row)
  next_msg_bytes := Vector.ofFn (fun i => message_byte c (16 + i.1) row)

/-- Typed SHA-2 `Message2` wrapper entry emitted by one main-chip row. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def wrapperMsg2Entry (c : C F ExtF) (row : ℕ) :
    Sha2MainWrapperMsg2Entry F where
  multiplicity := is_enabled c row
  message_type := 2
  request_id := request_id c row
  local_msg_bytes := Vector.ofFn (fun i => message_byte c (32 + i.1) row)
  next_msg_bytes := Vector.ofFn (fun i => message_byte c (48 + i.1) row)

/-- Wrapper-bus entries emitted by one main-chip row, in typed-entry order. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def wrapperBus_row (c : C F ExtF) (row : ℕ) : List (F × List F) :=
  [
    (wrapperStateEntry c row).toRaw,
    (wrapperMsg1Entry c row).toRaw,
    (wrapperMsg2Entry c row).toRaw
  ]

/-- SHA-2 wrapper-bus trace over the whole main-chip table. -/
@[Sha2MainAir_Sha256Config_constraint_and_interaction_simplification]
def wrapperBus_trace (c : C F ExtF) : List (F × List F) :=
  (List.range (Circuit.last_row c + 1)).flatMap (wrapperBus_row c)

@[simp] lemma wrapperStateEntry_prev_state_u16_get
    (c : C F ExtF) (row : ℕ) (i : Fin 16) :
    (wrapperStateEntry c row).prev_state_u16.get i = prev_state_u16 c i.1 row := by
  simpa [wrapperStateEntry] using
    (Vector.get_ofFn (f := fun j : Fin 16 => prev_state_u16 c j.1 row) i)

@[simp] lemma wrapperStateEntry_new_state_bytes_get
    (c : C F ExtF) (row : ℕ) (i : Fin 32) :
    (wrapperStateEntry c row).new_state_bytes.get i = new_state_byte c i.1 row := by
  simpa [wrapperStateEntry] using
    (Vector.get_ofFn (f := fun j : Fin 32 => new_state_byte c j.1 row) i)

@[simp] lemma wrapperMsg1Entry_local_msg_bytes_get
    (c : C F ExtF) (row : ℕ) (i : Fin 16) :
    (wrapperMsg1Entry c row).local_msg_bytes.get i = message_byte c i.1 row := by
  simpa [wrapperMsg1Entry] using
    (Vector.get_ofFn (f := fun j : Fin 16 => message_byte c j.1 row) i)

@[simp] lemma wrapperMsg1Entry_next_msg_bytes_get
    (c : C F ExtF) (row : ℕ) (i : Fin 16) :
    (wrapperMsg1Entry c row).next_msg_bytes.get i = message_byte c (16 + i.1) row := by
  simpa [wrapperMsg1Entry] using
    (Vector.get_ofFn (f := fun j : Fin 16 => message_byte c (16 + j.1) row) i)

@[simp] lemma wrapperMsg2Entry_local_msg_bytes_get
    (c : C F ExtF) (row : ℕ) (i : Fin 16) :
    (wrapperMsg2Entry c row).local_msg_bytes.get i = message_byte c (32 + i.1) row := by
  simpa [wrapperMsg2Entry] using
    (Vector.get_ofFn (f := fun j : Fin 16 => message_byte c (32 + j.1) row) i)

@[simp] lemma wrapperMsg2Entry_next_msg_bytes_get
    (c : C F ExtF) (row : ℕ) (i : Fin 16) :
    (wrapperMsg2Entry c row).next_msg_bytes.get i = message_byte c (48 + i.1) row := by
  simpa [wrapperMsg2Entry] using
    (Vector.get_ofFn (f := fun j : Fin 16 => message_byte c (48 + j.1) row) i)

@[simp] lemma sha2StateBus_row_eq_wrapperBus_row
    (c : C F ExtF) (row : ℕ) :
    sha2StateBus_row c row = [(wrapperStateEntry c row).toRaw] := by
  simp [sha2StateBus_row, wrapperStateEntry,
    Sha2MainWrapperStateEntry.toRaw,
    Vector.toList_ofFn,
    List.range, range_loop_sixteen, range_loop_thirtytwo]

@[simp] lemma sha2Message1Bus_row_eq_wrapperBus_row
    (c : C F ExtF) (row : ℕ) :
    sha2Message1Bus_row c row = [(wrapperMsg1Entry c row).toRaw] := by
  simp [sha2Message1Bus_row, wrapperMsg1Entry,
    Sha2MainWrapperMsg1Entry.toRaw,
    Vector.toList_ofFn,
    List.range, range_loop_thirtytwo]

@[simp] lemma sha2Message2Bus_row_eq_wrapperBus_row
    (c : C F ExtF) (row : ℕ) :
    sha2Message2Bus_row c row = [(wrapperMsg2Entry c row).toRaw] := by
  simp [sha2Message2Bus_row, wrapperMsg2Entry,
    Sha2MainWrapperMsg2Entry.toRaw,
    Vector.toList_ofFn,
    List.range, range_loop_thirtytwo]

@[simp] lemma sha2Bus_row_eq_wrapperBus_row
    (c : C F ExtF) (row : ℕ) :
    sha2Bus_row c row = wrapperBus_row c row := by
  simp [sha2Bus_row, wrapperBus_row]

end interaction_views

section extraction_bridge

variable {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]

@[Sha2MainAir_Sha256Config_air_simplification]
lemma executionBus_trace_of_extraction
    (c : C F ExtF)
    (h : Sha2MainAir_Sha256Config.extraction.constrain_interactions c) :
    Circuit.buses c Sha2MainExecutionBus = executionBus_trace c := by
  unfold Sha2MainAir_Sha256Config.extraction.constrain_interactions at h
  have hbus := congrArg (fun buses => buses Sha2MainExecutionBus) h
  simpa [Sha2MainExecutionBus, executionBus_trace, executionBus_row] using hbus

@[Sha2MainAir_Sha256Config_air_simplification]
lemma programBus_trace_of_extraction
    (c : C F ExtF)
    (h : Sha2MainAir_Sha256Config.extraction.constrain_interactions c) :
    Circuit.buses c Sha2MainProgramBus = programBus_trace c := by
  unfold Sha2MainAir_Sha256Config.extraction.constrain_interactions at h
  have hbus := congrArg (fun buses => buses Sha2MainProgramBus) h
  simpa [Sha2MainProgramBus, programBus_trace, programBus_row] using hbus

@[Sha2MainAir_Sha256Config_air_simplification]
lemma bitwiseLookupBus_trace_of_extraction
    (c : C F ExtF)
    (h : Sha2MainAir_Sha256Config.extraction.constrain_interactions c) :
    Circuit.buses c Sha2MainBitwiseBus = bitwiseLookupBus_trace c := by
  unfold Sha2MainAir_Sha256Config.extraction.constrain_interactions at h
  have hbus := congrArg (fun buses => buses Sha2MainBitwiseBus) h
  simpa [Sha2MainBitwiseBus, bitwiseLookupBus_trace, bitwiseLookupBus_row] using hbus

@[Sha2MainAir_Sha256Config_air_simplification]
lemma wrapperBus_trace_of_extraction
    (c : C F ExtF)
    (h : Sha2MainAir_Sha256Config.extraction.constrain_interactions c) :
    Circuit.buses c Sha2MainWrapperBus = wrapperBus_trace c := by
  unfold Sha2MainAir_Sha256Config.extraction.constrain_interactions at h
  have hbus := congrArg (fun buses => buses Sha2MainWrapperBus) h
  have hraw : Circuit.buses c Sha2MainWrapperBus =
      (List.range (Circuit.last_row c + 1)).flatMap (sha2Bus_row c) := by
    simpa [Sha2MainWrapperBus, sha2Bus_row, sha2StateBus_row, sha2Message1Bus_row,
      sha2Message2Bus_row, is_enabled, request_id, prev_state_u16, prev_state_byte,
      new_state_byte, message_byte, List.range, range_loop_sixteen,
      range_loop_thirtytwo, add_comm] using hbus
  simp only [show sha2Bus_row c = wrapperBus_row c from
    funext (sha2Bus_row_eq_wrapperBus_row c)] at hraw
  exact hraw

end extraction_bridge

end Sha2MainAir_sha256.constraints
