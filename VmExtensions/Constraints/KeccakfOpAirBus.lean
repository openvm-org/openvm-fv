import VmExtensions.Airs.KeccakfOpAir
import VmExtensions.Airs.KeccakfOpAirViews
import VmExtensions.Extraction.KeccakfOpAir
import VmExtensions.Constraints.KeccakfOpAir
import VmExtensions.Constraints.KeccakfStateBus
import OpenvmFv.Fundamentals.Interaction

set_option linter.all false
set_option maxHeartbeats 800000

namespace KeccakfOpAir.constraints

open KeccakfOpAir.constraints
open KeccakfOpAir.Views

/-!
# KeccakfOpAir Bus Interactions

Six buses:
- Bus 0 (ExecutionBus): 2 entries — receive (pc, timestamp), send (pc+4, timestamp+51)
- Bus 1 (MemoryBus): 102 entries — 1 rd read (2) + 50 buffer word read+write pairs (100)
- Bus 2 (ProgramBus): 1 entry — opcode 784 (KECCAKF)
- Bus 3 (RangeTupleCheckerBus): 102 entries — 51 timestamp checks × 2 range checks each
- Bus 6 (BitwiseOperationLookupBus): 101 entries — 1 ptr range check + 100 postimage byte pair checks
- Bus 7 (KeccakfStateBus): 2 entries — pre-state and post-state sends (102 fields each)
-/

-- Bus IDs
def ExecutionBus : ℕ := 0
def MemoryBus : ℕ := 1
def ProgramBus : ℕ := 2
def RangeTupleCheckerBus : ℕ := 3
def BitwiseOperationLookupBus : ℕ := 6
def KeccakfStateBus : ℕ := 7

variable {F ExtF : Type} [Field F] [Field ExtF]

-- Helper: combined buffer pointer from 4 byte-limbs (little-endian u32)
abbrev buffer_ptr (air : Valid_KeccakfOpAir F ExtF) (row : ℕ) : F :=
  buffer_ptr_limb_0 air row + buffer_ptr_limb_1 air row * 256 +
  buffer_ptr_limb_2 air row * 65536 + buffer_ptr_limb_3 air row * 16777216

-- Bus 0: ExecutionBus (2 entries per row)
def executionBus_row (air : Valid_KeccakfOpAir F ExtF) (row : ℕ) : List (F × List F) :=
  [ (-(is_valid air row),
     [pc air row, timestamp air row]),
    (is_valid air row,
     [pc air row + 4, timestamp air row + 51]) ]

-- Bus 2: ProgramBus (1 entry per row)
def programBus_row (air : Valid_KeccakfOpAir F ExtF) (row : ℕ) : List (F × List F) :=
  [ (is_valid air row,
     [pc air row, 784, rd_ptr air row, 0, 0, 1, 2, 0, 0]) ]

-- Bus 1: MemoryBus (102 entries per row)
-- Entry 0-1: rd register read (address space 1, 4 data limbs = buffer_ptr_limbs)
-- Entries 2+2k, 3+2k for k=0..49: buffer word read+write pairs (address space 2)
--   Read: preimage bytes, timestamp = buf_aux_k_prev_ts
--   Write: postimage bytes, timestamp = timestamp + (k+1)
def memoryBus_row (air : Valid_KeccakfOpAir F ExtF) (row : ℕ) : List (F × List F) :=
  -- rd register read pair
  [ (-(is_valid air row),
     [1, rd_ptr air row, buffer_ptr_limb_0 air row, buffer_ptr_limb_1 air row,
      buffer_ptr_limb_2 air row, buffer_ptr_limb_3 air row, rd_aux_prev_ts air row]),
    (is_valid air row,
     [1, rd_ptr air row, buffer_ptr_limb_0 air row, buffer_ptr_limb_1 air row,
      buffer_ptr_limb_2 air row, buffer_ptr_limb_3 air row, timestamp air row]) ] ++
  -- 50 buffer word read+write pairs
  (List.range 50).flatMap (fun k =>
    [ (-(is_valid air row),
       [2, buffer_ptr air row + ((4 * k : ℕ) : F),
        preimage air row (4 * k), preimage air row (4 * k + 1),
        preimage air row (4 * k + 2), preimage air row (4 * k + 3),
        buf_aux_prev_ts air row k]),
      (is_valid air row,
       [2, buffer_ptr air row + ((4 * k : ℕ) : F),
        postimage air row (4 * k), postimage air row (4 * k + 1),
        postimage air row (4 * k + 2), postimage air row (4 * k + 3),
        timestamp air row + ((k + 1 : ℕ) : F)]) ])

-- Bus 3: RangeTupleCheckerBus (102 entries per row)
-- 51 pairs: rd_aux + 50 buf_aux, each pair range-checks (lower_decomp_0, 17) and (lower_decomp_1, 12)
def rangeTupleCheckerBus_row (air : Valid_KeccakfOpAir F ExtF) (row : ℕ) : List (F × List F) :=
  -- rd_aux range checks
  [ (is_valid air row, [rd_aux_lower_decomp_0 air row, 17]),
    (is_valid air row, [rd_aux_lower_decomp_1 air row, 12]) ] ++
  -- 50 buf_aux range checks
  (List.range 50).flatMap (fun k =>
    [ (is_valid air row, [buf_aux_lower_decomp_0 air row k, 17]),
      (is_valid air row, [buf_aux_lower_decomp_1 air row k, 12]) ])

-- Bus 6: BitwiseOperationLookupBus (101 entries per row)
-- Entry 0: buffer_ptr_limb_3 range check (check limb_3 < 32 via 8*limb_3 < 256)
-- Entries 1-100: postimage byte pair range checks
def bitwiseBus_row (air : Valid_KeccakfOpAir F ExtF) (row : ℕ) : List (F × List F) :=
  -- ptr limb_3 range check
  [ (is_valid air row,
     [buffer_ptr_limb_3 air row * 8, buffer_ptr_limb_3 air row * 8, 0, 0]) ] ++
  -- 100 postimage byte pair range checks
  (List.range 100).map (fun k =>
    (is_valid air row,
     [postimage air row (2 * k), postimage air row (2 * k + 1), 0, 0]))

/-!
# Bus-derived axioms

These facts are established by the logup argument (bus interaction protocol).
The logup proof is handled separately; here we axiomatize the per-row consequences.
-/

-- Range check bus assumes: all range-checked values are within their bounds
structure RangeCheckAssume (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop where
  rd_aux_lo_bound : ∃ n : ℕ, rd_aux_lower_decomp_0 air row = ↑n ∧ n < 2^17
  rd_aux_hi_bound : ∃ n : ℕ, rd_aux_lower_decomp_1 air row = ↑n ∧ n < 2^12
  buf_aux_lo_bound : ∀ k, k < 50 → ∃ n : ℕ, buf_aux_lower_decomp_0 air row k = ↑n ∧ n < 2^17
  buf_aux_hi_bound : ∀ k, k < 50 → ∃ n : ℕ, buf_aux_lower_decomp_1 air row k = ↑n ∧ n < 2^12

-- Bitwise bus assumes: all byte pair values are indeed bytes
structure BitwiseAssume (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop where
  ptr_limb3_bound : ∃ n : ℕ, buffer_ptr_limb_3 air row = ↑n ∧ n < 32
  postimage_byte_bound : ∀ k, k < 200 → ∃ n : ℕ, postimage air row k = ↑n ∧ n < 256

-- Memory bus assume-side: bounds on data read from memory
-- These come from the logup argument guaranteeing that the memory bus reads are well-formed.
structure MemoryReadAssume (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop where
  rd_ptr_bound : (rd_ptr air row).val < 2^29
  buf_limb_0_byte : (buffer_ptr_limb_0 air row).val < 256
  buf_limb_1_byte : (buffer_ptr_limb_1 air row).val < 256
  buf_limb_2_byte : (buffer_ptr_limb_2 air row).val < 256
  buf_limb_3_byte : (buffer_ptr_limb_3 air row).val < 256
  buf_ptr_k_bound : ∀ k, k < 50 → (buffer_ptr air row + ((4 * k : ℕ) : FBB)).val < 2^29
  preimage_byte_bound : ∀ k, k < 200 → (preimage air row k).val < 256

/-! ## Typed bus rows

Typed bus row definitions using the framework's bus entry types.
These mirror the raw bus rows but use structured types instead of `(F × List F)`.
All typed rows are FBB-specialized (required for BusEntry instances).
-/

-- ExecutionBus typed row (2 entries)
def _executionBus_row (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List (Interaction.ExecutionBusEntry FBB) :=
  [ ⟨-(is_valid air row), pc air row, timestamp air row⟩,
    ⟨is_valid air row, pc air row + 4, timestamp air row + 51⟩ ]

-- ProgramBus typed row (1 entry)
def _programBus_row (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List (Interaction.ProgramBusEntry FBB) :=
  [ ⟨is_valid air row, pc air row, 784, rd_ptr air row, 0, 0, 1, 2, 0, 0⟩ ]

-- MemoryBus typed rows (102 entries: 2 rd + 100 buffer)
def _memoryBus_rd_pair (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List (Interaction.MemoryBusEntry FBB) :=
  [ ⟨-(is_valid air row), 1, rd_ptr air row,
     buffer_ptr_limb_0 air row, buffer_ptr_limb_1 air row,
     buffer_ptr_limb_2 air row, buffer_ptr_limb_3 air row,
     rd_aux_prev_ts air row⟩,
    ⟨is_valid air row, 1, rd_ptr air row,
     buffer_ptr_limb_0 air row, buffer_ptr_limb_1 air row,
     buffer_ptr_limb_2 air row, buffer_ptr_limb_3 air row,
     timestamp air row⟩ ]

def _memoryBus_buf_pair (air : Valid_KeccakfOpAir FBB ExtF) (row k : ℕ) :
    List (Interaction.MemoryBusEntry FBB) :=
  [ ⟨-(is_valid air row), 2, buffer_ptr air row + ((4 * k : ℕ) : FBB),
     preimage air row (4 * k), preimage air row (4 * k + 1),
     preimage air row (4 * k + 2), preimage air row (4 * k + 3),
     buf_aux_prev_ts air row k⟩,
    ⟨is_valid air row, 2, buffer_ptr air row + ((4 * k : ℕ) : FBB),
     postimage air row (4 * k), postimage air row (4 * k + 1),
     postimage air row (4 * k + 2), postimage air row (4 * k + 3),
     timestamp air row + ((k + 1 : ℕ) : FBB)⟩ ]

def _memoryBus_row (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List (Interaction.MemoryBusEntry FBB) :=
  _memoryBus_rd_pair air row ++ (List.range 50).flatMap (_memoryBus_buf_pair air row)

-- RangeCheckerBus typed rows (102 entries: 2 rd + 100 buffer)
def _rangeCheckerBus_rd_pair (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List (Interaction.RangeCheckerBusEntry FBB) :=
  [ ⟨is_valid air row, rd_aux_lower_decomp_0 air row, 17⟩,
    ⟨is_valid air row, rd_aux_lower_decomp_1 air row, 12⟩ ]

def _rangeCheckerBus_buf_pair (air : Valid_KeccakfOpAir FBB ExtF) (row k : ℕ) :
    List (Interaction.RangeCheckerBusEntry FBB) :=
  [ ⟨is_valid air row, buf_aux_lower_decomp_0 air row k, 17⟩,
    ⟨is_valid air row, buf_aux_lower_decomp_1 air row k, 12⟩ ]

def _rangeCheckerBus_row (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List (Interaction.RangeCheckerBusEntry FBB) :=
  _rangeCheckerBus_rd_pair air row ++ (List.range 50).flatMap (_rangeCheckerBus_buf_pair air row)

-- BitwiseBus typed rows (101 entries: 1 ptr + 100 postimage pairs)
def _bitwiseBus_ptr_entry (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    Interaction.BitwiseBusEntry FBB :=
  ⟨is_valid air row, buffer_ptr_limb_3 air row * 8, buffer_ptr_limb_3 air row * 8, 0, 0⟩

def _bitwiseBus_postimage_entry (air : Valid_KeccakfOpAir FBB ExtF) (row k : ℕ) :
    Interaction.BitwiseBusEntry FBB :=
  ⟨is_valid air row, postimage air row (2 * k), postimage air row (2 * k + 1), 0, 0⟩

def _bitwiseBus_row (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List (Interaction.BitwiseBusEntry FBB) :=
  [_bitwiseBus_ptr_entry air row] ++ (List.range 100).map (_bitwiseBus_postimage_entry air row)

-- KeccakfStateBus typed rows (2 entries: preimage + postimage), reusing the
-- shared keccak state-bus payload format from `VmExtensions/Constraints/KeccakfStateBus.lean`.
noncomputable def _keccakfStateBus_pre_entry
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    Interaction.KeccakfStateBusEntry FBB :=
  { multiplicity := is_valid air row
    payload := Keccakf.constraints.msgPayload (preMsgOfColumns air row) }

noncomputable def _keccakfStateBus_post_entry
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    Interaction.KeccakfStateBusEntry FBB :=
  { multiplicity := is_valid air row
    payload := Keccakf.constraints.msgPayload (postMsgOfColumns air row) }

noncomputable def _keccakfStateBus_row (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    List (Interaction.KeccakfStateBusEntry FBB) :=
  [_keccakfStateBus_pre_entry air row, _keccakfStateBus_post_entry air row]

noncomputable def keccakfStateBus_row (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : List (FBB × List FBB) :=
  (_keccakfStateBus_row air row).map Interaction.BusEntry.serialiseToList

-- Concatenation of all raw bus rows per row (used for multiplicities_zero)
noncomputable def busRow (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : List (FBB × List FBB) :=
  executionBus_row air row ++ memoryBus_row air row ++ programBus_row air row ++
  rangeTupleCheckerBus_row air row ++ bitwiseBus_row air row ++ keccakfStateBus_row air row

-- Aggregated bus row for constrain_interactions
noncomputable def constrain_interactions (air : Valid_KeccakfOpAir FBB ExtF) : Prop :=
  air.buses = fun index ↦
    if index = ExecutionBus then (List.range (air.last_row + 1)).flatMap (executionBus_row air)
    else if index = MemoryBus then (List.range (air.last_row + 1)).flatMap (memoryBus_row air)
    else if index = ProgramBus then (List.range (air.last_row + 1)).flatMap (programBus_row air)
    else if index = RangeTupleCheckerBus then (List.range (air.last_row + 1)).flatMap (rangeTupleCheckerBus_row air)
    else if index = BitwiseOperationLookupBus then (List.range (air.last_row + 1)).flatMap (bitwiseBus_row air)
    else if index = KeccakfStateBus then (List.range (air.last_row + 1)).flatMap (keccakfStateBus_row air)
    else []

/-! ## Generic Bus Entry Helpers -/

@[simp]
def serialiseToList {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) :
    List (FBB × List FBB) :=
  rowData.map (Interaction.BusEntry.serialiseToList)

@[simp]
def axioms {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
  List.Forall id (rowData.map (Interaction.BusEntry.axioms FBB))

@[simp]
def propertiesToAssume {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
  List.Forall id (rowData.map (Interaction.BusEntry.assume FBB))

@[simp]
def propertiesToAssert {α : Type} [Interaction.BusEntry FBB α] (rowData : List α) : Prop :=
  List.Forall id (rowData.map (Interaction.BusEntry.assert FBB))

/-! ## Aggregated Per-Row WF Predicates -/

def axiomsPerRow (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop :=
  axioms (_executionBus_row air row) ∧
  axioms (_memoryBus_row air row) ∧
  axioms (_programBus_row air row) ∧
  axioms (_rangeCheckerBus_row air row) ∧
  axioms (_bitwiseBus_row air row) ∧
  axioms (_keccakfStateBus_row air row)

def wf_propertiesToAssumePerRow (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop :=
  propertiesToAssume (_executionBus_row air row) ∧
  propertiesToAssume (_memoryBus_row air row) ∧
  propertiesToAssume (_programBus_row air row) ∧
  propertiesToAssume (_rangeCheckerBus_row air row) ∧
  propertiesToAssume (_bitwiseBus_row air row) ∧
  propertiesToAssume (_keccakfStateBus_row air row)

def wf_propertiesToAssertPerRow (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop :=
  propertiesToAssert (_executionBus_row air row) ∧
  propertiesToAssert (_memoryBus_row air row) ∧
  propertiesToAssert (_programBus_row air row) ∧
  propertiesToAssert (_rangeCheckerBus_row air row) ∧
  propertiesToAssert (_bitwiseBus_row air row) ∧
  propertiesToAssert (_keccakfStateBus_row air row)

/-! ## Raw ↔ typed bus row bridges

Bridges between raw bus rows `(F × List F)` and typed bus rows serialized back.
These connect extraction-level bus definitions to framework-level typed definitions.
-/

lemma executionBus_bridge (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    serialiseToList (_executionBus_row air row) = executionBus_row air row := by
  simp only [serialiseToList, _executionBus_row, executionBus_row,
    Interaction.BusEntry.serialiseToList, List.map]
  rfl

lemma programBus_bridge (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    serialiseToList (_programBus_row air row) = programBus_row air row := by
  simp only [serialiseToList, _programBus_row, programBus_row,
    Interaction.BusEntry.serialiseToList, List.map]
  rfl

-- Per-entry serialisation helpers for buses with flatMap
private lemma rangeChecker_rd_ser (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    (_rangeCheckerBus_rd_pair air row).map (Interaction.BusEntry.serialiseToList) =
    [ (is_valid air row, [rd_aux_lower_decomp_0 air row, 17]),
      (is_valid air row, [rd_aux_lower_decomp_1 air row, 12]) ] := by
  simp only [_rangeCheckerBus_rd_pair, Interaction.BusEntry.serialiseToList, List.map]
  rfl

private lemma rangeChecker_buf_ser (air : Valid_KeccakfOpAir FBB ExtF) (row k : ℕ) :
    (_rangeCheckerBus_buf_pair air row k).map (Interaction.BusEntry.serialiseToList) =
    [ (is_valid air row, [buf_aux_lower_decomp_0 air row k, 17]),
      (is_valid air row, [buf_aux_lower_decomp_1 air row k, 12]) ] := by
  simp only [_rangeCheckerBus_buf_pair, Interaction.BusEntry.serialiseToList, List.map]
  rfl

lemma rangeCheckerBus_bridge (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    serialiseToList (_rangeCheckerBus_row air row) = rangeTupleCheckerBus_row air row := by
  simp only [serialiseToList, _rangeCheckerBus_row, rangeTupleCheckerBus_row,
    List.map_append, List.map_flatMap]
  congr 1

private lemma memory_rd_ser (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    (_memoryBus_rd_pair air row).map (Interaction.BusEntry.serialiseToList) =
    [ (-(is_valid air row),
       [1, rd_ptr air row, buffer_ptr_limb_0 air row, buffer_ptr_limb_1 air row,
        buffer_ptr_limb_2 air row, buffer_ptr_limb_3 air row, rd_aux_prev_ts air row]),
      (is_valid air row,
       [1, rd_ptr air row, buffer_ptr_limb_0 air row, buffer_ptr_limb_1 air row,
        buffer_ptr_limb_2 air row, buffer_ptr_limb_3 air row, timestamp air row]) ] := by
  simp only [_memoryBus_rd_pair, Interaction.BusEntry.serialiseToList, List.map]
  rfl

private lemma memory_buf_ser (air : Valid_KeccakfOpAir FBB ExtF) (row k : ℕ) :
    (_memoryBus_buf_pair air row k).map (Interaction.BusEntry.serialiseToList) =
    [ (-(is_valid air row),
       [2, buffer_ptr air row + ((4 * k : ℕ) : FBB),
        preimage air row (4 * k), preimage air row (4 * k + 1),
        preimage air row (4 * k + 2), preimage air row (4 * k + 3),
        buf_aux_prev_ts air row k]),
      (is_valid air row,
       [2, buffer_ptr air row + ((4 * k : ℕ) : FBB),
        postimage air row (4 * k), postimage air row (4 * k + 1),
        postimage air row (4 * k + 2), postimage air row (4 * k + 3),
        timestamp air row + ((k + 1 : ℕ) : FBB)]) ] := by
  simp only [_memoryBus_buf_pair, Interaction.BusEntry.serialiseToList, List.map]
  rfl

lemma memoryBus_bridge (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    serialiseToList (_memoryBus_row air row) = memoryBus_row air row := by
  simp only [serialiseToList, _memoryBus_row, memoryBus_row,
    List.map_append, List.map_flatMap]
  congr 1

private lemma bitwise_ptr_ser (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    Interaction.BusEntry.serialiseToList (_bitwiseBus_ptr_entry air row) =
    (is_valid air row,
     [buffer_ptr_limb_3 air row * 8, buffer_ptr_limb_3 air row * 8, 0, 0]) := by
  simp only [_bitwiseBus_ptr_entry, Interaction.BusEntry.serialiseToList]
  rfl

private lemma bitwise_postimage_ser (air : Valid_KeccakfOpAir FBB ExtF) (row k : ℕ) :
    Interaction.BusEntry.serialiseToList (_bitwiseBus_postimage_entry air row k) =
    (is_valid air row,
     [postimage air row (2 * k), postimage air row (2 * k + 1), 0, 0]) := by
  simp only [_bitwiseBus_postimage_entry, Interaction.BusEntry.serialiseToList]
  rfl

lemma bitwiseBus_bridge (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    serialiseToList (_bitwiseBus_row air row) = bitwiseBus_row air row := by
  simp only [serialiseToList, _bitwiseBus_row, bitwiseBus_row,
    List.map_append, List.map_cons, List.map_nil, List.map_map]
  congr 1

lemma keccakfStateBus_bridge (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) :
    serialiseToList (_keccakfStateBus_row air row) = keccakfStateBus_row air row := by
  rfl

end KeccakfOpAir.constraints
