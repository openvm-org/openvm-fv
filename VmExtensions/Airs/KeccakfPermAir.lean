/-
  Minimal concrete AIR interface for KeccakfPermAir.

  Defines the structural block-layout fields (`exportedBlocks`, `isExportedBlock`,
  `blockStartRow`, `blockExportRow`) and the predicates `BlockLayoutFacts`
  and `BlockLocalFacts`.

  Column-native message views (`blockPreMsg`, `blockPostMsg`) are defined
  from export-row column values in `KeccakfPermAirViews.lean`.
-/
import LeanZKCircuit.OpenVM.Circuit
import VmExtensions.Soundness.Keccakf.Interface

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfPermAir

open Keccakf.Interface

/-! ## Constants -/

def BLOCK_ROWS : Nat := 24

/-- The row offset from the start of a 24-round Keccak-f block to its export row. -/
def EXPORT_ROW_OFFSET : Nat := BLOCK_ROWS - 1

/-! ## Block layout predicate -/

/-- Named exported-block layout predicate.
    Owns the row-layout facts for an exported block: start-row alignment,
    export-row offset, and export-row within trace bounds. -/
structure BlockLayoutFacts
    (startRow exportRow lastRow : Nat) : Prop where
  start_row_aligned : startRow % BLOCK_ROWS = 0
  export_row_eq : exportRow = startRow + EXPORT_ROW_OFFSET
  export_row_le_last : exportRow ≤ lastRow

/-! ## Block-local fact predicate -/

/-- Named block-local fact bundle for the permutation side.
    Owns the layout, message-normalization obligations, and timestamp bound
    for an exported block. -/
structure BlockLocalFacts
    (startRow exportRow lastRow : Nat)
    (preMsg postMsg : KeccakStateMsg) : Prop where
  layout : BlockLayoutFacts startRow exportRow lastRow
  pre_flag : preMsg.isPost = false
  post_flag : postMsg.isPost = true
  same_timestamp : preMsg.timestamp = postMsg.timestamp
  timestamp_lt : preMsg.timestamp < timestampBound

/-! ## Raw AIR structure -/

/-- Minimal concrete permutation AIR structure.
    Circuit-level fields provide the trace interface; the block-level structural
    fields identify exported blocks and their row layout.

    `isValid` contains only the bus index, block bookkeeping, layout
    alignment/offset/bounds, and rotation consistency. Semantic facts
    (timestamp bound, export_flag = 1, timestamp uniqueness) are proven from
    constraints and bus axioms, not assumed here.

    Column-native message views (`blockPreMsg`, `blockPostMsg`) are defined
    from export-row column values in `KeccakfPermAirViews.lean`. -/
structure Raw_KeccakfPermAir (F : Type) (ExtF : Type) where
  -- Circuit plumbing
  buses (index : ℕ) : List (F × List F)
  keccakStateBusIndex : ℕ
  challenge (index : ℕ) : ExtF
  exposed (index : ℕ) : ExtF
  main (id : ℕ) (column : ℕ) (row : ℕ) (rotation : ℕ) : F
  permutation (column : ℕ) (row : ℕ) (rotation : ℕ) : ExtF
  preprocessed (column : ℕ) (row : ℕ) (rotation : ℕ) : F
  public_values (index : ℕ) : F
  last_row : ℕ
  -- Shared block-level structural surface
  /-- The list of block indices that are exported (carry valid keccak-f results). -/
  exportedBlocks : List ℕ
  /-- Whether a block index is an exported block. -/
  isExportedBlock : ℕ → Prop
  /-- The start row of a given block. -/
  blockStartRow : ℕ → Nat
  /-- The export row of a given block (where the state bus message is emitted). -/
  blockExportRow : ℕ → Nat

-- Circuit instance
instance {F ExtF} [Field F] [Field ExtF] : Circuit F ExtF Raw_KeccakfPermAir where
  buses := Raw_KeccakfPermAir.buses
  challenge := Raw_KeccakfPermAir.challenge
  exposed := Raw_KeccakfPermAir.exposed
  main := Raw_KeccakfPermAir.main
  permutation := Raw_KeccakfPermAir.permutation
  preprocessed := Raw_KeccakfPermAir.preprocessed
  public_values := Raw_KeccakfPermAir.public_values
  last_row := Raw_KeccakfPermAir.last_row

/-! ## Raw column accessors on the AIR -/

-- Timestamp column (col 2633) — raw accessor on Raw_KeccakfPermAir.
def timestamp_col {F ExtF : Type} (c : Raw_KeccakfPermAir F ExtF) (row : ℕ) : F :=
  c.main (id := 0) (column := 2633) (row := row) (rotation := 0)

-- Export flag column (col 24) — raw accessor on Raw_KeccakfPermAir.
def export_flag_col {F ExtF : Type} (c : Raw_KeccakfPermAir F ExtF) (row : ℕ) : F :=
  c.main (id := 0) (column := 24) (row := row) (rotation := 0)

/-! ## Validity predicate -/

-- Semantic facts (timestamp bound, export_flag = 1, timestamp uniqueness)
-- are proven from constraints/bus axioms, not assumed here.
def Raw_KeccakfPermAir.isValid {F ExtF} (c : Raw_KeccakfPermAir F ExtF) : Prop :=
  c.keccakStateBusIndex = 7 ∧
  c.exportedBlocks.Nodup ∧
  (∀ block, c.isExportedBlock block ↔ block ∈ c.exportedBlocks) ∧
  -- Structural layout (instance-free)
  (∀ block, c.isExportedBlock block →
    (c.blockStartRow block) % BLOCK_ROWS = 0 ∧
    c.blockExportRow block = c.blockStartRow block + EXPORT_ROW_OFFSET ∧
    c.blockExportRow block ≤ c.last_row) ∧
  -- Rotation consistency: rotation=1 at row r equals rotation=0 at row r+1
  (∀ id column row, row < c.last_row →
    c.main id column row 1 = c.main id column (row + 1) 0)

/-- Valid KeccakfPermAir: a `Raw_KeccakfPermAir` satisfying `isValid`. -/
abbrev Valid_KeccakfPermAir (F : Type) (ExtF : Type) :=
  { c : Raw_KeccakfPermAir F ExtF // c.isValid }

/-! ## Projections for Valid_KeccakfPermAir -/

abbrev Valid_KeccakfPermAir.buses {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.buses
abbrev Valid_KeccakfPermAir.keccakStateBusIndex {F ExtF}
    (c : Valid_KeccakfPermAir F ExtF) := c.1.keccakStateBusIndex
abbrev Valid_KeccakfPermAir.challenge {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.challenge
abbrev Valid_KeccakfPermAir.exposed {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.exposed
abbrev Valid_KeccakfPermAir.main {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.main
abbrev Valid_KeccakfPermAir.permutation {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.permutation
abbrev Valid_KeccakfPermAir.preprocessed {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.preprocessed
abbrev Valid_KeccakfPermAir.public_values {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.public_values
abbrev Valid_KeccakfPermAir.last_row {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.last_row
abbrev Valid_KeccakfPermAir.exportedBlocks {F ExtF}
    (c : Valid_KeccakfPermAir F ExtF) := c.1.exportedBlocks
abbrev Valid_KeccakfPermAir.isExportedBlock {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.isExportedBlock
abbrev Valid_KeccakfPermAir.blockStartRow {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.blockStartRow
abbrev Valid_KeccakfPermAir.blockExportRow {F ExtF} (c : Valid_KeccakfPermAir F ExtF) := c.1.blockExportRow

/-! ## Validity theorems -/

theorem Valid_KeccakfPermAir.keccakStateBusIndex_eq {F ExtF}
    (c : Valid_KeccakfPermAir F ExtF) :
    c.keccakStateBusIndex = 7 :=
  c.2.1

theorem Valid_KeccakfPermAir.exportedBlocks_nodup {F ExtF}
    (c : Valid_KeccakfPermAir F ExtF) :
    c.exportedBlocks.Nodup :=
  c.2.2.1

theorem Valid_KeccakfPermAir.mem_exportedBlocks_iff {F ExtF}
    (c : Valid_KeccakfPermAir F ExtF) (block : ℕ) :
    c.isExportedBlock block ↔ block ∈ c.exportedBlocks :=
  c.2.2.2.1 block

-- Extracts BlockLayoutFacts (alignment, offset, bounds) from isValid.
-- Layout is the 4th conjunct (.2.2.2.2.1).
theorem Valid_KeccakfPermAir.exportedBlockLayout {F ExtF}
    (c : Valid_KeccakfPermAir F ExtF) {block : ℕ}
    (h_block : c.isExportedBlock block) :
    BlockLayoutFacts (c.blockStartRow block) (c.blockExportRow block) c.last_row := by
  have h := c.2.2.2.2.1 block h_block
  exact ⟨h.1, h.2.1, h.2.2⟩

-- Rotation consistency: rotation=1 at row r equals rotation=0 at row r+1.
-- Encodes the framework invariant that `_next` column accessors read the next row.
theorem Valid_KeccakfPermAir.rotation_consistent {F ExtF}
    (c : Valid_KeccakfPermAir F ExtF)
    {id column row : ℕ} (h : row < c.last_row) :
    c.1.main id column row 1 = c.1.main id column (row + 1) 0 :=
  c.2.2.2.2.2 id column row h

-- Circuit instance for the valid subtype
instance {F ExtF} [Field F] [Field ExtF] : Circuit F ExtF Valid_KeccakfPermAir where
  buses := Valid_KeccakfPermAir.buses
  challenge := Valid_KeccakfPermAir.challenge
  exposed := Valid_KeccakfPermAir.exposed
  main := Valid_KeccakfPermAir.main
  permutation := Valid_KeccakfPermAir.permutation
  preprocessed := Valid_KeccakfPermAir.preprocessed
  public_values := Valid_KeccakfPermAir.public_values
  last_row := Valid_KeccakfPermAir.last_row

end KeccakfPermAir
