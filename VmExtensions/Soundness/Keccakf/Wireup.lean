/-
  Concrete shared theorem targets for the Keccakf sub-AIR soundness surface.

  Defines contract predicates and theorem targets for `KeccakfOpAir`,
  `KeccakfPermAir`, the cross-AIR bus pairing, and the spec-facing row target.

  All opcode-side definitions are column-native: they reference
  `inputOfColumns`, `outputOfColumns`, `rdPtrOfColumns`, `preMsgOfColumns`,
  and `postMsgOfColumns` directly.

  This file declares theorem targets; proofs live in specialized modules.

  Permutation-side message views (`blockPreMsg`, `blockPostMsg`) are column-native:
  constructed from export-row column values in `KeccakfPermAirViews.lean`, not
  from stored witness fields.
-/
import VmExtensions.Airs.KeccakfOpAir
import VmExtensions.Airs.KeccakfOpAirViews
import VmExtensions.Airs.KeccakfPermAirViews
import VmExtensions.Constraints.KeccakfOpAir
import OpenvmFv.Fundamentals.BabyBear

set_option autoImplicit false

namespace Keccakf.Soundness

open Keccakf.Interface
open KeccakfOpAir
open KeccakfOpAir.Views
open KeccakfOpAir.constraints
open KeccakfPermAir
open KeccakfPermAir.constraints

/-! ## Opcode-side row contract -/

/-- Column-native row-local opcode contract.
    Packages `RowLocalFacts` together with the semantic decode links between
    the row's pre/post message states and the spec-level preimage/postimage.
    All fields reference column-derived views directly. -/
def KeccakfOpRowLocalContract
    {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) (row : ℕ) : Prop :=
  RowLocalFacts
      (inputOfColumns decodeBusState air row)
      (outputOfColumns decodeBusState air row)
      (rdPtrOfColumns air row)
      (preMsgOfColumns air row)
      (postMsgOfColumns air row)
    ∧ (inputOfColumns decodeBusState air row).preimage =
        decodeBusState (preMsgOfColumns air row).state
    ∧ (outputOfColumns decodeBusState air row).postimage =
        decodeBusState (postMsgOfColumns air row).state

/-- Top-level opcode AIR property: every bounded row is disabled or satisfies
    the row contract. -/
def KeccakfOpAirProperty
    {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF) : Prop :=
  ∀ row, row ≤ air.last_row →
    is_valid air row = 0 ∨ KeccakfOpRowLocalContract air row

/-! ## Permutation-side block contract

The perm-side contract uses column-native message views (`blockPreMsg`,
`blockPostMsg`) from `KeccakfPermAirViews.lean`. These construct `KeccakStateMsg`
objects directly from export-row column values (preimage/output columns + timestamp).

### `BlockLocalFacts` instantiation proof path
- `pre_flag`: `rfl` (blockPreMsg hardcodes `isPost := false`)
- `post_flag`: `rfl` (blockPostMsg hardcodes `isPost := true`)
- `same_timestamp`: `rfl` (both views read the same timestamp column)
- `timestamp_lt`: derived from op-side execution bus axioms + logup payload
  equality at the composition level
- `layout`: `exportedBlockLayout` from the AIR surface

These two proof paths are independent: `BlockLocalFacts` needs composition-level
facts; `BlockBusMatch` needs `export_flag = 1` and
`wf_propertiesToAssumePerPermBlock`.
-/

/-- Concrete exported-block permutation contract.
    Packages `BlockLocalFacts` together with the semantic permutation relation
    over the block's column-native pre/post message states.
    `blockPreMsg`/`blockPostMsg` are column-native views from
    `KeccakfPermAirViews.lean`, constructed from export-row columns. -/
def KeccakfPermBlockContract
    {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfPermAir FBB ExtF)
    (block : ℕ) : Prop :=
  BlockLocalFacts (air.1.blockStartRow block) (air.1.blockExportRow block) air.1.last_row
    (blockPreMsg air block) (blockPostMsg air block)
  ∧ BusKeccakPermutes (blockPreMsg air block).state (blockPostMsg air block).state

/-- Top-level permutation AIR property: every exported block satisfies BusKeccakPermutes.
    `KeccakfPermBlockContract` (which also includes `BlockLocalFacts`) remains as a
    documentation definition but is no longer the per-AIR theorem target.
    The composition level supplies `BlockLocalFacts` facts (timestamp, export_flag)
    via cross-AIR bus protocol, not via per-AIR `isValid`. -/
def KeccakfPermBlockProperty
    {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfPermAir FBB ExtF) : Prop :=
  ∀ block, air.1.isExportedBlock block →
    BusKeccakPermutes (blockPreMsg air block).state (blockPostMsg air block).state

/-! ## Row-native permutation-side property -/

/-- Row-native permutation AIR property: every row with `export_flag = 1`
    satisfies BusKeccakPermutes.
    This is the row-native analogue of `KeccakfPermBlockProperty` that avoids
    the structural `isExportedBlock` layer. -/
def KeccakfPermRowProperty
    {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfPermAir FBB ExtF) : Prop :=
  ∀ row, row ≤ air.last_row → export_flag air row = 1 →
    BusKeccakPermutes (rowPreMsg air row).state (rowPostMsg air row).state

/-! ## Cross-AIR bus pairing targets -/

/-- Column-native shared message-level pairing between opcode rows and
    permutation blocks.  For every enabled opcode row (within bounds), there
    exists an exported permutation block with matching pre and post messages.
    Op-side uses `preMsgOfColumns`/`postMsgOfColumns`; perm-side uses
    column-native `blockPreMsg`/`blockPostMsg` from `KeccakfPermAirViews.lean`. -/
def KeccakStateBusPairing
    {ExtF : Type} [Field ExtF]
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF) : Prop :=
  ∀ row, row ≤ opAir.last_row → is_valid opAir row = 1 →
    ∃ block, permAir.1.isExportedBlock block
      ∧ preMsgOfColumns opAir row = blockPreMsg permAir block
      ∧ postMsgOfColumns opAir row = blockPostMsg permAir block

/-- Row-native shared message-level pairing between opcode rows and
    permutation rows.  For every enabled opcode row (within bounds), there
    exists a perm row with `export_flag = 1` and matching pre/post messages.
    Avoids the structural `isExportedBlock` layer entirely. -/
def KeccakStateBusRowPairing
    {ExtF : Type} [Field ExtF]
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (permAir : Valid_KeccakfPermAir FBB ExtF) : Prop :=
  ∀ row, row ≤ opAir.last_row → is_valid opAir row = 1 →
    ∃ permRow, permRow ≤ permAir.last_row
      ∧ export_flag permAir permRow = 1
      ∧ preMsgOfColumns opAir row = rowPreMsg permAir permRow
      ∧ postMsgOfColumns opAir row = rowPostMsg permAir permRow

/-! ## Spec-facing row target -/

/-- Column-native spec-facing row target: the opcode row's output equals the
    pure `KeccakfOp.Spec.execute` of its input.  Any enabled-row premise
    belongs in the theorem that proves it, not in this definition. -/
def keccakf_row_matches_spec
    {ExtF : Type} [Field ExtF]
    (air : Valid_KeccakfOpAir FBB ExtF)
    (row : ℕ) : Prop :=
  outputOfColumns decodeBusState air row =
    KeccakfOp.Spec.execute (inputOfColumns decodeBusState air row)

end Keccakf.Soundness
