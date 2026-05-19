/-
  Block-level soundness.

  Proves BusKeccakPermutes for each exported block from constraints alone.
  The per-AIR target is just BusKeccakPermutes (not the full
  KeccakfPermBlockContract which also includes BlockLocalFacts — that is now
  supplied at the composition level). Uses:
  - exportedBlockLayout (KeccakfPermAir.lean)
  - preimage_persists (PreimagePersistence.lean)
  - block_24_rounds (BlockComposition.lean)
  - pre_state_bridge, post_state_bridge (StateBridge.lean)
  - spongeToState/stateToSponge roundtrip (proved here)
-/
import VmExtensions.Soundness.KeccakfPermAir.BlockComposition
import VmExtensions.Soundness.KeccakfPermAir.PreimagePersistence
import VmExtensions.Soundness.KeccakfPermAir.StateBridge
import VmExtensions.Soundness.KeccakfPermAir.BusFacts
import VmExtensions.Soundness.Keccakf.Wireup

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfPermAir.Soundness.BlockSoundness

open KeccakfPermAir.constraints
open KeccakfPermAir.Soundness
open KeccakfPermAir.Soundness.StateBridge
open Keccakf.Interface
open Keccakf.Soundness
open Keccak
open BabyBear

variable {ExtF : Type} [Field ExtF]

/-! ## Spec-level roundtrip: spongeToState (stateToSponge st) = st

The lane→byte→lane conversion is lossless. Extracting 8 bytes from a u64
lane via laneGetByte and reassembling via spongeToLane recovers the
original lane value. This bitvector identity lifts to a full State roundtrip.
-/

-- Per-lane bitvector roundtrip: extract 8 bytes via laneGetByte and re-pack = identity.
-- Kernel-checked proof: per-bit equality via getLsbD + interval_cases on the 64 bit positions.
-- No bv_decide — avoids Lean.ofReduceBool/Lean.trustCompiler axioms.
set_option maxHeartbeats 3200000 in
private theorem lane_byte_roundtrip (v : UInt64) :
    (laneGetByte v 7).toUInt64 <<< 56 |||
    (laneGetByte v 6).toUInt64 <<< 48 |||
    (laneGetByte v 5).toUInt64 <<< 40 |||
    (laneGetByte v 4).toUInt64 <<< 32 |||
    (laneGetByte v 3).toUInt64 <<< 24 |||
    (laneGetByte v 2).toUInt64 <<< 16 |||
    (laneGetByte v 1).toUInt64 <<< 8 |||
    (laneGetByte v 0).toUInt64 = v := by
  cases v with | ofBitVec bv => ?_
  apply congrArg UInt64.ofBitVec
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [laneGetByte, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
    UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft]
  interval_cases i <;> simp_all

-- Per-lane roundtrip: spongeToLane (stateToSponge st) j recovers lane j of st.
-- Proof: unfold spongeToLane's 8 byte accesses, simplify the SpongeState indexing
-- to laneGetByte terms, then apply the bitvector roundtrip.
set_option maxHeartbeats 800000 in
private theorem spongeToLane_stateToSponge (st : State) (j : Fin 25) :
    spongeToLane (stateToSponge st) j =
      st.val[j.val]'(by have := st.2; omega) := by
  simp only [spongeToLane, stateToSponge]
  -- Unfold SpongeState and ByteArray subscript chains to Array.ofFn elements
  dsimp only [GetElem.getElem]
  simp [ByteArray.get]
  -- Simplify (8 * j + k) / 8 = j for k = 1..7 (k=0 already reduced)
  simp only [show ∀ n, (8 * n + 7) / 8 = n from fun n => by omega,
    show ∀ n, (8 * n + 6) / 8 = n from fun n => by omega,
    show ∀ n, (8 * n + 5) / 8 = n from fun n => by omega,
    show ∀ n, (8 * n + 4) / 8 = n from fun n => by omega,
    show ∀ n, (8 * n + 3) / 8 = n from fun n => by omega,
    show ∀ n, (8 * n + 2) / 8 = n from fun n => by omega,
    show ∀ n, (8 * n + 1) / 8 = n from fun n => by omega]
  -- All byte accesses now read from lane j; apply the bitvector roundtrip
  exact lane_byte_roundtrip _

-- Full state-level roundtrip: lane→byte→lane conversion is the identity on State.
private theorem spongeToState_stateToSponge (st : State) :
    spongeToState (stateToSponge st) = st := by
  apply Subtype.ext
  simp only [spongeToState]
  apply Array.ext
  · simp [st.2]
  · intro j h₁ h₂
    simp only [Array.size_ofFn] at h₁
    simp only [Array.getElem_ofFn]
    exact spongeToLane_stateToSponge st ⟨j, h₁⟩

/-! ## Row-Indexed BusKeccakPermutes

Composition chain (row-indexed):
1. post_state_bridge_row: decodeBusState(rowPostMsg.state) = stateToSponge(rowOutputState exportRow)
2. layout: exportRow = startRow + 23
3. rounds_24_row: rowOutputState(startRow + 23) = keccakP(rowInputState(startRow))
4. pre_state_bridge_row: decodeBusState(rowPreMsg.state) = stateToSponge(rowInputState(startRow))
5. keccakF definition + spongeToState_stateToSponge roundtrip
-/

theorem busKeccakPermutes_row
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    {startRow exportRow : ℕ}
    (h_layout : BlockLayoutFacts startRow exportRow air.last_row)
    (h_persist : ∀ i, i < 100 →
      preimage air i exportRow = a air i startRow) :
    BusKeccakPermutes (rowPreMsg air exportRow).state
      (rowPostMsg air exportRow).state := by
  have h_rowE : exportRow = startRow + 23 := by
    have := h_layout.export_row_eq
    simp only [EXPORT_ROW_OFFSET, BLOCK_ROWS] at this; omega
  subst h_rowE
  unfold BusKeccakPermutes
  rw [post_state_bridge_row air]
  rw [rounds_24_row h_allHold h_layout]
  rw [pre_state_bridge_row air h_persist]
  unfold keccakF
  rw [spongeToState_stateToSponge]

/-! ## Block-Indexed Wrappers -/

private theorem busKeccakPermutes
    {air : Valid_KeccakfPermAir FBB ExtF}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    {block : ℕ}
    (h_layout : BlockLayoutFacts (air.blockStartRow block)
        (air.blockExportRow block) air.last_row)
    (h_persist : ∀ i, i < 100 →
      preimage air i (air.blockExportRow block) =
        a air i (air.blockStartRow block)) :
    BusKeccakPermutes (blockPreMsg air block).state
      (blockPostMsg air block).state := by
  rw [blockPreMsg_eq_rowPreMsg, blockPostMsg_eq_rowPostMsg]
  exact busKeccakPermutes_row h_allHold h_layout h_persist

/-! ## Main theorem: block_contract

For each exported block, BusKeccakPermutes holds: the perm-side output state
is the keccak-f permutation of the input state.
BlockLocalFacts is no longer part of the per-AIR target; composition supplies it.
-/

-- Per-block BusKeccakPermutes from constraints alone (no bus wf assumptions needed).
theorem block_contract
    {air : Valid_KeccakfPermAir FBB ExtF} {block : ℕ}
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row)
    (h_exported : air.isExportedBlock block) :
    BusKeccakPermutes (blockPreMsg air block).state
      (blockPostMsg air block).state := by
  have h_layout := air.exportedBlockLayout h_exported
  -- Derive preimage persistence at the export row from preimage_persists
  have h_persist : ∀ i, i < 100 →
      preimage air i (air.blockExportRow block) =
        a air i (air.blockStartRow block) := by
    intro i hi
    have h_rowE : air.blockExportRow block = air.blockStartRow block + 23 := by
      have := h_layout.export_row_eq
      simp only [EXPORT_ROW_OFFSET, BLOCK_ROWS] at this; omega
    rw [h_rowE]
    exact preimage_persists h_allHold h_layout hi _ (by omega) (by omega)
  exact busKeccakPermutes h_allHold h_layout h_persist

/-! ## Top-level theorem

Thin wrapper over block_contract — quantify over exported blocks.
-/

-- Every exported block in the KeccakfPermAir trace satisfies BusKeccakPermutes.
theorem keccakf_perm_block_soundness
    (air : Valid_KeccakfPermAir FBB ExtF)
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row) :
    KeccakfPermBlockProperty air :=
  fun block h_exported => block_contract h_allHold h_exported

/-! ## Row-native PermAir property

Every row with `export_flag = 1` satisfies BusKeccakPermutes.
-/

theorem keccakf_perm_row_soundness
    (air : Valid_KeccakfPermAir FBB ExtF)
    (h_allHold : ∀ row, row ≤ air.last_row → allHold_simplified air row) :
    Keccakf.Soundness.KeccakfPermRowProperty air := by
  intro row h_row h_ef
  have h_layout := ef_implies_layout h_allHold h_row h_ef
  have h_persist : ∀ i, i < 100 →
      preimage air i row = a air i (row - 23) := by
    intro i hi
    exact preimage_persists_row h_allHold h_layout hi row (by omega) (by omega)
  exact busKeccakPermutes_row h_allHold h_layout h_persist

end KeccakfPermAir.Soundness.BlockSoundness
