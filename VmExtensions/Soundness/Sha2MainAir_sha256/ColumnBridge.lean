import VmExtensions.Soundness.Sha2MainAir_sha256.Permutation

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace Sha2CompressionBridge_sha256

open BabyBear
open Sha2MainAir_sha256.Soundness
open Sha2BlockHasherVmAir_sha256.BlockSpec

section SharedBridge

open Sha2BlockHasherVmAir_sha256.constraints

variable {CMain CBlock : Type → Type → Type} {ExtF : Type}
  [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]

/-- Byte-level bridge at the main-chip column boundary: once the three
main wrapper sends match the block-window wrapper payloads, the row's exposed
state limbs, input bytes, and output bytes agree with the block window
byte-for-byte. -/
def rowBlockColumnAgreementSpec
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ) : Prop :=
  let blockState := Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)
  let blockMsg1 := Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start
  let blockMsg2 := Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)
  (∀ i : Fin 16, Sha2MainAir_sha256.constraints.prev_state_u16 mainAir i.1 row =
      blockState.prev_state_u16.get i) ∧
  (∀ i : Fin 32, Sha2MainAir_sha256.constraints.new_state_byte mainAir i.1 row =
      blockState.new_state_bytes.get i) ∧
  (∀ i : Fin 16, Sha2MainAir_sha256.constraints.message_byte mainAir i.1 row =
      blockMsg1.local_msg_bytes.get i) ∧
  (∀ i : Fin 16, Sha2MainAir_sha256.constraints.message_byte mainAir (16 + i.1) row =
      blockMsg1.next_msg_bytes.get i) ∧
  (∀ i : Fin 16, Sha2MainAir_sha256.constraints.message_byte mainAir (32 + i.1) row =
      blockMsg2.local_msg_bytes.get i) ∧
  ∀ i : Fin 16, Sha2MainAir_sha256.constraints.message_byte mainAir (48 + i.1) row =
      blockMsg2.next_msg_bytes.get i

theorem rowBlockColumnAgreement_of_shared_payload
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hmain : wrapperPayloadSpec mainAir row)
    (hshared : sharedWrapperPayloadSpec mainAir blockAir row start) :
    rowBlockColumnAgreementSpec mainAir blockAir row start := by
  rcases hmain with
    ⟨_, _, _, _, _, _, _, _, _, hmainPrev, hmainNew,
      hmainMsg1Local, hmainMsg1Next, hmainMsg2Local, hmainMsg2Next⟩
  rcases hshared with
    ⟨hstateShared, hwriteShared, hmsg1LocalShared, hmsg1NextShared,
      hmsg2LocalShared, hmsg2NextShared⟩
  unfold rowBlockColumnAgreementSpec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    calc
      Sha2MainAir_sha256.constraints.prev_state_u16 mainAir i.1 row =
          (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).prev_state_u16.get i := by
        symm
        exact hmainPrev i
      _ =
          (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).prev_state_u16.get i :=
          hstateShared i
  · intro i
    calc
      Sha2MainAir_sha256.constraints.new_state_byte mainAir i.1 row =
          (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).new_state_bytes.get i := by
        symm
        exact hmainNew i
      _ =
          (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get i :=
          hwriteShared i
  · intro i
    calc
      Sha2MainAir_sha256.constraints.message_byte mainAir i.1 row =
          (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).local_msg_bytes.get i := by
        symm
        exact hmainMsg1Local i
      _ =
          (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start).local_msg_bytes.get i :=
          hmsg1LocalShared i
  · intro i
    calc
      Sha2MainAir_sha256.constraints.message_byte mainAir (16 + i.1) row =
          (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).next_msg_bytes.get i := by
        symm
        exact hmainMsg1Next i
      _ =
          (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start).next_msg_bytes.get i :=
          hmsg1NextShared i
  · intro i
    calc
      Sha2MainAir_sha256.constraints.message_byte mainAir (32 + i.1) row =
          (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).local_msg_bytes.get i := by
        symm
        exact hmainMsg2Local i
      _ =
          (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)).local_msg_bytes.get i :=
          hmsg2LocalShared i
  · intro i
    calc
      Sha2MainAir_sha256.constraints.message_byte mainAir (48 + i.1) row =
          (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).next_msg_bytes.get i := by
        symm
        exact hmainMsg2Next i
      _ =
          (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)).next_msg_bytes.get i :=
          hmsg2NextShared i

/-- The main row's previous SHA-256 chaining state, reconstructed from the
exposed `prev_state_u16` columns. -/
def rowPrevStateWord
    (mainAir : CMain FBB ExtF) (row : ℕ) (word : Fin 8) : Word :=
  UInt32.ofNat
    ((Sha2MainAir_sha256.constraints.prev_state_u16 mainAir (2 * word.1) row).val +
      (Sha2MainAir_sha256.constraints.prev_state_u16 mainAir (2 * word.1 + 1) row).val * 2 ^ 16)

/-- The main row's written output state, reconstructed word-by-word from the
exposed `new_state_byte` columns. -/
def rowNewStateWord
    (mainAir : CMain FBB ExtF) (row : ℕ) (word : Fin 8) : Word :=
  UInt32.ofNat
    ((Sha2MainAir_sha256.constraints.new_state_byte mainAir (4 * word.1) row).val +
      (Sha2MainAir_sha256.constraints.new_state_byte mainAir (4 * word.1 + 1) row).val * 256 +
      (Sha2MainAir_sha256.constraints.new_state_byte mainAir (4 * word.1 + 2) row).val * 65536 +
      (Sha2MainAir_sha256.constraints.new_state_byte mainAir (4 * word.1 + 3) row).val * 16777216)

/-- Previous chaining state reconstructed from one main-chip row. -/
def rowPrevState (mainAir : CMain FBB ExtF) (row : ℕ) : WorkingVars where
  a := rowPrevStateWord mainAir row ⟨0, by decide⟩
  b := rowPrevStateWord mainAir row ⟨1, by decide⟩
  c := rowPrevStateWord mainAir row ⟨2, by decide⟩
  d := rowPrevStateWord mainAir row ⟨3, by decide⟩
  e := rowPrevStateWord mainAir row ⟨4, by decide⟩
  f := rowPrevStateWord mainAir row ⟨5, by decide⟩
  g := rowPrevStateWord mainAir row ⟨6, by decide⟩
  h := rowPrevStateWord mainAir row ⟨7, by decide⟩

/-- Output chaining state reconstructed from one main-chip row. -/
def rowNewState (mainAir : CMain FBB ExtF) (row : ℕ) : WorkingVars where
  a := rowNewStateWord mainAir row ⟨0, by decide⟩
  b := rowNewStateWord mainAir row ⟨1, by decide⟩
  c := rowNewStateWord mainAir row ⟨2, by decide⟩
  d := rowNewStateWord mainAir row ⟨3, by decide⟩
  e := rowNewStateWord mainAir row ⟨4, by decide⟩
  f := rowNewStateWord mainAir row ⟨5, by decide⟩
  g := rowNewStateWord mainAir row ⟨6, by decide⟩
  h := rowNewStateWord mainAir row ⟨7, by decide⟩

private theorem blockWrapperState_prev_state_u16_get
    (blockAir : CBlock FBB ExtF) (row : ℕ) (word : Fin 8) (limb : Fin 2) :
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir row).prev_state_u16.get
      ⟨2 * word.1 + limb.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha256.constraints.prev_hash blockAir word.1 limb.1 row := by
  fin_cases word <;> fin_cases limb <;>
    simp [Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry]

private theorem blockWrapperState_new_state_bytes_get
    (blockAir : CBlock FBB ExtF) (row : ℕ) (word : Fin 8) (byte : Fin 4) :
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir row).new_state_bytes.get
      ⟨4 * word.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 byte.1 row := by
  fin_cases word <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry]

private theorem rowPrevStateWord_eq_digestPrevHashWord_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 8) :
    rowPrevStateWord mainAir row word = digestPrevHashWord blockAir (start + 16) word.1 := by
  rcases hcols with ⟨hprev, _, _, _, _, _⟩
  unfold rowPrevStateWord
  rw [digestPrevHash_eq_limbs]
  rw [hprev ⟨2 * word.1, by omega⟩, hprev ⟨2 * word.1 + 1, by omega⟩]
  have hwrap0 :
      (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).prev_state_u16.get
        ⟨2 * word.1, by omega⟩ =
          Sha2BlockHasherVmAir_sha256.constraints.prev_hash blockAir word.1 0 (start + 16) := by
    simpa using
      blockWrapperState_prev_state_u16_get blockAir (start + 16) word ⟨0, by decide⟩
  have hwrap1 :
      (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).prev_state_u16.get
        ⟨2 * word.1 + 1, by omega⟩ =
          Sha2BlockHasherVmAir_sha256.constraints.prev_hash blockAir word.1 1 (start + 16) := by
    simpa using
      blockWrapperState_prev_state_u16_get blockAir (start + 16) word ⟨1, by decide⟩
  rw [hwrap0, hwrap1]
  simp [digestPrevHashLo16, digestPrevHashHi16]

private theorem rowPrevState_eq_digestPrevHashState_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start) :
    rowPrevState mainAir row = digestPrevHashState blockAir (start + 16) := by
  rw [rowPrevState, digestPrevHashState, WorkingVars.mk.injEq]
  repeat' constructor
  · simpa using
      rowPrevStateWord_eq_digestPrevHashWord_of_columns mainAir blockAir row start hcols
        ⟨0, by decide⟩
  · simpa using
      rowPrevStateWord_eq_digestPrevHashWord_of_columns mainAir blockAir row start hcols
        ⟨1, by decide⟩
  · simpa using
      rowPrevStateWord_eq_digestPrevHashWord_of_columns mainAir blockAir row start hcols
        ⟨2, by decide⟩
  · simpa using
      rowPrevStateWord_eq_digestPrevHashWord_of_columns mainAir blockAir row start hcols
        ⟨3, by decide⟩
  · simpa using
      rowPrevStateWord_eq_digestPrevHashWord_of_columns mainAir blockAir row start hcols
        ⟨4, by decide⟩
  · simpa using
      rowPrevStateWord_eq_digestPrevHashWord_of_columns mainAir blockAir row start hcols
        ⟨5, by decide⟩
  · simpa using
      rowPrevStateWord_eq_digestPrevHashWord_of_columns mainAir blockAir row start hcols
        ⟨6, by decide⟩
  · simpa using
      rowPrevStateWord_eq_digestPrevHashWord_of_columns mainAir blockAir row start hcols
        ⟨7, by decide⟩

private theorem rowNewStateWord_eq_digestFinalHashWord_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 8) :
    rowNewStateWord mainAir row word = digestFinalHashWord blockAir (start + 16) word.1 := by
  rcases hcols with ⟨_, hnew, _, _, _, _⟩
  unfold rowNewStateWord
  rw [digestFinalHashWord, bytesLEToWord, foldl_range_add_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 :
      Sha2MainAir_sha256.constraints.new_state_byte mainAir (4 * word.1) row =
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get
          ⟨4 * word.1, by omega⟩ := by
    simpa using hnew ⟨4 * word.1, by omega⟩
  have h1 :
      Sha2MainAir_sha256.constraints.new_state_byte mainAir (4 * word.1 + 1) row =
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get
          ⟨4 * word.1 + 1, by omega⟩ := by
    simpa using hnew ⟨4 * word.1 + 1, by omega⟩
  have h2 :
      Sha2MainAir_sha256.constraints.new_state_byte mainAir (4 * word.1 + 2) row =
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get
          ⟨4 * word.1 + 2, by omega⟩ := by
    simpa using hnew ⟨4 * word.1 + 2, by omega⟩
  have h3 :
      Sha2MainAir_sha256.constraints.new_state_byte mainAir (4 * word.1 + 3) row =
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get
          ⟨4 * word.1 + 3, by omega⟩ := by
    simpa using hnew ⟨4 * word.1 + 3, by omega⟩
  have hwrap0 :
      (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get
        ⟨4 * word.1, by omega⟩ =
          Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 0 (start + 16) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 16) word ⟨0, by decide⟩
  have hwrap1 :
      (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get
        ⟨4 * word.1 + 1, by omega⟩ =
          Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 1 (start + 16) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 16) word ⟨1, by decide⟩
  have hwrap2 :
      (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get
        ⟨4 * word.1 + 2, by omega⟩ =
          Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 2 (start + 16) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 16) word ⟨2, by decide⟩
  have hwrap3 :
      (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).new_state_bytes.get
        ⟨4 * word.1 + 3, by omega⟩ =
          Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 3 (start + 16) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 16) word ⟨3, by decide⟩
  rw [h0, h1, h2, h3, hwrap0, hwrap1, hwrap2, hwrap3]
  open scoped UInt32.CommRing in
    change
      (((Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 0 (start + 16)).val +
          (Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 1 (start + 16)).val * 256 +
          (Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 2 (start + 16)).val * 65536 +
          (Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 3 (start + 16)).val * 16777216 : ℕ) :
        UInt32) =
      (((Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 0 (start + 16)).val * 256 ^ 0 +
          (Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 1 (start + 16)).val * 256 ^ 1 +
          (Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 2 (start + 16)).val * 256 ^ 2 +
          (Sha2BlockHasherVmAir_sha256.constraints.final_hash blockAir word.1 3 (start + 16)).val * 256 ^ 3 : ℕ) :
        UInt32)
    norm_num

private theorem rowNewState_eq_digestFinalHashState_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start) :
    rowNewState mainAir row = digestFinalHashState blockAir (start + 16) := by
  rw [rowNewState, digestFinalHashState, WorkingVars.mk.injEq]
  repeat' constructor
  · simpa using
      rowNewStateWord_eq_digestFinalHashWord_of_columns mainAir blockAir row start hcols
        ⟨0, by decide⟩
  · simpa using
      rowNewStateWord_eq_digestFinalHashWord_of_columns mainAir blockAir row start hcols
        ⟨1, by decide⟩
  · simpa using
      rowNewStateWord_eq_digestFinalHashWord_of_columns mainAir blockAir row start hcols
        ⟨2, by decide⟩
  · simpa using
      rowNewStateWord_eq_digestFinalHashWord_of_columns mainAir blockAir row start hcols
        ⟨3, by decide⟩
  · simpa using
      rowNewStateWord_eq_digestFinalHashWord_of_columns mainAir blockAir row start hcols
        ⟨4, by decide⟩
  · simpa using
      rowNewStateWord_eq_digestFinalHashWord_of_columns mainAir blockAir row start hcols
        ⟨5, by decide⟩
  · simpa using
      rowNewStateWord_eq_digestFinalHashWord_of_columns mainAir blockAir row start hcols
        ⟨6, by decide⟩
  · simpa using
      rowNewStateWord_eq_digestFinalHashWord_of_columns mainAir blockAir row start hcols
        ⟨7, by decide⟩

theorem rowBlockCompressionPackage_of_shared_payload
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hmain : wrapperPayloadSpec mainAir row)
    (hshared : sharedWrapperPayloadSpec mainAir blockAir row start)
    (hblock : blockCompressionSpec blockAir start) :
    rowBlockColumnAgreementSpec mainAir blockAir row start ∧
      blockCompressionSpec blockAir start := by
  exact ⟨
    rowBlockColumnAgreement_of_shared_payload mainAir blockAir row start hmain hshared,
    hblock
  ⟩

theorem rowBlockStartState_of_block_package
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hpackage :
      rowBlockColumnAgreementSpec mainAir blockAir row start ∧
        blockCompressionSpec blockAir start) :
    rowBlockColumnAgreementSpec mainAir blockAir row start ∧
      rowPrevState mainAir row = blockStartState blockAir start := by
  rcases hpackage with ⟨hcols, hblock⟩
  rcases hblock with ⟨_, hprevBlock, _⟩
  have hprev :
      rowPrevState mainAir row = blockStartState blockAir start := by
    calc
      rowPrevState mainAir row = digestPrevHashState blockAir (start + 16) :=
        rowPrevState_eq_digestPrevHashState_of_columns mainAir blockAir row start hcols
      _ = blockStartState blockAir start := hprevBlock
  exact ⟨hcols, hprev⟩

theorem rowBlockOutputState_of_block_package
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hpackage :
      rowBlockColumnAgreementSpec mainAir blockAir row start ∧
        blockCompressionSpec blockAir start) :
    rowBlockColumnAgreementSpec mainAir blockAir row start ∧
      let initialState := blockStartState blockAir start
      let messageWords := blockInputWords blockAir start
      let schedule := expandSchedule messageWords
      let finalState := (compressionTrace initialState schedule)[64]!
      rowNewState mainAir row = initialState.add finalState := by
  rcases hpackage with ⟨hcols, hblock⟩
  rcases hblock with ⟨_, _, hfinalBlock⟩
  dsimp
  refine ⟨hcols, ?_⟩
  calc
    rowNewState mainAir row = digestFinalHashState blockAir (start + 16) :=
      rowNewState_eq_digestFinalHashState_of_columns mainAir blockAir row start hcols
    _ = (blockStartState blockAir start).add
          (compressionTrace (blockStartState blockAir start)
            (expandSchedule (blockInputWords blockAir start)))[64]! :=
      hfinalBlock


end SharedBridge

end Sha2CompressionBridge_sha256
