import VmExtensions.Soundness.Sha2MainAir_sha512.Permutation

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1_000_000_000

namespace Sha2CompressionBridge_sha512

open BabyBear
open Sha2MainAir_sha512.Soundness
open Sha2BlockHasherVmAir_sha512.BlockSpec

section SharedBridge

open Sha2BlockHasherVmAir_sha512.constraints

variable {CMain CBlock : Type → Type → Type} {ExtF : Type}
  [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]

/-- Byte-level bridge at the main-chip column boundary: once the three wrapper
entries match a SHA-512 block window, the exposed state limbs, input bytes, and
output bytes agree column-for-column with that block window. -/
def rowBlockColumnAgreementSpec
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ) : Prop :=
  let blockState := Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)
  let blockMsg1 := Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start
  let blockMsg2 := Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)
  (∀ i : Fin 32, Sha2MainAir_sha512.constraints.prev_state_u16 mainAir i.1 row =
      blockState.prev_state_u16.get i) ∧
  (∀ i : Fin 64, Sha2MainAir_sha512.constraints.new_state_byte mainAir i.1 row =
      blockState.new_state_bytes.get i) ∧
  (∀ i : Fin 32, Sha2MainAir_sha512.constraints.message_byte mainAir i.1 row =
      blockMsg1.local_msg_bytes.get i) ∧
  (∀ i : Fin 32, Sha2MainAir_sha512.constraints.message_byte mainAir (32 + i.1) row =
      blockMsg1.next_msg_bytes.get i) ∧
  (∀ i : Fin 32, Sha2MainAir_sha512.constraints.message_byte mainAir (64 + i.1) row =
      blockMsg2.local_msg_bytes.get i) ∧
  ∀ i : Fin 32, Sha2MainAir_sha512.constraints.message_byte mainAir (96 + i.1) row =
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
      Sha2MainAir_sha512.constraints.prev_state_u16 mainAir i.1 row =
          (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir row).prev_state_u16.get i := by
        symm
        exact hmainPrev i
      _ =
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).prev_state_u16.get i :=
        hstateShared i
  · intro i
    calc
      Sha2MainAir_sha512.constraints.new_state_byte mainAir i.1 row =
          (Sha2MainAir_sha512.constraints.wrapperStateEntry mainAir row).new_state_bytes.get i := by
        symm
        exact hmainNew i
      _ =
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get i :=
        hwriteShared i
  · intro i
    calc
      Sha2MainAir_sha512.constraints.message_byte mainAir i.1 row =
          (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir row).local_msg_bytes.get i := by
        symm
        exact hmainMsg1Local i
      _ =
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).local_msg_bytes.get i :=
        hmsg1LocalShared i
  · intro i
    calc
      Sha2MainAir_sha512.constraints.message_byte mainAir (32 + i.1) row =
          (Sha2MainAir_sha512.constraints.wrapperMsg1Entry mainAir row).next_msg_bytes.get i := by
        symm
        exact hmainMsg1Next i
      _ =
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).next_msg_bytes.get i :=
        hmsg1NextShared i
  · intro i
    calc
      Sha2MainAir_sha512.constraints.message_byte mainAir (64 + i.1) row =
          (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir row).local_msg_bytes.get i := by
        symm
        exact hmainMsg2Local i
      _ =
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).local_msg_bytes.get i :=
        hmsg2LocalShared i
  · intro i
    calc
      Sha2MainAir_sha512.constraints.message_byte mainAir (96 + i.1) row =
          (Sha2MainAir_sha512.constraints.wrapperMsg2Entry mainAir row).next_msg_bytes.get i := by
        symm
        exact hmainMsg2Next i
      _ =
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).next_msg_bytes.get i :=
        hmsg2NextShared i

/-- Previous chaining word reconstructed from the main row's exposed
`prev_state_u16` limbs. -/
def rowPrevStateWord
    (mainAir : CMain FBB ExtF) (row : ℕ) (word : Fin 8) : Word :=
  limbs16LEToWord (fun limb =>
    Sha2MainAir_sha512.constraints.prev_state_u16 mainAir (4 * word.1 + limb) row)

/-- Output chaining word reconstructed from the main row's exposed
`new_state_byte` columns. -/
def rowNewStateWord
    (mainAir : CMain FBB ExtF) (row : ℕ) (word : Fin 8) : Word :=
  bytesLEToWord (fun byte =>
    Sha2MainAir_sha512.constraints.new_state_byte mainAir (8 * word.1 + byte) row)

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
    (blockAir : CBlock FBB ExtF) (row : ℕ) (word : Fin 8) (limb : Fin 4) :
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir row).prev_state_u16.get
      ⟨4 * word.1 + limb.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha512.constraints.prev_hash blockAir word.1 limb.1 row := by
  fin_cases word <;> fin_cases limb <;>
    simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry]

private theorem blockWrapperState_new_state_bytes_get
    (blockAir : CBlock FBB ExtF) (row : ℕ) (word : Fin 8) (byte : Fin 8) :
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir row).new_state_bytes.get
      ⟨8 * word.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha512.constraints.final_hash blockAir word.1 byte.1 row := by
  fin_cases word <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry]

private theorem rowPrevStateWord_eq_digestPrevHashWord_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 8) :
    rowPrevStateWord mainAir row word = digestPrevHashWord blockAir (start + 20) word.1 := by
  rcases hcols with ⟨hprev, _, _, _, _, _⟩
  have h0 :
      Sha2MainAir_sha512.constraints.prev_state_u16 mainAir (4 * word.1) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).prev_state_u16.get
          ⟨4 * word.1, by omega⟩ := by
    simpa using hprev ⟨4 * word.1, by omega⟩
  have h1 :
      Sha2MainAir_sha512.constraints.prev_state_u16 mainAir (4 * word.1 + 1) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).prev_state_u16.get
          ⟨4 * word.1 + 1, by omega⟩ := by
    simpa using hprev ⟨4 * word.1 + 1, by omega⟩
  have h2 :
      Sha2MainAir_sha512.constraints.prev_state_u16 mainAir (4 * word.1 + 2) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).prev_state_u16.get
          ⟨4 * word.1 + 2, by omega⟩ := by
    simpa using hprev ⟨4 * word.1 + 2, by omega⟩
  have h3 :
      Sha2MainAir_sha512.constraints.prev_state_u16 mainAir (4 * word.1 + 3) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).prev_state_u16.get
          ⟨4 * word.1 + 3, by omega⟩ := by
    simpa using hprev ⟨4 * word.1 + 3, by omega⟩
  have hwrap0 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).prev_state_u16.get
        ⟨4 * word.1, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.prev_hash blockAir word.1 0 (start + 20) := by
    simpa using
      blockWrapperState_prev_state_u16_get blockAir (start + 20) word ⟨0, by decide⟩
  have hwrap1 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).prev_state_u16.get
        ⟨4 * word.1 + 1, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.prev_hash blockAir word.1 1 (start + 20) := by
    simpa using
      blockWrapperState_prev_state_u16_get blockAir (start + 20) word ⟨1, by decide⟩
  have hwrap2 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).prev_state_u16.get
        ⟨4 * word.1 + 2, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.prev_hash blockAir word.1 2 (start + 20) := by
    simpa using
      blockWrapperState_prev_state_u16_get blockAir (start + 20) word ⟨2, by decide⟩
  have hwrap3 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).prev_state_u16.get
        ⟨4 * word.1 + 3, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.prev_hash blockAir word.1 3 (start + 20) := by
    simpa using
      blockWrapperState_prev_state_u16_get blockAir (start + 20) word ⟨3, by decide⟩
  unfold rowPrevStateWord limbs16LEToWord
  rw [foldl_range_add_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [digestPrevHash_eq_limbs]
  simp [digestPrevHashU16Limb, h0, h1, h2, h3, hwrap0, hwrap1, hwrap2, hwrap3]

private theorem rowPrevState_eq_digestPrevHashState_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start) :
    rowPrevState mainAir row = digestPrevHashState blockAir (start + 20) := by
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
    rowNewStateWord mainAir row word = digestFinalHashWord blockAir (start + 20) word.1 := by
  rcases hcols with ⟨_, hnew, _, _, _, _⟩
  have h0 :
      Sha2MainAir_sha512.constraints.new_state_byte mainAir (8 * word.1) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
          ⟨8 * word.1, by omega⟩ := by
    simpa using hnew ⟨8 * word.1, by omega⟩
  have h1 :
      Sha2MainAir_sha512.constraints.new_state_byte mainAir (8 * word.1 + 1) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
          ⟨8 * word.1 + 1, by omega⟩ := by
    simpa using hnew ⟨8 * word.1 + 1, by omega⟩
  have h2 :
      Sha2MainAir_sha512.constraints.new_state_byte mainAir (8 * word.1 + 2) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
          ⟨8 * word.1 + 2, by omega⟩ := by
    simpa using hnew ⟨8 * word.1 + 2, by omega⟩
  have h3 :
      Sha2MainAir_sha512.constraints.new_state_byte mainAir (8 * word.1 + 3) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
          ⟨8 * word.1 + 3, by omega⟩ := by
    simpa using hnew ⟨8 * word.1 + 3, by omega⟩
  have h4 :
      Sha2MainAir_sha512.constraints.new_state_byte mainAir (8 * word.1 + 4) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
          ⟨8 * word.1 + 4, by omega⟩ := by
    simpa using hnew ⟨8 * word.1 + 4, by omega⟩
  have h5 :
      Sha2MainAir_sha512.constraints.new_state_byte mainAir (8 * word.1 + 5) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
          ⟨8 * word.1 + 5, by omega⟩ := by
    simpa using hnew ⟨8 * word.1 + 5, by omega⟩
  have h6 :
      Sha2MainAir_sha512.constraints.new_state_byte mainAir (8 * word.1 + 6) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
          ⟨8 * word.1 + 6, by omega⟩ := by
    simpa using hnew ⟨8 * word.1 + 6, by omega⟩
  have h7 :
      Sha2MainAir_sha512.constraints.new_state_byte mainAir (8 * word.1 + 7) row =
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
          ⟨8 * word.1 + 7, by omega⟩ := by
    simpa using hnew ⟨8 * word.1 + 7, by omega⟩
  have hwrap0 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
        ⟨8 * word.1, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.final_hash blockAir word.1 0 (start + 20) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 20) word ⟨0, by decide⟩
  have hwrap1 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
        ⟨8 * word.1 + 1, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.final_hash blockAir word.1 1 (start + 20) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 20) word ⟨1, by decide⟩
  have hwrap2 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
        ⟨8 * word.1 + 2, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.final_hash blockAir word.1 2 (start + 20) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 20) word ⟨2, by decide⟩
  have hwrap3 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
        ⟨8 * word.1 + 3, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.final_hash blockAir word.1 3 (start + 20) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 20) word ⟨3, by decide⟩
  have hwrap4 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
        ⟨8 * word.1 + 4, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.final_hash blockAir word.1 4 (start + 20) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 20) word ⟨4, by decide⟩
  have hwrap5 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
        ⟨8 * word.1 + 5, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.final_hash blockAir word.1 5 (start + 20) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 20) word ⟨5, by decide⟩
  have hwrap6 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
        ⟨8 * word.1 + 6, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.final_hash blockAir word.1 6 (start + 20) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 20) word ⟨6, by decide⟩
  have hwrap7 :
      (Sha2BlockHasherVmAir_sha512.constraints.wrapperStateEntry blockAir (start + 20)).new_state_bytes.get
        ⟨8 * word.1 + 7, by omega⟩ =
          Sha2BlockHasherVmAir_sha512.constraints.final_hash blockAir word.1 7 (start + 20) := by
    simpa using
      blockWrapperState_new_state_bytes_get blockAir (start + 20) word ⟨7, by decide⟩
  unfold rowNewStateWord digestFinalHashWord bytesLEToWord
  rw [foldl_range_add_eq_sum, foldl_range_add_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [h0, h1, h2, h3, h4, h5, h6, h7,
    hwrap0, hwrap1, hwrap2, hwrap3, hwrap4, hwrap5, hwrap6, hwrap7]

private theorem rowNewState_eq_digestFinalHashState_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start) :
    rowNewState mainAir row = digestFinalHashState blockAir (start + 20) := by
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
      rowPrevState mainAir row = digestPrevHashState blockAir (start + 20) :=
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
      let finalState := (compressionTrace initialState schedule)[80]!
      rowNewState mainAir row = initialState.add finalState := by
  rcases hpackage with ⟨hcols, hblock⟩
  rcases hblock with ⟨_, _, hfinalBlock⟩
  dsimp
  refine ⟨hcols, ?_⟩
  calc
    rowNewState mainAir row = digestFinalHashState blockAir (start + 20) :=
      rowNewState_eq_digestFinalHashState_of_columns mainAir blockAir row start hcols
    _ = (blockStartState blockAir start).add
          (compressionTrace (blockStartState blockAir start)
            (expandSchedule (blockInputWords blockAir start)))[80]! :=
      hfinalBlock

end SharedBridge

end Sha2CompressionBridge_sha512
