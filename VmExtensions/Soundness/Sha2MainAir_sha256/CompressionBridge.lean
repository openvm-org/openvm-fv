import VmExtensions.Soundness.Sha2MainAir_sha256.Bus
import VmExtensions.Constraints.Sha2BlockHasherSubAirBus_sha256
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.Block.Soundness

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

/-- The full shared SHA-2 wrapper-bus trace, formed by concatenating the
main-chip wrapper sends with the block-hasher wrapper receives. Both sides use
the same raw `(multiplicity, payload)` encoding, so they can be compared
directly at the interaction level. -/
noncomputable def sharedWrapperTraceEntries
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) : List (FBB × List FBB) :=
  Sha2MainAir_sha256.constraints.wrapperBus_trace mainAir ++
    Sha2BlockHasherVmAir_sha256.constraints.wrapperBus_trace blockAir

/-- Global raw wrapper-bus permutation semantics spanning the two chips: the
combined main/block wrapper trace is balanced as an interaction list. This is
the direct shared-wrapper analogue of `privateBusRawPermutationSemantics`,
before any row- or block-window-specific extraction. -/
def sharedWrapperRawPermutationSemantics
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) : Prop :=
  InteractionList.is_balanced (sharedWrapperTraceEntries mainAir blockAir)

/-- Smaller shared-wrapper boundary: only the payload limbs/bytes agree across
the three matched wrapper entries. This is the exact data needed by the
row/block column bridge. -/
def sharedWrapperPayloadSpec
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ) : Prop :=
  let mainState := Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row
  let blockState := Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)
  let mainMsg1 := Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row
  let blockMsg1 := Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start
  let mainMsg2 := Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row
  let blockMsg2 := Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)
  (∀ i : Fin 16, mainState.prev_state_u16.get i = blockState.prev_state_u16.get i) ∧
  (∀ i : Fin 32, mainState.new_state_bytes.get i = blockState.new_state_bytes.get i) ∧
  (∀ i : Fin 16, mainMsg1.local_msg_bytes.get i = blockMsg1.local_msg_bytes.get i) ∧
  (∀ i : Fin 16, mainMsg1.next_msg_bytes.get i = blockMsg1.next_msg_bytes.get i) ∧
  (∀ i : Fin 16, mainMsg2.local_msg_bytes.get i = blockMsg2.local_msg_bytes.get i) ∧
  (∀ i : Fin 16, mainMsg2.next_msg_bytes.get i = blockMsg2.next_msg_bytes.get i)

theorem mainWrapperState_raw_head
    (mainAir : CMain FBB ExtF) (row : ℕ) :
    List.head? ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).toRaw.2) = some 0 := by
  simp [Sha2MainAir_sha256.constraints.wrapperStateEntry]

theorem mainWrapperMsg1_raw_head
    (mainAir : CMain FBB ExtF) (row : ℕ) :
    List.head? ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).toRaw.2) = some 1 := by
  simp [Sha2MainAir_sha256.constraints.wrapperMsg1Entry]

theorem mainWrapperMsg2_raw_head
    (mainAir : CMain FBB ExtF) (row : ℕ) :
    List.head? ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).toRaw.2) = some 2 := by
  simp [Sha2MainAir_sha256.constraints.wrapperMsg2Entry]

theorem blockWrapperState_raw_head
    (blockAir : CBlock FBB ExtF) (row : ℕ) :
    List.head? ((wrapperStateEntry blockAir row).toRaw.2) = some 0 := by
  simp [wrapperStateEntry]

theorem blockWrapperMsg1_raw_head
    (blockAir : CBlock FBB ExtF) (row : ℕ) :
    List.head? ((wrapperMsg1Entry blockAir row).toRaw.2) = some 1 := by
  simp [wrapperMsg1Entry]

theorem blockWrapperMsg2_raw_head
    (blockAir : CBlock FBB ExtF) (row : ℕ) :
    List.head? ((wrapperMsg2Entry blockAir row).toRaw.2) = some 2 := by
  simp [wrapperMsg2Entry]

theorem mainWrapperState_raw_request
    (mainAir : CMain FBB ExtF) (row : ℕ) :
    List.head? (List.tail ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).toRaw.2)) =
      some (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).request_id := by
  simp [Sha2MainAir_sha256.constraints.wrapperStateEntry]

theorem mainWrapperMsg1_raw_request
    (mainAir : CMain FBB ExtF) (row : ℕ) :
    List.head? (List.tail ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).toRaw.2)) =
      some (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).request_id := by
  simp [Sha2MainAir_sha256.constraints.wrapperMsg1Entry]

theorem mainWrapperMsg2_raw_request
    (mainAir : CMain FBB ExtF) (row : ℕ) :
    List.head? (List.tail ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).toRaw.2)) =
      some (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).request_id := by
  simp [Sha2MainAir_sha256.constraints.wrapperMsg2Entry]

theorem blockWrapperState_raw_request
    (blockAir : CBlock FBB ExtF) (row : ℕ) :
    List.head? (List.tail ((wrapperStateEntry blockAir row).toRaw.2)) =
      some (wrapperStateEntry blockAir row).request_id := by
  simp [wrapperStateEntry]

theorem blockWrapperMsg1_raw_request
    (blockAir : CBlock FBB ExtF) (row : ℕ) :
    List.head? (List.tail ((wrapperMsg1Entry blockAir row).toRaw.2)) =
      some (wrapperMsg1Entry blockAir row).request_id := by
  simp [wrapperMsg1Entry]

theorem blockWrapperMsg2_raw_request
    (blockAir : CBlock FBB ExtF) (row : ℕ) :
    List.head? (List.tail ((wrapperMsg2Entry blockAir row).toRaw.2)) =
      some (wrapperMsg2Entry blockAir row).request_id := by
  simp [wrapperMsg2Entry]

theorem prefixed_vectors_get_left
    {α : Type} (a b : α) {m n : ℕ} (xs : Vector α m) (ys : Vector α n) (i : Fin m) :
    ((([a, b] : List α) ++ xs.toList ++ ys.toList)[i.1 + 2]?) = some (xs.get i) := by
  have hprefix : ([a, b] : List α).length ≤ i.1 + 2 := by
    simp
  have hleft : i.1 < xs.toList.length := by
    simpa using i.2
  calc
    ((([a, b] : List α) ++ xs.toList ++ ys.toList)[i.1 + 2]?)
        = ((xs.toList ++ ys.toList)[(i.1 + 2) - ([a, b] : List α).length]?) := by
            simpa [List.append_assoc] using
              (List.getElem?_append_right
                (l₁ := ([a, b] : List α))
                (l₂ := xs.toList ++ ys.toList)
                (i := i.1 + 2) hprefix)
    _ = ((xs.toList ++ ys.toList)[i.1]?) := by
          simp
    _ = (xs.toList[i.1]?) := by
          simpa using
            (List.getElem?_append_left
              (l₁ := xs.toList)
              (l₂ := ys.toList)
              (i := i.1) hleft)
    _ = some (xs.get i) := by
          rw [List.getElem?_eq_getElem hleft]
          rw [Vector.getElem_toList (xs := xs) (i := i.1) hleft]
          rfl

theorem prefixed_vectors_get_right
    {α : Type} (a b : α) {m n : ℕ} (xs : Vector α m) (ys : Vector α n) (i : Fin n) :
    ((([a, b] : List α) ++ xs.toList ++ ys.toList)[m + i.1 + 2]?) = some (ys.get i) := by
  have hprefix : ([a, b] : List α).length ≤ m + i.1 + 2 := by
    simp
  have hright : i.1 < ys.toList.length := by
    simpa using i.2
  have hxs_le : xs.toList.length ≤ m + i.1 := by
    simp
  calc
    ((([a, b] : List α) ++ xs.toList ++ ys.toList)[m + i.1 + 2]?)
        = ((xs.toList ++ ys.toList)[(m + i.1 + 2) - ([a, b] : List α).length]?) := by
            simpa [List.append_assoc] using
              (List.getElem?_append_right
                (l₁ := ([a, b] : List α))
                (l₂ := xs.toList ++ ys.toList)
                (i := m + i.1 + 2) hprefix)
    _ = ((xs.toList ++ ys.toList)[m + i.1]?) := by
          simp
    _ = (ys.toList[(m + i.1) - xs.toList.length]?) := by
          simpa using
            (List.getElem?_append_right
              (l₁ := xs.toList)
              (l₂ := ys.toList)
              (i := m + i.1) hxs_le)
    _ = (ys.toList[i.1]?) := by
          simp
    _ = some (ys.get i) := by
          rw [List.getElem?_eq_getElem hright]
          rw [Vector.getElem_toList (xs := ys) (i := i.1) hright]
          rfl

theorem mainWrapperState_raw_prev
    (mainAir : CMain FBB ExtF) (row : ℕ) (i : Fin 16) :
    ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).toRaw.2)[i.1 + 2]? =
      some ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).prev_state_u16.get i) := by
  exact prefixed_vectors_get_left
    (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).message_type
    (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).request_id
    (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).prev_state_u16
    (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).new_state_bytes i

theorem mainWrapperState_raw_new
    (mainAir : CMain FBB ExtF) (row : ℕ) (i : Fin 32) :
    ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).toRaw.2)[i.1 + 18]? =
      some ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).new_state_bytes.get i) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (prefixed_vectors_get_right
      (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).message_type
      (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).request_id
      (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).prev_state_u16
      (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).new_state_bytes i)

theorem blockWrapperState_raw_prev
    (blockAir : CBlock FBB ExtF) (row : ℕ) (i : Fin 16) :
    ((wrapperStateEntry blockAir row).toRaw.2)[i.1 + 2]? =
      some ((wrapperStateEntry blockAir row).prev_state_u16.get i) := by
  exact prefixed_vectors_get_left
    (wrapperStateEntry blockAir row).message_type
    (wrapperStateEntry blockAir row).request_id
    (wrapperStateEntry blockAir row).prev_state_u16
    (wrapperStateEntry blockAir row).new_state_bytes i

theorem blockWrapperState_raw_new
    (blockAir : CBlock FBB ExtF) (row : ℕ) (i : Fin 32) :
    ((wrapperStateEntry blockAir row).toRaw.2)[i.1 + 18]? =
      some ((wrapperStateEntry blockAir row).new_state_bytes.get i) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (prefixed_vectors_get_right
      (wrapperStateEntry blockAir row).message_type
      (wrapperStateEntry blockAir row).request_id
      (wrapperStateEntry blockAir row).prev_state_u16
      (wrapperStateEntry blockAir row).new_state_bytes i)

theorem mainWrapperMsg1_raw_local
    (mainAir : CMain FBB ExtF) (row : ℕ) (i : Fin 16) :
    ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).toRaw.2)[i.1 + 2]? =
      some ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).local_msg_bytes.get i) := by
  exact prefixed_vectors_get_left
    (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).message_type
    (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).request_id
    (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).local_msg_bytes
    (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).next_msg_bytes i

theorem mainWrapperMsg1_raw_next
    (mainAir : CMain FBB ExtF) (row : ℕ) (i : Fin 16) :
    ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).toRaw.2)[i.1 + 18]? =
      some ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).next_msg_bytes.get i) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (prefixed_vectors_get_right
      (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).message_type
      (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).request_id
      (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).local_msg_bytes
      (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).next_msg_bytes i)

theorem blockWrapperMsg1_raw_local
    (blockAir : CBlock FBB ExtF) (row : ℕ) (i : Fin 16) :
    ((wrapperMsg1Entry blockAir row).toRaw.2)[i.1 + 2]? =
      some ((wrapperMsg1Entry blockAir row).local_msg_bytes.get i) := by
  exact prefixed_vectors_get_left
    (wrapperMsg1Entry blockAir row).message_type
    (wrapperMsg1Entry blockAir row).request_id
    (wrapperMsg1Entry blockAir row).local_msg_bytes
    (wrapperMsg1Entry blockAir row).next_msg_bytes i

theorem blockWrapperMsg1_raw_next
    (blockAir : CBlock FBB ExtF) (row : ℕ) (i : Fin 16) :
    ((wrapperMsg1Entry blockAir row).toRaw.2)[i.1 + 18]? =
      some ((wrapperMsg1Entry blockAir row).next_msg_bytes.get i) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (prefixed_vectors_get_right
      (wrapperMsg1Entry blockAir row).message_type
      (wrapperMsg1Entry blockAir row).request_id
      (wrapperMsg1Entry blockAir row).local_msg_bytes
      (wrapperMsg1Entry blockAir row).next_msg_bytes i)

theorem mainWrapperMsg2_raw_local
    (mainAir : CMain FBB ExtF) (row : ℕ) (i : Fin 16) :
    ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).toRaw.2)[i.1 + 2]? =
      some ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).local_msg_bytes.get i) := by
  exact prefixed_vectors_get_left
    (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).message_type
    (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).request_id
    (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).local_msg_bytes
    (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).next_msg_bytes i

theorem mainWrapperMsg2_raw_next
    (mainAir : CMain FBB ExtF) (row : ℕ) (i : Fin 16) :
    ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).toRaw.2)[i.1 + 18]? =
      some ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).next_msg_bytes.get i) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (prefixed_vectors_get_right
      (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).message_type
      (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).request_id
      (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).local_msg_bytes
      (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).next_msg_bytes i)

theorem blockWrapperMsg2_raw_local
    (blockAir : CBlock FBB ExtF) (row : ℕ) (i : Fin 16) :
    ((wrapperMsg2Entry blockAir row).toRaw.2)[i.1 + 2]? =
      some ((wrapperMsg2Entry blockAir row).local_msg_bytes.get i) := by
  exact prefixed_vectors_get_left
    (wrapperMsg2Entry blockAir row).message_type
    (wrapperMsg2Entry blockAir row).request_id
    (wrapperMsg2Entry blockAir row).local_msg_bytes
    (wrapperMsg2Entry blockAir row).next_msg_bytes i

theorem blockWrapperMsg2_raw_next
    (blockAir : CBlock FBB ExtF) (row : ℕ) (i : Fin 16) :
    ((wrapperMsg2Entry blockAir row).toRaw.2)[i.1 + 18]? =
      some ((wrapperMsg2Entry blockAir row).next_msg_bytes.get i) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (prefixed_vectors_get_right
      (wrapperMsg2Entry blockAir row).message_type
      (wrapperMsg2Entry blockAir row).request_id
      (wrapperMsg2Entry blockAir row).local_msg_bytes
      (wrapperMsg2Entry blockAir row).next_msg_bytes i)

theorem mem_filterMap_of_mem_some
    {α β : Type}
    (f : α → Option β)
    {l : List α} {a : α} {b : β}
    (ha : a ∈ l)
    (hf : f a = some b) :
    b ∈ l.filterMap f := by
  simpa using (List.mem_filterMap.2 ⟨a, ha, hf⟩)

theorem exists_mem_eq_some_of_mem_filterMap
    {α β : Type}
    (f : α → Option β)
    {l : List α} {b : β}
    (hb : b ∈ l.filterMap f) :
    ∃ a ∈ l, f a = some b := by
  simpa using (List.mem_filterMap.1 hb)

theorem mem_mainWrapperTrace_iff
    (mainAir : CMain FBB ExtF)
    (entry : FBB × List FBB) :
    entry ∈ Sha2MainAir_sha256.constraints.wrapperBus_trace mainAir ↔
      ∃ row, row ≤ Circuit.last_row mainAir ∧
        entry ∈ Sha2MainAir_sha256.constraints.wrapperBus_row mainAir row := by
  constructor
  · intro hentry
    rw [Sha2MainAir_sha256.constraints.wrapperBus_trace] at hentry
    rcases List.mem_flatMap.mp hentry with ⟨row, hrow_mem, hentry_row⟩
    exact ⟨row, Nat.lt_succ_iff.mp (List.mem_range.mp hrow_mem), hentry_row⟩
  · rintro ⟨row, hvalid, hentry_row⟩
    rw [Sha2MainAir_sha256.constraints.wrapperBus_trace]
    exact List.mem_flatMap.mpr
      ⟨row, List.mem_range.mpr (Nat.lt_succ_of_le hvalid), hentry_row⟩

theorem mem_blockWrapperTrace_iff
    (blockAir : CBlock FBB ExtF)
    (entry : FBB × List FBB) :
    entry ∈ Sha2BlockHasherVmAir_sha256.constraints.wrapperBus_trace blockAir ↔
      ∃ row, row ≤ Circuit.last_row blockAir ∧
        entry ∈ Sha2BlockHasherVmAir_sha256.constraints.wrapperBus_row blockAir row := by
  constructor
  · intro hentry
    rw [Sha2BlockHasherVmAir_sha256.constraints.wrapperBus_trace] at hentry
    rcases List.mem_flatMap.mp hentry with ⟨row, hrow_mem, hentry_row⟩
    exact ⟨row, Nat.lt_succ_iff.mp (List.mem_range.mp hrow_mem), hentry_row⟩
  · rintro ⟨row, hvalid, hentry_row⟩
    rw [Sha2BlockHasherVmAir_sha256.constraints.wrapperBus_trace]
    exact List.mem_flatMap.mpr
      ⟨row, List.mem_range.mpr (Nat.lt_succ_of_le hvalid), hentry_row⟩

private theorem padding_choose2_is_bit_lookup :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      ((2 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        (1 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        wrapperBus_choose2_coeff : FBB) = 0 ∨
      ((2 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        (1 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        wrapperBus_choose2_coeff : FBB) = 1 := by
  decide

theorem wrapperBus_padding_choose2_is_bit
    (air : CBlock FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    wrapperBus_padding_choose2 air row = 0 ∨
      wrapperBus_padding_choose2 air row = 1 := by
  have hd0 := encoder_digits_ternary air row hf 0 (by omega)
  have hd1 := encoder_digits_ternary air row hf 1 (by omega)
  have hd2 := encoder_digits_ternary air row hf 2 (by omega)
  have hd3 := encoder_digits_ternary air row hf 3 (by omega)
  have hd4 := encoder_digits_ternary air row hf 4 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 row) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 row) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 row) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 row) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 row) hd4 with ⟨n4, h4⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4] using
      encoder_digit_sum_ternary air row hf
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hlookup :
      ((2 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        (1 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        wrapperBus_choose2_coeff : FBB) = 0 ∨
      ((2 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        (1 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        wrapperBus_choose2_coeff : FBB) = 1 :=
    padding_choose2_is_bit_lookup n0 n1 n2 n3 n4 htotal_le
  simpa [wrapperBus_padding_choose2, h0, h1, h2, h3, h4] using hlookup

theorem wrapperBus_choose2_encoder4_is_bit
    (air : CBlock FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row) :
    wrapperBus_choose2 (encoder_idx air 4 row) = 0 ∨
      wrapperBus_choose2 (encoder_idx air 4 row) = 1 := by
  rcases encoder_digits_ternary air row hf 4 (by omega) with h0 | h1 | h2
  · left
    simp [wrapperBus_choose2, h0]
  · left
    simp [wrapperBus_choose2, h1]
  · right
    have hcoeff : ((2 : FBB) * ((2 : FBB) - 1) * wrapperBus_choose2_coeff : FBB) = 1 := by
      decide
    simpa [wrapperBus_choose2, h2] using hcoeff

private theorem padding_choose2_one_implies_selector_zero_lookup :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      ((2 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        (1 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        wrapperBus_choose2_coeff : FBB) = 1 →
      encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = 0 := by
  decide

private theorem selector_two_implies_choose2_one_lookup :
    ∀ n0 n1 n2 n3 n4 : Fin 3,
      n0.val + n1.val + n2.val + n3.val + n4.val ≤ 2 →
      encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = 2 →
      ((n4.val : FBB) * ((n4.val : FBB) - 1) * wrapperBus_choose2_coeff : FBB) = 1 := by
  decide

theorem blockWrapperMsg1_active_implies_selector_zero
    (air : CBlock FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row)
    (hactive :
      (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry air row).multiplicity = -1) :
    encoder_selector_idx air row = 0 := by
  have hprod_one :
      wrapperBus_padding_choose2 air row *
        (is_round_row air row + is_digest_row air row) = 1 := by
    have hactive' :
        -(wrapperBus_padding_choose2 air row *
          (is_round_row air row + is_digest_row air row)) = -1 := by
      simpa [Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry] using hactive
    have hactive'' := congrArg Neg.neg hactive'
    simpa using hactive''
  have hpad_bit := wrapperBus_padding_choose2_is_bit air row hf
  have hpad_one : wrapperBus_padding_choose2 air row = 1 := by
    rcases hpad_bit with hpad0 | hpad1
    · have : (0 : FBB) = 1 := by simpa [hpad0] using hprod_one
      exact False.elim ((by decide : (0 : FBB) ≠ 1) this)
    · exact hpad1
  have hd0 := encoder_digits_ternary air row hf 0 (by omega)
  have hd1 := encoder_digits_ternary air row hf 1 (by omega)
  have hd2 := encoder_digits_ternary air row hf 2 (by omega)
  have hd3 := encoder_digits_ternary air row hf 3 (by omega)
  have hd4 := encoder_digits_ternary air row hf 4 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 row) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 row) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 row) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 row) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 row) hd4 with ⟨n4, h4⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4] using
      encoder_digit_sum_ternary air row hf
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hpad_lookup :
      ((2 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        (1 - ((n0.val + n1.val + n2.val + n3.val + n4.val : ℕ) : FBB)) *
        wrapperBus_choose2_coeff : FBB) = 1 := by
    simpa [wrapperBus_padding_choose2, h0, h1, h2, h3, h4] using hpad_one
  have hsel0 :
      encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = 0 :=
    padding_choose2_one_implies_selector_zero_lookup n0 n1 n2 n3 n4 htotal_le hpad_lookup
  simpa [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from, encoderSelectorPoly,
    h0, h1, h2, h3, h4] using hsel0

theorem blockWrapperMsg2_active_of_selector_two
    (air : CBlock FBB ExtF) (row : ℕ)
    (hf : flag_constraints air row)
    (hreal : is_round_row air row + is_digest_row air row = 1)
    (hsel : encoder_selector_idx air row = 2) :
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry air row).multiplicity = -1 := by
  have hd0 := encoder_digits_ternary air row hf 0 (by omega)
  have hd1 := encoder_digits_ternary air row hf 1 (by omega)
  have hd2 := encoder_digits_ternary air row hf 2 (by omega)
  have hd3 := encoder_digits_ternary air row hf 3 (by omega)
  have hd4 := encoder_digits_ternary air row hf 4 (by omega)
  rcases ternary_as_fin3 (encoder_idx air 0 row) hd0 with ⟨n0, h0⟩
  rcases ternary_as_fin3 (encoder_idx air 1 row) hd1 with ⟨n1, h1⟩
  rcases ternary_as_fin3 (encoder_idx air 2 row) hd2 with ⟨n2, h2⟩
  rcases ternary_as_fin3 (encoder_idx air 3 row) hd3 with ⟨n3, h3⟩
  rcases ternary_as_fin3 (encoder_idx air 4 row) hd4 with ⟨n4, h4⟩
  let total : ℕ := n0.val + n1.val + n2.val + n3.val + n4.val
  have htotal_field :
      ((total : ℕ) : FBB) = 0 ∨ ((total : ℕ) : FBB) = 1 ∨ ((total : ℕ) : FBB) = 2 := by
    simpa [total, encoder_digit_sum, encoder_digit_sum_from, h0, h1, h2, h3, h4] using
      encoder_digit_sum_ternary air row hf
  have htotal_lt : total < BB_prime := by
    dsimp [total]
    omega
  have htotal_le : total ≤ 2 := nat_sum_le_two_of_field_ternary htotal_lt htotal_field
  have hsel_lookup :
      encoderSelectorPoly (n0.val : FBB) (n1.val : FBB) (n2.val : FBB)
        (n3.val : FBB) (n4.val : FBB) = 2 := by
    simpa [encoder_selector_idx, encoder_selector_from, encoder_digit_sum_from, encoderSelectorPoly,
      h0, h1, h2, h3, h4] using hsel
  have hchoose_lookup :
      ((n4.val : FBB) * ((n4.val : FBB) - 1) * wrapperBus_choose2_coeff : FBB) = 1 :=
    selector_two_implies_choose2_one_lookup n0 n1 n2 n3 n4 htotal_le hsel_lookup
  have hchoose : wrapperBus_choose2 (encoder_idx air 4 row) = 1 := by
    simpa [wrapperBus_choose2, h4] using hchoose_lookup
  simpa [Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry, hreal, hchoose]

private lemma block_next_request_id_eq_nextRow
    (air : CBlock FBB ExtF) (hrot : rotation_consistent air) (row : ℕ)
    (hvalid : row ≤ Circuit.last_row air) :
    next_request_id air row = request_id air (nextRow air row) := by
  by_cases hrow : row < Circuit.last_row air
  · simp [nextRow, hrow.ne, next_request_id, request_id,
      next_main_eq_main_succ air hrot 0 row hrow]
  · have hlast : row = Circuit.last_row air :=
      le_antisymm hvalid (Nat.le_of_not_lt hrow)
    simp [nextRow, hlast, next_request_id, request_id,
      last_row_main_eq_first air hrot 0]

private theorem block_request_id_preserved_on_round
    (air : CBlock FBB ExtF) (row : ℕ)
    (hrow : row < Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air)
    (hround : is_round_row air row = 1) :
    request_id air (nextRow air row) = request_id air row := by
  rcases hc row with ⟨_, _, _, _, _, _, _, hreq⟩
  dsimp [wrapper_request_id_constraints, constraint_753] at hreq
  have hstep : next_request_id air row - request_id air row = 0 := by
    simpa [Circuit.isTransitionRow, hrow.ne, hround] using hreq
  have hstep' : next_request_id air row = request_id air row :=
    sub_eq_zero.mp hstep
  calc
    request_id air (nextRow air row) = next_request_id air row := by
      symm
      exact block_next_request_id_eq_nextRow air hrot row hrow.le
    _ = request_id air row := hstep'

theorem block_request_id_eq_start
    (air : CBlock FBB ExtF) (start offset : ℕ)
    (hoffset : offset ≤ 16)
    (hstart : start ≤ Circuit.last_row air)
    (hsel : encoder_selector_idx air start = 0)
    (hrot : rotation_consistent air)
    (hc : blockHasherConstraints air) :
    request_id air (start + offset) = request_id air start := by
  have hwindow := blockWindowSupported_of_start_le air start hstart hsel hrot hc
  have hshape := blockWindowHasShape_of_constraints air start hwindow hsel hrot hc
  induction offset with
  | zero =>
      simp
  | succ offset ih =>
      have hoffset_prev : offset ≤ 16 := by omega
      have hoffset_lt : offset < 16 := by omega
      have hrow : start + offset < Circuit.last_row air := by
        dsimp [blockWindowSupported] at hwindow
        omega
      have hround : is_round_row air (start + offset) = 1 := (hshape.2.1 offset hoffset_lt).2.1
      have hstep :=
        block_request_id_preserved_on_round air (start + offset) hrow hrot hc hround
      calc
        request_id air (start + offset + 1) = request_id air (start + offset) := by
          simpa [nextRow, hrow.ne, Nat.add_assoc] using hstep
        _ = request_id air start := ih hoffset_prev

theorem sharedWrapperPayloadSpec_of_raw_payload_eqs
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hstate_raw :
      (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).toRaw.2 =
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir (start + 16)).toRaw.2)
    (hmsg1_raw :
      (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).toRaw.2 =
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start).toRaw.2)
    (hmsg2_raw :
      (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).toRaw.2 =
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)).toRaw.2) :
    sharedWrapperPayloadSpec mainAir blockAir row start := by
  unfold sharedWrapperPayloadSpec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hraw :
        ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).toRaw.2)[i.1 + 2]? =
          ((wrapperStateEntry blockAir (start + 16)).toRaw.2)[i.1 + 2]? := by
      simpa using congrArg (fun payload => payload[i.1 + 2]?) hstate_raw
    apply Option.some.inj
    calc
      some ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).prev_state_u16.get i)
          = ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).toRaw.2)[i.1 + 2]? := by
            symm
            exact mainWrapperState_raw_prev mainAir row i
      _ = ((wrapperStateEntry blockAir (start + 16)).toRaw.2)[i.1 + 2]? := hraw
      _ = some ((wrapperStateEntry blockAir (start + 16)).prev_state_u16.get i) :=
            blockWrapperState_raw_prev blockAir (start + 16) i
  · intro i
    have hraw :
        ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).toRaw.2)[i.1 + 18]? =
          ((wrapperStateEntry blockAir (start + 16)).toRaw.2)[i.1 + 18]? := by
      simpa using congrArg (fun payload => payload[i.1 + 18]?) hstate_raw
    apply Option.some.inj
    calc
      some ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).new_state_bytes.get i)
          = ((Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir row).toRaw.2)[i.1 + 18]? := by
            symm
            exact mainWrapperState_raw_new mainAir row i
      _ = ((wrapperStateEntry blockAir (start + 16)).toRaw.2)[i.1 + 18]? := hraw
      _ = some ((wrapperStateEntry blockAir (start + 16)).new_state_bytes.get i) :=
            blockWrapperState_raw_new blockAir (start + 16) i
  · intro i
    have hraw :
        ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).toRaw.2)[i.1 + 2]? =
          ((wrapperMsg1Entry blockAir start).toRaw.2)[i.1 + 2]? := by
      simpa using congrArg (fun payload => payload[i.1 + 2]?) hmsg1_raw
    apply Option.some.inj
    calc
      some ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).local_msg_bytes.get i)
          = ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).toRaw.2)[i.1 + 2]? := by
            symm
            exact mainWrapperMsg1_raw_local mainAir row i
      _ = ((wrapperMsg1Entry blockAir start).toRaw.2)[i.1 + 2]? := hraw
      _ = some ((wrapperMsg1Entry blockAir start).local_msg_bytes.get i) :=
            blockWrapperMsg1_raw_local blockAir start i
  · intro i
    have hraw :
        ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).toRaw.2)[i.1 + 18]? =
          ((wrapperMsg1Entry blockAir start).toRaw.2)[i.1 + 18]? := by
      simpa using congrArg (fun payload => payload[i.1 + 18]?) hmsg1_raw
    apply Option.some.inj
    calc
      some ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).next_msg_bytes.get i)
          = ((Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir row).toRaw.2)[i.1 + 18]? := by
            symm
            exact mainWrapperMsg1_raw_next mainAir row i
      _ = ((wrapperMsg1Entry blockAir start).toRaw.2)[i.1 + 18]? := hraw
      _ = some ((wrapperMsg1Entry blockAir start).next_msg_bytes.get i) :=
            blockWrapperMsg1_raw_next blockAir start i
  · intro i
    have hraw :
        ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).toRaw.2)[i.1 + 2]? =
          ((wrapperMsg2Entry blockAir (start + 2)).toRaw.2)[i.1 + 2]? := by
      simpa using congrArg (fun payload => payload[i.1 + 2]?) hmsg2_raw
    apply Option.some.inj
    calc
      some ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).local_msg_bytes.get i)
          = ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).toRaw.2)[i.1 + 2]? := by
            symm
            exact mainWrapperMsg2_raw_local mainAir row i
      _ = ((wrapperMsg2Entry blockAir (start + 2)).toRaw.2)[i.1 + 2]? := hraw
      _ = some ((wrapperMsg2Entry blockAir (start + 2)).local_msg_bytes.get i) :=
            blockWrapperMsg2_raw_local blockAir (start + 2) i
  · intro i
    have hraw :
        ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).toRaw.2)[i.1 + 18]? =
          ((wrapperMsg2Entry blockAir (start + 2)).toRaw.2)[i.1 + 18]? := by
      simpa using congrArg (fun payload => payload[i.1 + 18]?) hmsg2_raw
    apply Option.some.inj
    calc
      some ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).next_msg_bytes.get i)
          = ((Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir row).toRaw.2)[i.1 + 18]? := by
            symm
            exact mainWrapperMsg2_raw_next mainAir row i
      _ = ((wrapperMsg2Entry blockAir (start + 2)).toRaw.2)[i.1 + 18]? := hraw
      _ = some ((wrapperMsg2Entry blockAir (start + 2)).next_msg_bytes.get i) :=
            blockWrapperMsg2_raw_next blockAir (start + 2) i

theorem get_multiplicity_inv_perm
    {bus bus' : List (FBB × List FBB)}
    (hperm : bus.Perm bus')
    (data : List FBB) :
    InteractionList.get_multiplicity bus data =
      InteractionList.get_multiplicity bus' data := by
  unfold InteractionList.get_multiplicity
  simpa using List.Perm.sum_eq ((hperm.filter (fun x : FBB × List FBB => x.2 == data)).map Prod.fst)

theorem mainWrapperTrace_perm_components
    (mainAir : CMain FBB ExtF) (rows : List ℕ) :
    (rows.flatMap (Sha2MainAir_sha256.constraints.wrapperBus_row mainAir)).Perm
      (rows.map (fun r => (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir r).toRaw) ++
        rows.map (fun r => (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir r).toRaw) ++
        rows.map (fun r => (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir r).toRaw)) := by
  let stateRaw := fun r =>
    (Sha2MainAir_sha256.constraints.wrapperStateEntry mainAir r).toRaw
  let msg1Raw := fun r =>
    (Sha2MainAir_sha256.constraints.wrapperMsg1Entry mainAir r).toRaw
  let msg2Raw := fun r =>
    (Sha2MainAir_sha256.constraints.wrapperMsg2Entry mainAir r).toRaw
  have hstate :
      (rows.flatMap (Sha2MainAir_sha256.constraints.wrapperBus_row mainAir)).Perm
        (rows.map stateRaw ++ rows.flatMap (fun r => [msg1Raw r, msg2Raw r])) := by
    simpa [stateRaw, msg1Raw, msg2Raw, Sha2MainAir_sha256.constraints.wrapperBus_row] using
      (List.map_append_flatMap_perm rows stateRaw (fun r => [msg1Raw r, msg2Raw r])).symm
  have hmsgs :
      (rows.flatMap (fun r => [msg1Raw r, msg2Raw r])).Perm
        (rows.map msg1Raw ++ rows.map msg2Raw) := by
    simpa [msg1Raw, msg2Raw, List.map_eq_flatMap] using
      (List.flatMap_append_perm rows (fun r => [msg1Raw r]) (fun r => [msg2Raw r])).symm
  exact hstate.trans <| by
    simpa [List.append_assoc] using hmsgs.append_left (rows.map stateRaw)

theorem blockWrapperTrace_perm_components
    (blockAir : CBlock FBB ExtF) (rows : List ℕ) :
    (rows.flatMap (Sha2BlockHasherVmAir_sha256.constraints.wrapperBus_row blockAir)).Perm
      (rows.map (fun r => (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir r).toRaw) ++
        rows.map (fun r => (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir r).toRaw) ++
        rows.map (fun r => (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir r).toRaw)) := by
  let stateRaw := fun r =>
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperStateEntry blockAir r).toRaw
  let msg1Raw := fun r =>
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir r).toRaw
  let msg2Raw := fun r =>
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir r).toRaw
  have hstate :
      (rows.flatMap (Sha2BlockHasherVmAir_sha256.constraints.wrapperBus_row blockAir)).Perm
        (rows.map stateRaw ++ rows.flatMap (fun r => [msg1Raw r, msg2Raw r])) := by
    simpa [stateRaw, msg1Raw, msg2Raw, Sha2BlockHasherVmAir_sha256.constraints.wrapperBus_row] using
      (List.map_append_flatMap_perm rows stateRaw (fun r => [msg1Raw r, msg2Raw r])).symm
  have hmsgs :
      (rows.flatMap (fun r => [msg1Raw r, msg2Raw r])).Perm
        (rows.map msg1Raw ++ rows.map msg2Raw) := by
    simpa [msg1Raw, msg2Raw, List.map_eq_flatMap] using
      (List.flatMap_append_perm rows (fun r => [msg1Raw r]) (fun r => [msg2Raw r])).symm
  exact hstate.trans <| by
    simpa [List.append_assoc] using hmsgs.append_left (rows.map stateRaw)

end SharedBridge

end Sha2CompressionBridge_sha256
