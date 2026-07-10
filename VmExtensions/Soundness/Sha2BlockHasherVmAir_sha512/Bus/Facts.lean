/-
Bus-derived proof facts for the SHA-512 block hasher.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.SpecFacts
import VmExtensions.Constraints.Sha2BlockHasherSubAirBus_sha512
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Bus.PrivateChaining
import OpenvmFv.Fundamentals.BabyBear
import OpenvmFv.Fundamentals.Interaction

set_option autoImplicit false

set_option maxHeartbeats 1_000_000_000

namespace Sha2BlockHasherVmAir_sha512.Soundness.BusFacts

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints
open Sha2BlockHasherVmAir_sha512.BlockSpec

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

private lemma forall_id_map_get {α : Type} {f : α → Prop} {l : List α}
    (h : List.Forall id (l.map f)) {n : ℕ} (hn : n < l.length) :
    f (l[n]) := by
  induction l generalizing n with
  | nil => exact absurd hn (Nat.not_lt_zero _)
  | cons a t ih =>
    rw [List.map_cons, List.forall_cons] at h
    cases n with
    | zero => exact h.1
    | succ n => exact ih h.2 (Nat.lt_of_succ_lt_succ hn)

private theorem carry_entry_assume
    (air : C FBB ExtF) (row i j : ℕ)
    (hi : i < 4) (hj : j < 4)
    (h_wf : bitwise_lookup_send_properties air row) :
    Interaction.BusEntry.assume FBB (bitwiseCarryBusEntry air i j row) := by
  have hidx : 4 * i + j < (_bitwiseBus_row air row).length := by
    have : 4 * i + j < 48 := by omega
    simpa [_bitwiseBus_row] using this
  have hgeneric : Interaction.BusEntry.assume FBB ((_bitwiseBus_row air row)[4 * i + j]) := by
    simpa [bitwise_lookup_send_properties, propertiesToAssume] using
      (forall_id_map_get
        (f := Interaction.BusEntry.assume FBB)
        (l := _bitwiseBus_row air row)
        h_wf
        (n := 4 * i + j)
        hidx)
  have hget : (_bitwiseBus_row air row)[4 * i + j] = bitwiseCarryBusEntry air i j row := by
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hi_cases with rfl | rfl | rfl | rfl <;>
      rcases hj_cases with rfl | rfl | rfl | rfl <;>
      rfl
  simpa [hget] using hgeneric

private theorem digest_entry_assume
    (air : C FBB ExtF) (row word pair : ℕ)
    (hw : word < 8) (hp : pair < 4)
    (h_wf : bitwise_lookup_send_properties air row) :
    Interaction.BusEntry.assume FBB (bitwiseDigestBusEntry air word pair row) := by
  have hidx : 16 + (4 * word + pair) < (_bitwiseBus_row air row).length := by
    have : 16 + (4 * word + pair) < 48 := by omega
    simpa [_bitwiseBus_row] using this
  have hgeneric :
      Interaction.BusEntry.assume FBB ((_bitwiseBus_row air row)[16 + (4 * word + pair)]) := by
    simpa [bitwise_lookup_send_properties, propertiesToAssume] using
      (forall_id_map_get
        (f := Interaction.BusEntry.assume FBB)
        (l := _bitwiseBus_row air row)
        h_wf
        (n := 16 + (4 * word + pair))
        hidx)
  have hget :
      (_bitwiseBus_row air row)[16 + (4 * word + pair)] = bitwiseDigestBusEntry air word pair row := by
    have hw_cases :
        word = 0 ∨ word = 1 ∨ word = 2 ∨ word = 3 ∨
        word = 4 ∨ word = 5 ∨ word = 6 ∨ word = 7 := by
      omega
    have hp_cases : pair = 0 ∨ pair = 1 ∨ pair = 2 ∨ pair = 3 := by omega
    rcases hw_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hp_cases with rfl | rfl | rfl | rfl <;>
      rfl
  simpa [hget] using hgeneric

theorem carry_a_range_of_bus
    (air : C FBB ExtF) (row i j : ℕ)
    (hi : i < 4) (hj : j < 4)
    (h_round : is_round_row air row = 1)
    (h_wf : bitwise_lookup_send_properties air row) :
    (carry_a air i j row).val < 256 := by
  have hentry := carry_entry_assume air row i j hi hj h_wf
  have hwf := hentry (by simpa [bitwiseCarryBusEntry, h_round])
  simpa [bitwiseCarryBusEntry] using hwf.1

theorem carry_e_range_of_bus
    (air : C FBB ExtF) (row i j : ℕ)
    (hi : i < 4) (hj : j < 4)
    (h_round : is_round_row air row = 1)
    (h_wf : bitwise_lookup_send_properties air row) :
    (carry_e air i j row).val < 256 := by
  have hentry := carry_entry_assume air row i j hi hj h_wf
  have hwf := hentry (by simpa [bitwiseCarryBusEntry, h_round])
  simpa [bitwiseCarryBusEntry] using hwf.2.1

theorem carry_range_of_bus
    (air : C FBB ExtF) (row i j : ℕ)
    (hi : i < 4) (hj : j < 4)
    (h_round : is_round_row air row = 1)
    (h_wf : bitwise_lookup_send_properties air row) :
    (carry_a air i j row).val < 256 ∧ (carry_e air i j row).val < 256 :=
  ⟨carry_a_range_of_bus air row i j hi hj h_round h_wf,
   carry_e_range_of_bus air row i j hi hj h_round h_wf⟩

theorem next_final_hash_byte_range_of_bus
    (air : C FBB ExtF) (row word byte : ℕ)
    (hw : word < 8) (hb : byte < 8)
    (h_next_digest : next_is_digest_row air row = 1)
    (h_wf : bitwise_lookup_send_properties air row) :
    (next_final_hash air word byte row).val < 256 := by
  interval_cases byte
  · have hentry := digest_entry_assume air row word 0 hw (by omega) h_wf
    have hwf := hentry (by simpa [bitwiseDigestBusEntry, h_next_digest])
    simpa [bitwiseDigestBusEntry] using hwf.1
  · have hentry := digest_entry_assume air row word 0 hw (by omega) h_wf
    have hwf := hentry (by simpa [bitwiseDigestBusEntry, h_next_digest])
    simpa [bitwiseDigestBusEntry] using hwf.2.1
  · have hentry := digest_entry_assume air row word 1 hw (by omega) h_wf
    have hwf := hentry (by simpa [bitwiseDigestBusEntry, h_next_digest])
    simpa [bitwiseDigestBusEntry] using hwf.1
  · have hentry := digest_entry_assume air row word 1 hw (by omega) h_wf
    have hwf := hentry (by simpa [bitwiseDigestBusEntry, h_next_digest])
    simpa [bitwiseDigestBusEntry] using hwf.2.1
  · have hentry := digest_entry_assume air row word 2 hw (by omega) h_wf
    have hwf := hentry (by simpa [bitwiseDigestBusEntry, h_next_digest])
    simpa [bitwiseDigestBusEntry] using hwf.1
  · have hentry := digest_entry_assume air row word 2 hw (by omega) h_wf
    have hwf := hentry (by simpa [bitwiseDigestBusEntry, h_next_digest])
    simpa [bitwiseDigestBusEntry] using hwf.2.1
  · have hentry := digest_entry_assume air row word 3 hw (by omega) h_wf
    have hwf := hentry (by simpa [bitwiseDigestBusEntry, h_next_digest])
    simpa [bitwiseDigestBusEntry] using hwf.1
  · have hentry := digest_entry_assume air row word 3 hw (by omega) h_wf
    have hwf := hentry (by simpa [bitwiseDigestBusEntry, h_next_digest])
    simpa [bitwiseDigestBusEntry] using hwf.2.1

theorem digest_final_hash_byte_range_of_bus
    (air : C FBB ExtF) (row word byte : ℕ)
    (hw : word < 8) (hb : byte < 8)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (h_digest : is_digest_row air row = 1)
    (h_wf_prev : bitwise_lookup_send_properties air (prevRow air row)) :
    (final_hash air word byte row).val < 256 := by
  have hprev_valid : prevRow air row ≤ Circuit.last_row air := by
    by_cases hzero : row = 0
    · simp [prevRow, hzero]
    · have hpos : 0 < row := Nat.pos_of_ne_zero hzero
      have : row - 1 ≤ Circuit.last_row air := by omega
      simpa [prevRow, hzero, Nat.succ_pred_eq_of_pos hpos] using this
  have hnext_eq : nextRow air (prevRow air row) = row := by
    by_cases hzero : row = 0
    · simp [prevRow, nextRow, hzero]
    · have hpos : 0 < row := Nat.pos_of_ne_zero hzero
      have hne : row - 1 ≠ Circuit.last_row air := by omega
      simp [prevRow, nextRow, hzero, hne]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  have h_next_digest : next_is_digest_row air (prevRow air row) = 1 := by
    rw [next_is_digest_row_eq_nextRow air hrot (prevRow air row) hprev_valid, hnext_eq]
    exact h_digest
  have hrange :=
    next_final_hash_byte_range_of_bus air (prevRow air row) word byte hw hb h_next_digest h_wf_prev
  have hnext_final :
      next_final_hash air word byte (prevRow air row) = final_hash air word byte row := by
    by_cases hprev_lt : prevRow air row < Circuit.last_row air
    · rw [next_final_hash, final_hash, next_main_eq_main_succ air hrot
        (615 + 8 * word + byte) (prevRow air row) hprev_lt]
      have hsucc_eq : prevRow air row + 1 = row := by
        simpa [nextRow, hprev_lt.ne] using hnext_eq
      simpa [hsucc_eq]
    · have hprev_last : prevRow air row = Circuit.last_row air :=
        le_antisymm hprev_valid (Nat.le_of_not_lt hprev_lt)
      have hrow_zero : row = 0 := by
        simpa [nextRow, hprev_last] using hnext_eq
      simpa [next_final_hash, final_hash, hprev_last, hrow_zero] using
        last_row_main_eq_first air hrot (615 + 8 * word + byte)
  simpa [hnext_final] using hrange

private theorem range_loop_four : List.range.loop 4 [] = [0, 1, 2, 3] := by decide

private theorem range_loop_eight : List.range.loop 8 [] = [0, 1, 2, 3, 4, 5, 6, 7] := by
  decide

@[simp] theorem privateBus_send_data_get?_hash
    (air : C FBB ExtF) (row word limb : ℕ)
    (hw : word < 8) (hl : limb < 4) :
    (privateBus_send_data air row)[4 * word + limb]? =
      some (composed_hash_u16 air word limb row) := by
  interval_cases word <;> interval_cases limb <;>
    simp [privateBus_send_data, List.range, range_loop_four, range_loop_eight]

@[simp] theorem privateBus_recv_data_get?_prev_hash
    (air : C FBB ExtF) (row word limb : ℕ)
    (hw : word < 8) (hl : limb < 4) :
    (privateBus_recv_data air row)[4 * word + limb]? =
      some (prev_hash air word limb row) := by
  interval_cases word <;> interval_cases limb <;>
    simp [privateBus_recv_data, List.range, range_loop_four, range_loop_eight]

theorem block_chaining_of_private_bus
    (air : C FBB ExtF) (r1 r2 : ℕ)
    (h_private : privateBusChainingSupported air)
    (hr1_valid : r1 ≤ Circuit.last_row air)
    (hr2_valid : r2 ≤ Circuit.last_row air)
    (h_dig1 : is_digest_row air r1 = 1)
    (h_dig2 : is_digest_row air r2 = 1)
    (h_gbi : global_block_idx air r2 = global_block_idx air r1 + 1)
    (h_not_last : next_padding_flag air r1 = 0) :
    (∀ word limb, word < 8 → limb < 4 →
      composed_hash_u16 air word limb r1 = prev_hash air word limb r2) ∧
    global_block_idx air r1 + 1 = global_block_idx air r2 := by
  have hkey : private_bus_next_gbi air r1 = global_block_idx air r2 := by
    calc
      private_bus_next_gbi air r1
          = global_block_idx air r1 + 1 := by
              simp [private_bus_next_gbi, h_not_last]
      _ = global_block_idx air r2 := h_gbi.symm
  have hmsg := h_private r1 r2 hr1_valid hr2_valid h_dig1 h_dig2 hkey
  refine ⟨?_, h_gbi.symm⟩
  intro word limb hw hl
  have hentry := congrArg (fun xs => xs[4 * word + limb]?) hmsg
  simpa [privateBus_send_data_get?_hash air r1 word limb hw hl,
    privateBus_recv_data_get?_prev_hash air r2 word limb hw hl] using hentry

end Sha2BlockHasherVmAir_sha512.Soundness.BusFacts
