/-
  Column-native opcode reconnect/export layer for KeccakfOpAir.

  Bridges the column-based local proof (`RowContract`, `row_soundness`) to
  `VmExtensions/Soundness/Keccakf/Wireup.lean`, proving
  `Keccakf.Soundness.KeccakfOpAirProperty opAir` directly.

  The proof uses row-bounded quantification and the disabled-or-contract split
  from `KeccakfOpAirProperty`.
-/
import VmExtensions.Soundness.KeccakfOpAir.Soundness
import VmExtensions.Soundness.Keccakf.Wireup
import VmExtensions.Airs.KeccakfOpAirViews

set_option autoImplicit false

open Keccakf.Interface
open KeccakfOp.Spec
open BabyBear

namespace Keccakf.Soundness.Concrete

open KeccakfOpAir
open KeccakfOpAir.Views
open KeccakfOpAir.constraints
open KeccakfOpAir.Soundness

variable {ExtF : Type} [Field ExtF]

lemma buffer_ptr_of_columns_bound
    (air : Valid_KeccakfOpAir FBB ExtF) (row : Nat)
    (h_mem : MemoryReadAssume air row)
    (h_ptr3 : ∃ n : Nat, buffer_ptr_limb_3 air row = ↑n ∧ n < 32) :
    bufferPtrOfColumns air row < memoryPtrBound := by
  have h0 : (buffer_ptr_limb_0 air row).val < 256 := h_mem.buf_limb_0_byte
  have h1 : (buffer_ptr_limb_1 air row).val < 256 := h_mem.buf_limb_1_byte
  have h2 : (buffer_ptr_limb_2 air row).val < 256 := h_mem.buf_limb_2_byte
  have h3 : (buffer_ptr_limb_3 air row).val < 32 := by
    exact fbb_val_lt_of_exists h_ptr3 (by decide)
  unfold bufferPtrOfColumns memoryPtrBound
  omega

/-- Column-native `RowLocalFacts` packaging from `RowContract`.
    Proves directly over the extracted column views. -/
lemma row_local_facts
    (air : Valid_KeccakfOpAir FBB ExtF)
    (row : Nat)
    (rc : RowContract air row) :
    RowLocalFacts
      (inputOfColumns decodeBusState air row)
      (outputOfColumns decodeBusState air row)
      (rdPtrOfColumns air row)
      (preMsgOfColumns air row)
      (postMsgOfColumns air row) := by
  let h_mem := rc.mem_rd
  refine {
    execution := ?_,
    instruction := ?_,
    memory := ?_,
    pre_flag := ?_,
    post_flag := ?_,
    pre_timestamp := ?_,
    post_timestamp := ?_,
    timestamp_lt := ?_
  }
  · refine {
      next_pc := ?_,
      end_timestamp := ?_
    }
    · rfl
    · rfl
  · refine {
      rd_ptr_lt := ?_
    }
    exact h_mem.rd_ptr_bound
  · refine {
      buffer_ptr_lt := ?_,
      register_read := ?_,
      buffer_writes := ?_
    }
    · exact buffer_ptr_of_columns_bound air row h_mem (ptr_limb3_lt rc)
    ·
      refine ⟨{
        addressSpace := REGISTER_AS
        ptr := rdPtrOfColumns air row
        timestamp := (timestamp air row).val
        value := bufferPtrOfColumns air row
      }, rfl, rfl, rfl, rfl⟩
    ·
      refine ⟨{
        addressSpace := MEMORY_AS
        ptr := fun j => bufferPtrOfColumns air row + WORD_BYTES * j.val
        timestamp := fun j => (timestamp air row).val + 1 + j.val
        prevWord := fun j => spongeWord (decodeBusState (preStateOfColumns air row)) j
        data := fun j => spongeWord (decodeBusState (postStateOfColumns air row)) j
      }, rfl, ?_, ?_, ?_, ?_⟩
      · intro j
        rfl
      · intro j
        rfl
      · intro j
        rfl
      · intro j
        rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact rc.timestamp_lt

/-- Column-native `KeccakfOpRowLocalContract` from `RowContract`.
    Row-local facts plus decode links — the decode links are definitional
    equalities (`input_preimage_eq_decode`, `output_postimage_eq_decode`),
    so no witness rewrites are needed. -/
lemma row_local_contract
    (air : Valid_KeccakfOpAir FBB ExtF)
    (row : Nat)
    (rc : RowContract air row) :
    Keccakf.Soundness.KeccakfOpRowLocalContract air row :=
  ⟨row_local_facts air row rc,
   input_preimage_eq_decode air row,
   output_postimage_eq_decode air row⟩

/-- Export theorem: the local keccakf opcode-row proof discharges
    `KeccakfOpAirProperty` from row-bounded circuit assumptions. -/
theorem keccakf_op_air_soundness
    (opAir : Valid_KeccakfOpAir FBB ExtF)
    (h_allHold : ∀ row (h_row : row ≤ opAir.last_row),
      allHold_simplified opAir row h_row)
    (h_axioms : ∀ row, row ≤ opAir.last_row →
      axiomsPerRow opAir row)
    (h_wfAssume : ∀ row, row ≤ opAir.last_row →
      wf_propertiesToAssumePerRow opAir row) :
    Keccakf.Soundness.KeccakfOpAirProperty opAir := by
  intro row h_row_le
  have h_sound :=
    row_soundness opAir row h_row_le
      (rows_of_allHold_simplified (h_allHold row h_row_le))
      (h_axioms row h_row_le)
      (h_wfAssume row h_row_le)
  rcases h_sound.2 with h_disabled | h_enabled
  · exact Or.inl h_disabled.1
  · exact Or.inr (row_local_contract opAir row h_enabled.2)

end Keccakf.Soundness.Concrete
