import VmExtensions.Constraints.KeccakfOpAir
import VmExtensions.Soundness.Keccakf.Interface
import VmExtensions.Spec.KeccakfOp
import OpenvmFv.Fundamentals.BabyBear

set_option autoImplicit false

open Keccakf.Interface
open KeccakfOp.Spec
open BabyBear

namespace KeccakfOpAir.Views

open KeccakfOpAir.constraints

variable {ExtF : Type} [Field ExtF]

/-- The register-pointer column interpreted as a natural number. -/
def rdPtrOfColumns
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) : Nat :=
  (rd_ptr air row).val

/-- The buffer-pointer limbs interpreted as a little-endian `u32` natural. -/
def bufferPtrOfColumns
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) : Nat :=
  (buffer_ptr_limb_0 air row).val +
    (buffer_ptr_limb_1 air row).val * 256 +
    (buffer_ptr_limb_2 air row).val * 65536 +
    (buffer_ptr_limb_3 air row).val * 16777216

/-- The keccak pre-state carried by one opcode row, interpreted as 100
    little-endian `u16` limbs. -/
noncomputable def preStateOfColumns
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) : KeccakBusState :=
  Vector.ofFn fun i =>
    UInt16.ofNat <|
      (preimage air row (2 * i.val)).val +
        (preimage air row (2 * i.val + 1)).val * 256

/-- The keccak post-state carried by one opcode row, interpreted as 100
    little-endian `u16` limbs. -/
noncomputable def postStateOfColumns
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) : KeccakBusState :=
  Vector.ofFn fun i =>
    UInt16.ofNat <|
      (postimage air row (2 * i.val)).val +
        (postimage air row (2 * i.val + 1)).val * 256

/-- The opcode input view induced by the extracted opcode row columns. -/
noncomputable def inputOfColumns
    (decodeBusState : KeccakBusState → SpongeState)
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) : KeccakfOpInput where
  pc := (pc air row).val
  start_timestamp := (timestamp air row).val
  buffer_ptr := bufferPtrOfColumns air row
  preimage := decodeBusState (preStateOfColumns air row)

/-- The opcode output view induced by the extracted opcode row columns. -/
noncomputable def outputOfColumns
    (decodeBusState : KeccakBusState → SpongeState)
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) : KeccakfOpOutput where
  next_pc := (pc air row).val + 4
  end_timestamp := (timestamp air row).val + TIMESTAMP_DELTA
  postimage := decodeBusState (postStateOfColumns air row)

/-- The normalized pre-state message induced by the extracted opcode row. -/
noncomputable def preMsgOfColumns
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) : KeccakStateMsg :=
  mkPreMsg (timestamp air row).val (preStateOfColumns air row)

/-- The normalized post-state message induced by the extracted opcode row. -/
noncomputable def postMsgOfColumns
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) : KeccakStateMsg :=
  mkPostMsg (timestamp air row).val (postStateOfColumns air row)

/-! ## Direct column-native facts

These are premise-free `rfl` facts about the column-native message views.
-/

/-- The pre-state message is always flagged as non-post (by construction). -/
theorem pre_flag
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) :
    (preMsgOfColumns air row).isPost = false := by
  rfl

/-- The post-state message is always flagged as post (by construction). -/
theorem post_flag
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) :
    (postMsgOfColumns air row).isPost = true := by
  rfl

/-- The pre and post messages share the same timestamp (by construction). -/
theorem same_timestamp
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) :
    (preMsgOfColumns air row).timestamp = (postMsgOfColumns air row).timestamp := by
  rfl

/-- The preimage decode link holds definitionally:
    `(inputOfColumns decodeBusState air row).preimage = decodeBusState (preMsgOfColumns air row).state`. -/
theorem input_preimage_eq_decode
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) :
    (inputOfColumns decodeBusState air row).preimage =
      decodeBusState (preMsgOfColumns air row).state := by
  rfl

/-- The postimage decode link holds definitionally:
    `(outputOfColumns decodeBusState air row).postimage = decodeBusState (postMsgOfColumns air row).state`. -/
theorem output_postimage_eq_decode
    (air : KeccakfOpAir.Valid_KeccakfOpAir FBB ExtF) (row : Nat) :
    (outputOfColumns decodeBusState air row).postimage =
      decodeBusState (postMsgOfColumns air row).state := by
  rfl

end KeccakfOpAir.Views
