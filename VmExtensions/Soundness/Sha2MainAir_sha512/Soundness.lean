import VmExtensions.Soundness.Sha2MainAir_sha512.CoreBridge

set_option autoImplicit false
set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 20_000

namespace VmExtensions.Sha2CompressOpcode

open BabyBear
open Sha2CompressionBridge_sha512
open Sha2BlockHasherVmAir_sha512.BlockSpec
open Sha2MainAir_sha512.Soundness
open Sha2MainAir_sha512.constraints
open Sha2BlockHasherVmAir_sha512.constraints

/-- Explicit output equivalence for one SHA-512 `compress` row. -/
theorem equiv_SHA512_COMPRESS
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF)
    (blockAir : CBlock FBB ExtF)
    (row : ℕ)
    (hMainRow : row ≤ Circuit.last_row mainAir)
    (hMainEnabled : is_enabled mainAir row = 1)
    (hMainTraceFits : Circuit.last_row mainAir + 1 < BB_prime)
    (hMainConstraints : mainTraceConstraints mainAir)
    (hSharedRawPerm : InteractionList.is_balanced
      (Circuit.buses mainAir Sha2MainWrapperBus ++ Circuit.buses blockAir Sha2WrapperBus))
    (hMainRot :
      (∀ column row', row' < Circuit.last_row mainAir →
        Circuit.main mainAir (id := 0) (column := column) (row := row') (rotation := 1) =
          Circuit.main mainAir (id := 0) (column := column) (row := row' + 1) (rotation := 0)) ∧
      (∀ column,
        Circuit.main mainAir (id := 0) (column := column)
            (row := Circuit.last_row mainAir) (rotation := 1) =
          Circuit.main mainAir (id := 0) (column := column) (row := 0) (rotation := 0)))
    (hBlockRot :
      (∀ column row', row' < Circuit.last_row blockAir →
        Circuit.main blockAir (id := 0) (column := column) (row := row') (rotation := 1) =
          Circuit.main blockAir (id := 0) (column := column) (row := row' + 1) (rotation := 0)) ∧
      (∀ column,
        Circuit.main blockAir (id := 0) (column := column)
            (row := Circuit.last_row blockAir) (rotation := 1) =
          Circuit.main blockAir (id := 0) (column := column) (row := 0) (rotation := 0)))
    (hBlockConstraints : blockHasherConstraints blockAir)
    (hBlockRawPerm : InteractionList.is_balanced (Circuit.buses blockAir Sha2PrivateBus))
    (hBlockTraceFits : Circuit.last_row blockAir + 1 < BB_prime)
    (hBlockBitwiseWf : ∀ mult a b c op,
      (mult, [a, b, c, op]) ∈ Circuit.buses blockAir Sha2BitwiseBus →
      mult = 1 → a.val < 2 ^ 8 ∧ b.val < 2 ^ 8)
    (hPrevByteBound : ∀ i : Fin 64,
      (prev_state_byte mainAir i.1 row).val < 2 ^ 8) :
    let H : Vector UInt64 8 :=
      Vector.ofFn (fun w : Fin 8 =>
        UInt64.ofNat
          ((prev_state_byte mainAir (8 * w.1) row).val +
           (prev_state_byte mainAir (8 * w.1 + 1) row).val * 2 ^ 8 +
           (prev_state_byte mainAir (8 * w.1 + 2) row).val * 2 ^ 16 +
           (prev_state_byte mainAir (8 * w.1 + 3) row).val * 2 ^ 24 +
           (prev_state_byte mainAir (8 * w.1 + 4) row).val * 2 ^ 32 +
           (prev_state_byte mainAir (8 * w.1 + 5) row).val * 2 ^ 40 +
           (prev_state_byte mainAir (8 * w.1 + 6) row).val * 2 ^ 48 +
           (prev_state_byte mainAir (8 * w.1 + 7) row).val * 2 ^ 56))
    let M : Vector UInt64 16 :=
      Vector.ofFn (fun w : Fin 16 =>
        UInt64.ofNat
          ((message_byte mainAir (8 * w.1) row).val * 2 ^ 56 +
           (message_byte mainAir (8 * w.1 + 1) row).val * 2 ^ 48 +
           (message_byte mainAir (8 * w.1 + 2) row).val * 2 ^ 40 +
           (message_byte mainAir (8 * w.1 + 3) row).val * 2 ^ 32 +
           (message_byte mainAir (8 * w.1 + 4) row).val * 2 ^ 24 +
           (message_byte mainAir (8 * w.1 + 5) row).val * 2 ^ 16 +
           (message_byte mainAir (8 * w.1 + 6) row).val * 2 ^ 8 +
           (message_byte mainAir (8 * w.1 + 7) row).val))
    let outWords : Vector UInt64 8 :=
      Vector.ofFn (fun w : Fin 8 =>
        UInt64.ofNat
          ((new_state_byte mainAir (8 * w.1) row).val +
           (new_state_byte mainAir (8 * w.1 + 1) row).val * 2 ^ 8 +
           (new_state_byte mainAir (8 * w.1 + 2) row).val * 2 ^ 16 +
           (new_state_byte mainAir (8 * w.1 + 3) row).val * 2 ^ 24 +
           (new_state_byte mainAir (8 * w.1 + 4) row).val * 2 ^ 32 +
           (new_state_byte mainAir (8 * w.1 + 5) row).val * 2 ^ 40 +
           (new_state_byte mainAir (8 * w.1 + 6) row).val * 2 ^ 48 +
           (new_state_byte mainAir (8 * w.1 + 7) row).val * 2 ^ 56))
    (∀ i : Fin 64,
      (new_state_byte mainAir i.1 row).val < 2 ^ 8) ∧
    outWords = CryptoHash.SHA512.compressBlock H M := by
  exact equiv_SHA512_COMPRESS_word_explicit_bounded
    mainAir blockAir row
    hMainRow hMainEnabled hMainTraceFits hMainConstraints hSharedRawPerm
    hMainRot hBlockRot hBlockConstraints hBlockRawPerm hBlockTraceFits
    hBlockBitwiseWf hPrevByteBound

end VmExtensions.Sha2CompressOpcode
