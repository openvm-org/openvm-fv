import VmExtensions.Soundness.Sha2MainAir_sha256.CoreBridge

set_option autoImplicit false
set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 20_000

namespace VmExtensions.Sha2CompressOpcode

open BabyBear
open Sha2CompressionBridge_sha256
open Sha2BlockHasherVmAir_sha256.BlockSpec
open Sha2MainAir_sha256.Soundness
open Sha2MainAir_sha256.constraints
open Sha2BlockHasherVmAir_sha256.constraints

theorem equiv_SHA256_COMPRESS
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
      (mult, [a, b, c, op]) ∈ Circuit.buses blockAir BitwiseBus →
      mult = 1 → a.val < 2 ^ 8 ∧ b.val < 2 ^ 8)
    (hPrevByteBound : ∀ i : Fin 32,
      (prev_state_byte mainAir i.1 row).val < 2 ^ 8) :
    let H : Vector UInt32 8 :=
      Vector.ofFn (fun w : Fin 8 =>
        UInt32.ofNat
          ((prev_state_byte mainAir (4 * w.1) row).val +
           (prev_state_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 8 +
           (prev_state_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 16 +
           (prev_state_byte mainAir (4 * w.1 + 3) row).val * 2 ^ 24))
    let M : Vector UInt32 16 :=
      Vector.ofFn (fun w : Fin 16 =>
        UInt32.ofNat
          ((message_byte mainAir (4 * w.1) row).val * 2 ^ 24 +
           (message_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 16 +
           (message_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 8 +
           (message_byte mainAir (4 * w.1 + 3) row).val))
    let outWords : Vector UInt32 8 :=
      Vector.ofFn (fun w : Fin 8 =>
        UInt32.ofNat
          ((new_state_byte mainAir (4 * w.1) row).val +
           (new_state_byte mainAir (4 * w.1 + 1) row).val * 2 ^ 8 +
           (new_state_byte mainAir (4 * w.1 + 2) row).val * 2 ^ 16 +
           (new_state_byte mainAir (4 * w.1 + 3) row).val * 2 ^ 24))
    (∀ i : Fin 32,
      (new_state_byte mainAir i.1 row).val < 2 ^ 8) ∧
    outWords = CryptoHash.SHA256.compressBlock H M := by
  exact equiv_SHA256_COMPRESS_word_explicit_bounded
    mainAir blockAir row
    hMainRow hMainEnabled hMainTraceFits hMainConstraints hSharedRawPerm
    hMainRot hBlockRot hBlockConstraints hBlockRawPerm hBlockTraceFits
    hBlockBitwiseWf hPrevByteBound

end VmExtensions.Sha2CompressOpcode
