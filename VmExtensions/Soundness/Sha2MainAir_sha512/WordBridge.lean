import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.Defs
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.FieldArithmetic
import VmExtensions.Soundness.Sha2MainAir_sha512.ColumnBridge

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 20_000

namespace Sha2CompressionBridge_sha512

open BabyBear
open Sha2BlockHasherVmAir_sha512.BlockSpec
open Sha2MainAir_sha512.Soundness

/-- The SHA-512 state is stored as 64 bytes, grouped into eight little-endian words. -/
abbrev StateBytes := Vector (BitVec 8) 64

private def wordByteLE (w : Word) (byte : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((w.toNat / (256 ^ byte)) % 256)

private def workingVarAt (state : WorkingVars) (word : Nat) : Word :=
  match word with
  | 0 => state.a
  | 1 => state.b
  | 2 => state.c
  | 3 => state.d
  | 4 => state.e
  | 5 => state.f
  | 6 => state.g
  | 7 => state.h
  | _ => 0

/-- Converts working variables to the opcode's little-endian byte layout. -/
def workingVarsToStateBytes (state : WorkingVars) : StateBytes :=
  Vector.ofFn (fun i =>
    let word := i.val / 8
    let byte := i.val % 8
    wordByteLE (workingVarAt state word) byte)

/-- Pure SHA-512 compression on decoded state and input words. -/
def sha512CompressWords (initialState : WorkingVars) (messageWords : Array Word) : WorkingVars :=
  let schedule := expandSchedule messageWords
  let finalState := (compressionTrace initialState schedule)[80]!
  initialState.add finalState

section SharedBridge

open Sha2BlockHasherVmAir_sha512.constraints

variable {CMain CBlock : Type → Type → Type} {ExtF : Type}
  [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]

def beFieldBytesNat (bytes : Fin 8 → FBB) : Nat :=
  (bytes ⟨0, by decide⟩).val * 2 ^ 56 +
    (bytes ⟨1, by decide⟩).val * 2 ^ 48 +
    (bytes ⟨2, by decide⟩).val * 2 ^ 40 +
    (bytes ⟨3, by decide⟩).val * 2 ^ 32 +
    (bytes ⟨4, by decide⟩).val * 2 ^ 24 +
    (bytes ⟨5, by decide⟩).val * 2 ^ 16 +
    (bytes ⟨6, by decide⟩).val * 256 +
    (bytes ⟨7, by decide⟩).val

def beFieldBytesToWord (bytes : Fin 8 → FBB) : Word :=
  UInt64.ofNat (beFieldBytesNat bytes)

def rowMessageWord
    (mainAir : CMain FBB ExtF) (row : ℕ) (word : Fin 16) : Word :=
  beFieldBytesToWord
    (fun byte => Sha2MainAir_sha512.constraints.message_byte mainAir (8 * word.1 + byte.1) row)

def rowMessageWords
    (mainAir : CMain FBB ExtF) (row : ℕ) : Array Word :=
  Array.ofFn (fun word : Fin 16 => rowMessageWord mainAir row word)

private def bitsWordByte (bits : BitsWord) (byteIdx : Fin 8) : FBB :=
  ∑ bit : Fin 8, bits ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩ * 2 ^ bit.1

private theorem bitsWordByte_eq_nat_sum
    (bits : BitsWord) (hb : isBitsWord bits) (byteIdx : Fin 8) :
    bitsWordByte bits byteIdx =
      ((∑ bit : Fin 8,
          (bits ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) : FBB) := by
  rw [bitsWordByte, Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro bit _
  rcases hb ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩ with hbit | hbit <;> simp [hbit]

private theorem bitsWordByte_nat_sum_lt
    (bits : BitsWord) (hb : isBitsWord bits) (byteIdx : Fin 8) :
    (∑ bit : Fin 8,
        (bits ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) < 2 ^ 8 := by
  have hle :
      (∑ bit : Fin 8,
          (bits ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) ≤
        ∑ bit : Fin 8, 2 ^ bit.1 := by
    refine Finset.sum_le_sum ?_
    intro bit _
    rcases hb ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩ with hbit | hbit <;> simp [hbit]
  have hpow : (∑ bit : Fin 8, 2 ^ bit.1 : ℕ) < 2 ^ 8 := by
    norm_num [Fin.sum_univ_eq_sum_range]
  exact lt_of_le_of_lt hle hpow

private theorem bitsWordByte_val_eq_nat_sum
    (bits : BitsWord) (hb : isBitsWord bits) (byteIdx : Fin 8) :
    (bitsWordByte bits byteIdx).val =
      ∑ bit : Fin 8,
        (bits ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 := by
  have hs_lt :
      (∑ bit : Fin 8,
          (bits ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) < 2 ^ 8 :=
    bitsWordByte_nat_sum_lt bits hb byteIdx
  have hs_prime :
      (∑ bit : Fin 8,
          (bits ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) < BB_prime := by
    exact lt_trans hs_lt (by norm_num)
  have hcast := congrArg Fin.val (bitsWordByte_eq_nat_sum bits hb byteIdx)
  change
    (bitsWordByte bits byteIdx).val =
      (∑ bit : Fin 8,
        (bits ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) % BB_prime at hcast
  rw [Nat.mod_eq_of_lt hs_prime] at hcast
  exact hcast

private theorem bitsWordByte_val_lt
    (bits : BitsWord) (hb : isBitsWord bits) (byteIdx : Fin 8) :
    (bitsWordByte bits byteIdx).val < 256 := by
  have hs_lt :
      (∑ bit : Fin 8,
          (bits ⟨(7 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) < 2 ^ 8 :=
    bitsWordByte_nat_sum_lt bits hb byteIdx
  rw [bitsWordByte_val_eq_nat_sum bits hb byteIdx]
  norm_num at hs_lt ⊢
  exact hs_lt

private theorem byte_pair_val_eq (lo hi : FBB)
    (hlo : lo.val < 256) (hhi : hi.val < 256) :
    (lo + hi * 256).val = lo.val + hi.val * 256 := by
  have h256 : ((256 : FBB)).val = 256 := by
    exact ZMod.val_natCast_of_lt (by decide : 256 < BB_prime)
  have hmul_lt_nat : hi.val * 256 < BB_prime := by
    have hmul_le : hi.val * 256 ≤ 255 * 256 := by omega
    exact lt_of_le_of_lt hmul_le (by norm_num)
  have hmul : (hi * (256 : FBB)).val = hi.val * 256 := by
    rw [Fin.val_mul]
    rw [h256, Nat.mod_eq_of_lt hmul_lt_nat]
  have hadd_nat : lo.val + hi.val * 256 < BB_prime := by
    have hsum_le : lo.val + hi.val * 256 ≤ 255 + 255 * 256 := by omega
    exact lt_of_le_of_lt hsum_le (by norm_num)
  have hadd : lo.val + (hi * (256 : FBB)).val < BB_prime := by
    simpa [hmul] using hadd_nat
  have hadd' : (lo + hi * (256 : FBB)).val = lo.val + (hi * (256 : FBB)).val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt hadd]
  calc
    (lo + hi * 256).val = lo.val + (hi * (256 : FBB)).val := by simpa using hadd'
    _ = lo.val + hi.val * 256 := by rw [hmul]

private theorem sum_range8_eq_fin_sum (g : ℕ → FBB) :
    (∑ i ∈ Finset.range 8, g i) = ∑ i : Fin 8, g i.1 := by
  symm
  simpa using (Fin.sum_univ_eq_sum_range (f := g) (n := 8))

private theorem composeU16Limb0_eq_bitsWordBytes (bits : BitsWord) :
    composeU16Limb bits ⟨0, by decide⟩ =
      bitsWordByte bits ⟨7, by decide⟩ + bitsWordByte bits ⟨6, by decide⟩ * 256 := by
  rw [composeU16Limb_range_eq]
  have hsplit :
      (∑ i ∈ Finset.range 16,
        (if hi : i < 16 then bits ⟨i + 16 * (0 : ℕ), by omega⟩ * 2 ^ i else 0)) =
        (∑ i ∈ Finset.range 8,
          (if hi : i < 16 then bits ⟨i, by omega⟩ * 2 ^ i else 0)) +
          ∑ i ∈ Finset.range 8,
            (if hi : 8 + i < 16 then bits ⟨8 + i, by omega⟩ * 2 ^ (8 + i) else 0) := by
    simpa using
      (Finset.sum_range_add
        (f := fun i => if hi : i < 16 then bits ⟨i, by omega⟩ * 2 ^ i else 0)
        8 8)
  rw [hsplit]
  have hlow :
      (∑ i ∈ Finset.range 8,
        (if hi : i < 16 then bits ⟨i, by omega⟩ * 2 ^ i else 0)) =
        bitsWordByte bits ⟨7, by decide⟩ := by
    calc
      (∑ i ∈ Finset.range 8,
        (if hi : i < 16 then bits ⟨i, by omega⟩ * 2 ^ i else 0)) =
          ∑ i : Fin 8,
            (if hi : i.1 < 16 then bits ⟨i.1, by omega⟩ * 2 ^ i.1 else 0) := by
            exact sum_range8_eq_fin_sum
              (g := fun i => if hi : i < 16 then bits ⟨i, by omega⟩ * 2 ^ i else 0)
      _ = ∑ i : Fin 8, bits ⟨i.1, by omega⟩ * 2 ^ i.1 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hlt : i.1 < 16 := by omega
            simp [hlt]
      _ = bitsWordByte bits ⟨7, by decide⟩ := by
            simp [bitsWordByte]
  have hhigh :
      (∑ i ∈ Finset.range 8,
        (if hi : 8 + i < 16 then bits ⟨8 + i, by omega⟩ * 2 ^ (8 + i) else 0)) =
        bitsWordByte bits ⟨6, by decide⟩ * 256 := by
    calc
      (∑ i ∈ Finset.range 8,
        (if hi : 8 + i < 16 then bits ⟨8 + i, by omega⟩ * 2 ^ (8 + i) else 0)) =
          ∑ i : Fin 8,
            (if hi : 8 + i.1 < 16 then bits ⟨8 + i.1, by omega⟩ * 2 ^ (8 + i.1) else 0) := by
            exact sum_range8_eq_fin_sum
              (g := fun i => if hi : 8 + i < 16 then bits ⟨8 + i, by omega⟩ * 2 ^ (8 + i) else 0)
      _ = ∑ i : Fin 8, bits ⟨8 + i.1, by omega⟩ * 2 ^ (8 + i.1) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hlt : 8 + i.1 < 16 := by omega
            simp [hlt]
      _ = ∑ i : Fin 8, (bits ⟨8 + i.1, by omega⟩ * 2 ^ i.1) * 256 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              norm_num [pow_add, mul_assoc, mul_left_comm, mul_comm]
      _ = (∑ i : Fin 8, bits ⟨8 + i.1, by omega⟩ * 2 ^ i.1) * 256 := by
            rw [Finset.sum_mul]
      _ = bitsWordByte bits ⟨6, by decide⟩ * 256 := by
            simp [bitsWordByte]
  rw [hlow, hhigh]

private theorem composeU16Limb1_eq_bitsWordBytes (bits : BitsWord) :
    composeU16Limb bits ⟨1, by decide⟩ =
      bitsWordByte bits ⟨5, by decide⟩ + bitsWordByte bits ⟨4, by decide⟩ * 256 := by
  rw [composeU16Limb_range_eq]
  have hsplit :
      (∑ i ∈ Finset.range 16,
        (if hi : i < 16 then bits ⟨i + 16 * (1 : ℕ), by omega⟩ * 2 ^ i else 0)) =
        (∑ i ∈ Finset.range 8,
          (if hi : i < 16 then bits ⟨16 + i, by omega⟩ * 2 ^ i else 0)) +
          ∑ i ∈ Finset.range 8,
            (if hi : 8 + i < 16 then bits ⟨16 + 8 + i, by omega⟩ * 2 ^ (8 + i) else 0) := by
    simpa [Nat.add_assoc] using
      (Finset.sum_range_add
        (f := fun i => if hi : i < 16 then bits ⟨16 + i, by omega⟩ * 2 ^ i else 0)
        8 8)
  rw [hsplit]
  have hlow :
      (∑ i ∈ Finset.range 8,
        (if hi : i < 16 then bits ⟨16 + i, by omega⟩ * 2 ^ i else 0)) =
        bitsWordByte bits ⟨5, by decide⟩ := by
    calc
      (∑ i ∈ Finset.range 8,
        (if hi : i < 16 then bits ⟨16 + i, by omega⟩ * 2 ^ i else 0)) =
          ∑ i : Fin 8,
            (if hi : i.1 < 16 then bits ⟨16 + i.1, by omega⟩ * 2 ^ i.1 else 0) := by
            exact sum_range8_eq_fin_sum
              (g := fun i => if hi : i < 16 then bits ⟨16 + i, by omega⟩ * 2 ^ i else 0)
      _ = ∑ i : Fin 8, bits ⟨16 + i.1, by omega⟩ * 2 ^ i.1 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hlt : i.1 < 16 := by omega
            simp [hlt]
      _ = bitsWordByte bits ⟨5, by decide⟩ := by
            norm_num [bitsWordByte]
  have hhigh :
      (∑ i ∈ Finset.range 8,
        (if hi : 8 + i < 16 then bits ⟨16 + 8 + i, by omega⟩ * 2 ^ (8 + i) else 0)) =
        bitsWordByte bits ⟨4, by decide⟩ * 256 := by
    calc
      (∑ i ∈ Finset.range 8,
        (if hi : 8 + i < 16 then bits ⟨16 + 8 + i, by omega⟩ * 2 ^ (8 + i) else 0)) =
          ∑ i : Fin 8,
            (if hi : 8 + i.1 < 16 then bits ⟨24 + i.1, by omega⟩ * 2 ^ (8 + i.1) else 0) := by
            exact sum_range8_eq_fin_sum
              (g := fun i => if hi : 8 + i < 16 then bits ⟨24 + i, by omega⟩ * 2 ^ (8 + i) else 0)
      _ = ∑ i : Fin 8, bits ⟨24 + i.1, by omega⟩ * 2 ^ (8 + i.1) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hlt : 8 + i.1 < 16 := by omega
            simp [hlt]
      _ = ∑ i : Fin 8, (bits ⟨24 + i.1, by omega⟩ * 2 ^ i.1) * 256 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              norm_num [pow_add, mul_assoc, mul_left_comm, mul_comm]
      _ = (∑ i : Fin 8, bits ⟨24 + i.1, by omega⟩ * 2 ^ i.1) * 256 := by
            rw [Finset.sum_mul]
      _ = bitsWordByte bits ⟨4, by decide⟩ * 256 := by
            norm_num [bitsWordByte]
  rw [hlow, hhigh]

private theorem composeU16Limb2_eq_bitsWordBytes (bits : BitsWord) :
    composeU16Limb bits ⟨2, by decide⟩ =
      bitsWordByte bits ⟨3, by decide⟩ + bitsWordByte bits ⟨2, by decide⟩ * 256 := by
  rw [composeU16Limb_range_eq]
  have hsplit :
      (∑ i ∈ Finset.range 16,
        (if hi : i < 16 then bits ⟨i + 16 * (2 : ℕ), by omega⟩ * 2 ^ i else 0)) =
        (∑ i ∈ Finset.range 8,
          (if hi : i < 16 then bits ⟨32 + i, by omega⟩ * 2 ^ i else 0)) +
          ∑ i ∈ Finset.range 8,
            (if hi : 8 + i < 16 then bits ⟨32 + 8 + i, by omega⟩ * 2 ^ (8 + i) else 0) := by
    simpa [Nat.add_assoc] using
      (Finset.sum_range_add
        (f := fun i => if hi : i < 16 then bits ⟨32 + i, by omega⟩ * 2 ^ i else 0)
        8 8)
  rw [hsplit]
  have hlow :
      (∑ i ∈ Finset.range 8,
        (if hi : i < 16 then bits ⟨32 + i, by omega⟩ * 2 ^ i else 0)) =
        bitsWordByte bits ⟨3, by decide⟩ := by
    calc
      (∑ i ∈ Finset.range 8,
        (if hi : i < 16 then bits ⟨32 + i, by omega⟩ * 2 ^ i else 0)) =
          ∑ i : Fin 8,
            (if hi : i.1 < 16 then bits ⟨32 + i.1, by omega⟩ * 2 ^ i.1 else 0) := by
            exact sum_range8_eq_fin_sum
              (g := fun i => if hi : i < 16 then bits ⟨32 + i, by omega⟩ * 2 ^ i else 0)
      _ = ∑ i : Fin 8, bits ⟨32 + i.1, by omega⟩ * 2 ^ i.1 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hlt : i.1 < 16 := by omega
            simp [hlt]
      _ = bitsWordByte bits ⟨3, by decide⟩ := by
            norm_num [bitsWordByte]
  have hhigh :
      (∑ i ∈ Finset.range 8,
        (if hi : 8 + i < 16 then bits ⟨32 + 8 + i, by omega⟩ * 2 ^ (8 + i) else 0)) =
        bitsWordByte bits ⟨2, by decide⟩ * 256 := by
    calc
      (∑ i ∈ Finset.range 8,
        (if hi : 8 + i < 16 then bits ⟨32 + 8 + i, by omega⟩ * 2 ^ (8 + i) else 0)) =
          ∑ i : Fin 8,
            (if hi : 8 + i.1 < 16 then bits ⟨40 + i.1, by omega⟩ * 2 ^ (8 + i.1) else 0) := by
            exact sum_range8_eq_fin_sum
              (g := fun i => if hi : 8 + i < 16 then bits ⟨40 + i, by omega⟩ * 2 ^ (8 + i) else 0)
      _ = ∑ i : Fin 8, bits ⟨40 + i.1, by omega⟩ * 2 ^ (8 + i.1) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hlt : 8 + i.1 < 16 := by omega
            simp [hlt]
      _ = ∑ i : Fin 8, (bits ⟨40 + i.1, by omega⟩ * 2 ^ i.1) * 256 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              norm_num [pow_add, mul_assoc, mul_left_comm, mul_comm]
      _ = (∑ i : Fin 8, bits ⟨40 + i.1, by omega⟩ * 2 ^ i.1) * 256 := by
            rw [Finset.sum_mul]
      _ = bitsWordByte bits ⟨2, by decide⟩ * 256 := by
            norm_num [bitsWordByte]
  rw [hlow, hhigh]

private theorem composeU16Limb3_eq_bitsWordBytes (bits : BitsWord) :
    composeU16Limb bits ⟨3, by decide⟩ =
      bitsWordByte bits ⟨1, by decide⟩ + bitsWordByte bits ⟨0, by decide⟩ * 256 := by
  rw [composeU16Limb_range_eq]
  have hsplit :
      (∑ i ∈ Finset.range 16,
        (if hi : i < 16 then bits ⟨i + 16 * (3 : ℕ), by omega⟩ * 2 ^ i else 0)) =
        (∑ i ∈ Finset.range 8,
          (if hi : i < 16 then bits ⟨48 + i, by omega⟩ * 2 ^ i else 0)) +
          ∑ i ∈ Finset.range 8,
            (if hi : 8 + i < 16 then bits ⟨48 + 8 + i, by omega⟩ * 2 ^ (8 + i) else 0) := by
    simpa [Nat.add_assoc] using
      (Finset.sum_range_add
        (f := fun i => if hi : i < 16 then bits ⟨48 + i, by omega⟩ * 2 ^ i else 0)
        8 8)
  rw [hsplit]
  have hlow :
      (∑ i ∈ Finset.range 8,
        (if hi : i < 16 then bits ⟨48 + i, by omega⟩ * 2 ^ i else 0)) =
        bitsWordByte bits ⟨1, by decide⟩ := by
    calc
      (∑ i ∈ Finset.range 8,
        (if hi : i < 16 then bits ⟨48 + i, by omega⟩ * 2 ^ i else 0)) =
          ∑ i : Fin 8,
            (if hi : i.1 < 16 then bits ⟨48 + i.1, by omega⟩ * 2 ^ i.1 else 0) := by
            exact sum_range8_eq_fin_sum
              (g := fun i => if hi : i < 16 then bits ⟨48 + i, by omega⟩ * 2 ^ i else 0)
      _ = ∑ i : Fin 8, bits ⟨48 + i.1, by omega⟩ * 2 ^ i.1 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hlt : i.1 < 16 := by omega
            simp [hlt]
      _ = bitsWordByte bits ⟨1, by decide⟩ := by
            norm_num [bitsWordByte]
  have hhigh :
      (∑ i ∈ Finset.range 8,
        (if hi : 8 + i < 16 then bits ⟨48 + 8 + i, by omega⟩ * 2 ^ (8 + i) else 0)) =
        bitsWordByte bits ⟨0, by decide⟩ * 256 := by
    calc
      (∑ i ∈ Finset.range 8,
        (if hi : 8 + i < 16 then bits ⟨48 + 8 + i, by omega⟩ * 2 ^ (8 + i) else 0)) =
          ∑ i : Fin 8,
            (if hi : 8 + i.1 < 16 then bits ⟨56 + i.1, by omega⟩ * 2 ^ (8 + i.1) else 0) := by
            exact sum_range8_eq_fin_sum
              (g := fun i => if hi : 8 + i < 16 then bits ⟨56 + i, by omega⟩ * 2 ^ (8 + i) else 0)
      _ = ∑ i : Fin 8, bits ⟨56 + i.1, by omega⟩ * 2 ^ (8 + i.1) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hlt : 8 + i.1 < 16 := by omega
            simp [hlt]
      _ = ∑ i : Fin 8, (bits ⟨56 + i.1, by omega⟩ * 2 ^ i.1) * 256 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              norm_num [pow_add, mul_assoc, mul_left_comm, mul_comm]
      _ = (∑ i : Fin 8, bits ⟨56 + i.1, by omega⟩ * 2 ^ i.1) * 256 := by
            rw [Finset.sum_mul]
      _ = bitsWordByte bits ⟨0, by decide⟩ * 256 := by
            norm_num [bitsWordByte]
  rw [hlow, hhigh]

private theorem composeU16Limb0_val_eq_bitsWordBytes
    (bits : BitsWord) (hb : isBitsWord bits) :
    (composeU16Limb bits ⟨0, by decide⟩).val =
      (bitsWordByte bits ⟨7, by decide⟩).val +
        (bitsWordByte bits ⟨6, by decide⟩).val * 256 := by
  have hlo := bitsWordByte_val_lt bits hb ⟨7, by decide⟩
  have hhi := bitsWordByte_val_lt bits hb ⟨6, by decide⟩
  have hval := congrArg Fin.val (composeU16Limb0_eq_bitsWordBytes bits)
  rw [byte_pair_val_eq _ _ hlo hhi] at hval
  exact hval

private theorem composeU16Limb1_val_eq_bitsWordBytes
    (bits : BitsWord) (hb : isBitsWord bits) :
    (composeU16Limb bits ⟨1, by decide⟩).val =
      (bitsWordByte bits ⟨5, by decide⟩).val +
        (bitsWordByte bits ⟨4, by decide⟩).val * 256 := by
  have hlo := bitsWordByte_val_lt bits hb ⟨5, by decide⟩
  have hhi := bitsWordByte_val_lt bits hb ⟨4, by decide⟩
  have hval := congrArg Fin.val (composeU16Limb1_eq_bitsWordBytes bits)
  rw [byte_pair_val_eq _ _ hlo hhi] at hval
  exact hval

private theorem composeU16Limb2_val_eq_bitsWordBytes
    (bits : BitsWord) (hb : isBitsWord bits) :
    (composeU16Limb bits ⟨2, by decide⟩).val =
      (bitsWordByte bits ⟨3, by decide⟩).val +
        (bitsWordByte bits ⟨2, by decide⟩).val * 256 := by
  have hlo := bitsWordByte_val_lt bits hb ⟨3, by decide⟩
  have hhi := bitsWordByte_val_lt bits hb ⟨2, by decide⟩
  have hval := congrArg Fin.val (composeU16Limb2_eq_bitsWordBytes bits)
  rw [byte_pair_val_eq _ _ hlo hhi] at hval
  exact hval

private theorem composeU16Limb3_val_eq_bitsWordBytes
    (bits : BitsWord) (hb : isBitsWord bits) :
    (composeU16Limb bits ⟨3, by decide⟩).val =
      (bitsWordByte bits ⟨1, by decide⟩).val +
        (bitsWordByte bits ⟨0, by decide⟩).val * 256 := by
  have hlo := bitsWordByte_val_lt bits hb ⟨1, by decide⟩
  have hhi := bitsWordByte_val_lt bits hb ⟨0, by decide⟩
  have hval := congrArg Fin.val (composeU16Limb3_eq_bitsWordBytes bits)
  rw [byte_pair_val_eq _ _ hlo hhi] at hval
  exact hval

private theorem beFieldBytesToWord_eq_bitsWordToUInt64
    (bits : BitsWord) (hb : isBitsWord bits) :
    beFieldBytesToWord (fun byte => bitsWordByte bits byte) = bitsWordToUInt64 bits := by
  rw [beFieldBytesToWord, bitsWordToUInt64_eq_compose16 bits hb,
    composeU16Limb0_val_eq_bitsWordBytes bits hb,
    composeU16Limb1_val_eq_bitsWordBytes bits hb,
    composeU16Limb2_val_eq_bitsWordBytes bits hb,
    composeU16Limb3_val_eq_bitsWordBytes bits hb]
  let b0 := (bitsWordByte bits ⟨0, by decide⟩).val
  let b1 := (bitsWordByte bits ⟨1, by decide⟩).val
  let b2 := (bitsWordByte bits ⟨2, by decide⟩).val
  let b3 := (bitsWordByte bits ⟨3, by decide⟩).val
  let b4 := (bitsWordByte bits ⟨4, by decide⟩).val
  let b5 := (bitsWordByte bits ⟨5, by decide⟩).val
  let b6 := (bitsWordByte bits ⟨6, by decide⟩).val
  let b7 := (bitsWordByte bits ⟨7, by decide⟩).val
  have hgrouped :
      b7 + b6 * 256 + (b5 + b4 * 256) * 2 ^ 16 + (b3 + b2 * 256) * 2 ^ 32 +
        (b1 + b0 * 256) * 2 ^ 48 =
      b0 * 2 ^ 56 + b1 * 2 ^ 48 + b2 * 2 ^ 40 + b3 * 2 ^ 32 +
        b4 * 2 ^ 24 + b5 * 2 ^ 16 + b6 * 256 + b7 := by
    calc
      b7 + b6 * 256 + (b5 + b4 * 256) * 2 ^ 16 + (b3 + b2 * 256) * 2 ^ 32 +
          (b1 + b0 * 256) * 2 ^ 48 =
          b7 + b6 * 256 + b5 * 2 ^ 16 + b4 * 2 ^ 24 + b3 * 2 ^ 32 +
            b2 * 2 ^ 40 + b1 * 2 ^ 48 + b0 * 2 ^ 56 := by
              norm_num
              omega
      _ = b0 * 2 ^ 56 + b1 * 2 ^ 48 + b2 * 2 ^ 40 + b3 * 2 ^ 32 +
            b4 * 2 ^ 24 + b5 * 2 ^ 16 + b6 * 256 + b7 := by
              ac_rfl
  change (beFieldBytesNat (fun byte => bitsWordByte bits byte)).toUInt64 =
    (b7 + b6 * 256 + (b5 + b4 * 256) * 2 ^ 16 + (b3 + b2 * 256) * 2 ^ 32 +
      (b1 + b0 * 256) * 2 ^ 48).toUInt64
  have hword := congrArg Nat.toUInt64 hgrouped
  rw [hword]
  change (beFieldBytesNat (fun byte => bitsWordByte bits byte)).toUInt64 =
    (b0 * 2 ^ 56 + b1 * 2 ^ 48 + b2 * 2 ^ 40 + b3 * 2 ^ 32 +
      b4 * 2 ^ 24 + b5 * 2 ^ 16 + b6 * 256 + b7).toUInt64
  simpa [b0, b1, b2, b3, b4, b5, b6, b7, beFieldBytesNat]

private theorem bitsWordByte_eq_schedule_byte
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4) (byte : Fin 8) :
    bitsWordByte (scheduleBitsWord blockAir row slot.1) byte =
      Sha2BlockHasherVmAir_sha512.constraints.compose_schedule_byte blockAir slot.1 byte.1 row := by
  have hsum :
      (∑ bit : Fin 8,
        Sha2BlockHasherVmAir_sha512.constraints.msg_schedule_w blockAir slot.1
          ((7 - byte.1) * 8 + bit.1) row * 2 ^ bit.1) =
      ∑ bit ∈ Finset.range 8,
        Sha2BlockHasherVmAir_sha512.constraints.msg_schedule_w blockAir slot.1
          ((7 - byte.1) * 8 + bit) row * 2 ^ bit := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun bit =>
          Sha2BlockHasherVmAir_sha512.constraints.msg_schedule_w blockAir slot.1
            ((7 - byte.1) * 8 + bit) row * 2 ^ bit)
        (n := 8))
  simpa [bitsWordByte, scheduleBitsWord,
    Sha2BlockHasherVmAir_sha512.constraints.compose_schedule_byte] using hsum.symm

private theorem bitsWordByte_eq_next_schedule_byte
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4) (byte : Fin 8) :
    bitsWordByte (nextScheduleBitsWord blockAir row slot.1) byte =
      Sha2BlockHasherVmAir_sha512.constraints.compose_next_schedule_byte
        blockAir slot.1 byte.1 row := by
  have hsum :
      (∑ bit : Fin 8,
        Sha2BlockHasherVmAir_sha512.constraints.next_msg_schedule_w blockAir slot.1
          ((7 - byte.1) * 8 + bit.1) row * 2 ^ bit.1) =
      ∑ bit ∈ Finset.range 8,
        Sha2BlockHasherVmAir_sha512.constraints.next_msg_schedule_w blockAir slot.1
          ((7 - byte.1) * 8 + bit) row * 2 ^ bit := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun bit =>
          Sha2BlockHasherVmAir_sha512.constraints.next_msg_schedule_w blockAir slot.1
            ((7 - byte.1) * 8 + bit) row * 2 ^ bit)
        (n := 8))
  simpa [bitsWordByte, nextScheduleBitsWord,
    Sha2BlockHasherVmAir_sha512.constraints.compose_next_schedule_byte] using hsum.symm

private theorem beFieldBytesToWord_eq_scheduleWordAtRow_of_bits
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4)
    (hb : isBitsWord (scheduleBitsWord blockAir row slot.1)) :
    beFieldBytesToWord
      (fun byte =>
        Sha2BlockHasherVmAir_sha512.constraints.compose_schedule_byte blockAir slot.1 byte.1 row) =
      scheduleWordAtRow blockAir row slot.1 := by
  have hbytes :
      (fun byte : Fin 8 =>
        Sha2BlockHasherVmAir_sha512.constraints.compose_schedule_byte blockAir slot.1 byte.1 row) =
      (fun byte : Fin 8 => bitsWordByte (scheduleBitsWord blockAir row slot.1) byte) := by
    funext byte
    symm
    exact bitsWordByte_eq_schedule_byte blockAir row slot byte
  calc
    beFieldBytesToWord
        (fun byte =>
          Sha2BlockHasherVmAir_sha512.constraints.compose_schedule_byte blockAir slot.1 byte.1 row) =
        bitsWordToUInt64 (scheduleBitsWord blockAir row slot.1) := by
          rw [hbytes]
          exact beFieldBytesToWord_eq_bitsWordToUInt64 _ hb
    _ = scheduleWordAtRow blockAir row slot.1 := by
      symm
      exact scheduleWordAtRow_eq_bitsWordToUInt64 blockAir row slot.1

private theorem beFieldBytesToWord_eq_nextScheduleWordAtRow_of_bits
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4)
    (hrot : rotation_consistent blockAir)
    (hvalid : row ≤ Circuit.last_row blockAir)
    (hb : isBitsWord (nextScheduleBitsWord blockAir row slot.1)) :
    beFieldBytesToWord
      (fun byte =>
        Sha2BlockHasherVmAir_sha512.constraints.compose_next_schedule_byte
          blockAir slot.1 byte.1 row) =
      scheduleWordAtRow blockAir (nextRow blockAir row) slot.1 := by
  have hbytes :
      (fun byte : Fin 8 =>
        Sha2BlockHasherVmAir_sha512.constraints.compose_next_schedule_byte
          blockAir slot.1 byte.1 row) =
      (fun byte : Fin 8 => bitsWordByte (nextScheduleBitsWord blockAir row slot.1) byte) := by
    funext byte
    symm
    exact bitsWordByte_eq_next_schedule_byte blockAir row slot byte
  calc
    beFieldBytesToWord
        (fun byte =>
          Sha2BlockHasherVmAir_sha512.constraints.compose_next_schedule_byte
            blockAir slot.1 byte.1 row) =
        bitsWordToUInt64 (nextScheduleBitsWord blockAir row slot.1) := by
          rw [hbytes]
          exact beFieldBytesToWord_eq_bitsWordToUInt64 _ hb
    _ = bitsWordToUInt64 (scheduleBitsWord blockAir (nextRow blockAir row) slot.1) := by
      exact congrArg bitsWordToUInt64
        (nextScheduleBitsWord_eq_scheduleBitsWord_nextRow blockAir row slot.1 hrot hvalid)
    _ = scheduleWordAtRow blockAir (nextRow blockAir row) slot.1 := by
      symm
      exact scheduleWordAtRow_eq_bitsWordToUInt64 blockAir (nextRow blockAir row) slot.1

private theorem wrapperMsg1Entry_local_byte
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4) (byte : Fin 8) :
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir row).local_msg_bytes.get
      ⟨8 * slot.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha512.constraints.compose_schedule_byte
          blockAir slot.1 byte.1 row := by
  fin_cases slot <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry]

private theorem wrapperMsg1Entry_next_byte
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4) (byte : Fin 8) :
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir row).next_msg_bytes.get
      ⟨8 * slot.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha512.constraints.compose_next_schedule_byte
          blockAir slot.1 byte.1 row := by
  fin_cases slot <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry]

private theorem wrapperMsg2Entry_local_byte
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4) (byte : Fin 8) :
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir row).local_msg_bytes.get
      ⟨8 * slot.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha512.constraints.compose_schedule_byte
          blockAir slot.1 byte.1 row := by
  fin_cases slot <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry]

private theorem wrapperMsg2Entry_next_byte
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4) (byte : Fin 8) :
    (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir row).next_msg_bytes.get
      ⟨8 * slot.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha512.constraints.compose_next_schedule_byte
          blockAir slot.1 byte.1 row := by
  fin_cases slot <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry]

private theorem rowMessageWord_eq_msg1LocalWord_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨word.1, by omega⟩ =
      beFieldBytesToWord
        (fun byte =>
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).local_msg_bytes.get
            ⟨8 * word.1 + byte.1, by omega⟩) := by
  rcases hcols with ⟨_, _, hmsg1Local, _, _, _⟩
  have hbytes :
      (fun byte : Fin 8 =>
        Sha2MainAir_sha512.constraints.message_byte mainAir (8 * word.1 + byte.1) row) =
      (fun byte : Fin 8 =>
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).local_msg_bytes.get
          ⟨8 * word.1 + byte.1, by omega⟩) := by
    funext byte
    simpa using hmsg1Local ⟨8 * word.1 + byte.1, by omega⟩
  simp [rowMessageWord, hbytes]

private theorem rowMessageWord_eq_msg1NextWord_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨4 + word.1, by omega⟩ =
      beFieldBytesToWord
        (fun byte =>
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).next_msg_bytes.get
            ⟨8 * word.1 + byte.1, by omega⟩) := by
  rcases hcols with ⟨_, _, _, hmsg1Next, _, _⟩
  have hbytes :
      (fun byte : Fin 8 =>
        Sha2MainAir_sha512.constraints.message_byte mainAir (8 * (4 + word.1) + byte.1) row) =
      (fun byte : Fin 8 =>
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).next_msg_bytes.get
          ⟨8 * word.1 + byte.1, by omega⟩) := by
    funext byte
    have hidx : 8 * (4 + word.1) + byte.1 = 32 + (8 * word.1 + byte.1) := by omega
    simpa [hidx] using hmsg1Next ⟨8 * word.1 + byte.1, by omega⟩
  simp [rowMessageWord, hbytes]

private theorem rowMessageWord_eq_msg2LocalWord_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨8 + word.1, by omega⟩ =
      beFieldBytesToWord
        (fun byte =>
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).local_msg_bytes.get
            ⟨8 * word.1 + byte.1, by omega⟩) := by
  rcases hcols with ⟨_, _, _, _, hmsg2Local, _⟩
  have hbytes :
      (fun byte : Fin 8 =>
        Sha2MainAir_sha512.constraints.message_byte mainAir (8 * (8 + word.1) + byte.1) row) =
      (fun byte : Fin 8 =>
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).local_msg_bytes.get
          ⟨8 * word.1 + byte.1, by omega⟩) := by
    funext byte
    have hidx : 8 * (8 + word.1) + byte.1 = 64 + (8 * word.1 + byte.1) := by omega
    simpa [hidx] using hmsg2Local ⟨8 * word.1 + byte.1, by omega⟩
  simp [rowMessageWord, hbytes]

private theorem rowMessageWord_eq_msg2NextWord_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨12 + word.1, by omega⟩ =
      beFieldBytesToWord
        (fun byte =>
          (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).next_msg_bytes.get
            ⟨8 * word.1 + byte.1, by omega⟩) := by
  rcases hcols with ⟨_, _, _, _, _, hmsg2Next⟩
  have hbytes :
      (fun byte : Fin 8 =>
        Sha2MainAir_sha512.constraints.message_byte mainAir (8 * (12 + word.1) + byte.1) row) =
      (fun byte : Fin 8 =>
        (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).next_msg_bytes.get
          ⟨8 * word.1 + byte.1, by omega⟩) := by
    funext byte
    have hidx : 8 * (12 + word.1) + byte.1 = 96 + (8 * word.1 + byte.1) := by omega
    simpa [hidx] using hmsg2Next ⟨8 * word.1 + byte.1, by omega⟩
  simp [rowMessageWord, hbytes]

private def rowBlockInputWordQuarterSpec
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ) : Prop :=
  (∀ word : Fin 4,
    rowMessageWord mainAir row ⟨word.1, by omega⟩ =
      inputWord blockAir start word.1) ∧
  (∀ word : Fin 4,
    rowMessageWord mainAir row ⟨4 + word.1, by omega⟩ =
      inputWord blockAir start (4 + word.1)) ∧
  (∀ word : Fin 4,
    rowMessageWord mainAir row ⟨8 + word.1, by omega⟩ =
      inputWord blockAir start (8 + word.1)) ∧
  ∀ word : Fin 4,
    rowMessageWord mainAir row ⟨12 + word.1, by omega⟩ =
      inputWord blockAir start (12 + word.1)

private theorem rowMessageWord_eq_inputWord_msg1Local_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (hsched_bits : scheduleBitsBooleanOnBlock blockAir start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨word.1, by omega⟩ =
      inputWord blockAir start word.1 := by
  calc
    rowMessageWord mainAir row ⟨word.1, by omega⟩ =
        beFieldBytesToWord
          (fun byte =>
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).local_msg_bytes.get
              ⟨8 * word.1 + byte.1, by omega⟩) :=
      rowMessageWord_eq_msg1LocalWord_of_columns mainAir blockAir row start hcols word
    _ =
        beFieldBytesToWord
          (fun byte =>
            Sha2BlockHasherVmAir_sha512.constraints.compose_schedule_byte
              blockAir word.1 byte.1 start) := by
      congr 1
      funext byte
      exact wrapperMsg1Entry_local_byte blockAir start word byte
    _ = scheduleWordAtRow blockAir start word.1 := by
      exact beFieldBytesToWord_eq_scheduleWordAtRow_of_bits
        blockAir start word (hsched_bits 0 word.1 (by omega) word.is_lt)
    _ = inputWord blockAir start word.1 := by
      have hdiv : word.1 / 4 = 0 := by omega
      have hmod : word.1 % 4 = word.1 := by omega
      simp [inputWord, hdiv, hmod]

private theorem rowMessageWord_eq_inputWord_msg1Next_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (hwindow : blockWindowSupported blockAir start)
    (hrot : rotation_consistent blockAir)
    (hsched_bits : scheduleBitsBooleanOnBlock blockAir start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨4 + word.1, by omega⟩ =
      inputWord blockAir start (4 + word.1) := by
  have hvalid : start ≤ Circuit.last_row blockAir := by
    have hsupp : start + 20 ≤ Circuit.last_row blockAir := by
      simpa [blockWindowSupported] using hwindow
    omega
  have hnext : nextRow blockAir start = start + 1 := by
    have hsupp : start + 20 ≤ Circuit.last_row blockAir := by
      simpa [blockWindowSupported] using hwindow
    have hlt : start < Circuit.last_row blockAir := by
      omega
    simp [nextRow, hlt.ne]
  have hnext_bits : isBitsWord (nextScheduleBitsWord blockAir start word.1) := by
    intro i
    have hEq := congrFun
      (nextScheduleBitsWord_eq_scheduleBitsWord_nextRow blockAir start word.1 hrot hvalid) i
    rw [hnext] at hEq
    rw [hEq]
    exact hsched_bits 1 word.1 (by omega) word.is_lt i
  calc
    rowMessageWord mainAir row ⟨4 + word.1, by omega⟩ =
        beFieldBytesToWord
          (fun byte =>
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg1Entry blockAir start).next_msg_bytes.get
              ⟨8 * word.1 + byte.1, by omega⟩) :=
      rowMessageWord_eq_msg1NextWord_of_columns mainAir blockAir row start hcols word
    _ =
        beFieldBytesToWord
          (fun byte =>
            Sha2BlockHasherVmAir_sha512.constraints.compose_next_schedule_byte
              blockAir word.1 byte.1 start) := by
      congr 1
      funext byte
      exact wrapperMsg1Entry_next_byte blockAir start word byte
    _ = scheduleWordAtRow blockAir (nextRow blockAir start) word.1 := by
      exact beFieldBytesToWord_eq_nextScheduleWordAtRow_of_bits
        blockAir start word hrot hvalid hnext_bits
    _ = scheduleWordAtRow blockAir (start + 1) word.1 := by rw [hnext]
    _ = inputWord blockAir start (4 + word.1) := by
      have hdiv : (4 + word.1) / 4 = 1 := by omega
      have hmod : (4 + word.1) % 4 = word.1 := by omega
      simp [inputWord, hdiv, hmod]

private theorem rowMessageWord_eq_inputWord_msg2Local_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (hsched_bits : scheduleBitsBooleanOnBlock blockAir start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨8 + word.1, by omega⟩ =
      inputWord blockAir start (8 + word.1) := by
  calc
    rowMessageWord mainAir row ⟨8 + word.1, by omega⟩ =
        beFieldBytesToWord
          (fun byte =>
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).local_msg_bytes.get
              ⟨8 * word.1 + byte.1, by omega⟩) :=
      rowMessageWord_eq_msg2LocalWord_of_columns mainAir blockAir row start hcols word
    _ =
        beFieldBytesToWord
          (fun byte =>
            Sha2BlockHasherVmAir_sha512.constraints.compose_schedule_byte
              blockAir word.1 byte.1 (start + 2)) := by
      congr 1
      funext byte
      exact wrapperMsg2Entry_local_byte blockAir (start + 2) word byte
    _ = scheduleWordAtRow blockAir (start + 2) word.1 := by
      exact beFieldBytesToWord_eq_scheduleWordAtRow_of_bits
        blockAir (start + 2) word (hsched_bits 2 word.1 (by omega) word.is_lt)
    _ = inputWord blockAir start (8 + word.1) := by
      have hdiv : (8 + word.1) / 4 = 2 := by omega
      have hmod : (8 + word.1) % 4 = word.1 := by omega
      simp [inputWord, hdiv, hmod]

private theorem rowMessageWord_eq_inputWord_msg2Next_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (hwindow : blockWindowSupported blockAir start)
    (hrot : rotation_consistent blockAir)
    (hsched_bits : scheduleBitsBooleanOnBlock blockAir start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨12 + word.1, by omega⟩ =
      inputWord blockAir start (12 + word.1) := by
  have hvalid : start + 2 ≤ Circuit.last_row blockAir := by
    have hsupp : start + 20 ≤ Circuit.last_row blockAir := by
      simpa [blockWindowSupported] using hwindow
    omega
  have hnext : nextRow blockAir (start + 2) = start + 3 := by
    have hsupp : start + 20 ≤ Circuit.last_row blockAir := by
      simpa [blockWindowSupported] using hwindow
    have hlt : start + 2 < Circuit.last_row blockAir := by
      omega
    simp [nextRow, hlt.ne]
  have hnext_bits : isBitsWord (nextScheduleBitsWord blockAir (start + 2) word.1) := by
    intro i
    have hEq := congrFun
      (nextScheduleBitsWord_eq_scheduleBitsWord_nextRow
        blockAir (start + 2) word.1 hrot hvalid) i
    rw [hnext] at hEq
    rw [hEq]
    exact hsched_bits 3 word.1 (by omega) word.is_lt i
  calc
    rowMessageWord mainAir row ⟨12 + word.1, by omega⟩ =
        beFieldBytesToWord
          (fun byte =>
            (Sha2BlockHasherVmAir_sha512.constraints.wrapperMsg2Entry blockAir (start + 2)).next_msg_bytes.get
              ⟨8 * word.1 + byte.1, by omega⟩) :=
      rowMessageWord_eq_msg2NextWord_of_columns mainAir blockAir row start hcols word
    _ =
        beFieldBytesToWord
          (fun byte =>
            Sha2BlockHasherVmAir_sha512.constraints.compose_next_schedule_byte
              blockAir word.1 byte.1 (start + 2)) := by
      congr 1
      funext byte
      exact wrapperMsg2Entry_next_byte blockAir (start + 2) word byte
    _ = scheduleWordAtRow blockAir (nextRow blockAir (start + 2)) word.1 := by
      exact beFieldBytesToWord_eq_nextScheduleWordAtRow_of_bits
        blockAir (start + 2) word hrot hvalid hnext_bits
    _ = scheduleWordAtRow blockAir (start + 3) word.1 := by rw [hnext]
    _ = inputWord blockAir start (12 + word.1) := by
      have hdiv : (12 + word.1) / 4 = 3 := by omega
      have hmod : (12 + word.1) % 4 = word.1 := by omega
      simp [inputWord, hdiv, hmod]

private theorem rowBlockInputWordQuarterSpec_of_columns
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (hwindow : blockWindowSupported blockAir start)
    (hrot : rotation_consistent blockAir)
    (hsched_bits : scheduleBitsBooleanOnBlock blockAir start) :
    rowBlockInputWordQuarterSpec mainAir blockAir row start := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro word
    exact rowMessageWord_eq_inputWord_msg1Local_of_columns
      mainAir blockAir row start hcols hsched_bits word
  · intro word
    exact rowMessageWord_eq_inputWord_msg1Next_of_columns
      mainAir blockAir row start hcols hwindow hrot hsched_bits word
  · intro word
    exact rowMessageWord_eq_inputWord_msg2Local_of_columns
      mainAir blockAir row start hcols hsched_bits word
  · intro word
    exact rowMessageWord_eq_inputWord_msg2Next_of_columns
      mainAir blockAir row start hcols hwindow hrot hsched_bits word

/-- The main-row output words equal the pure compression result computed from
the row's reconstructed input state and message words. -/
def compressWordEquivSpec
    (mainAir : CMain FBB ExtF) (row : ℕ) : Prop :=
  rowNewState mainAir row =
    sha512CompressWords (rowPrevState mainAir row) (rowMessageWords mainAir row)

/-- Byte image of the row's written SHA-512 state. -/
def rowOutputBytes (mainAir : CMain FBB ExtF) (row : ℕ) : StateBytes :=
  workingVarsToStateBytes (rowNewState mainAir row)

private theorem rowMessageWord_eq_inputWord_of_quarters
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hquarters : rowBlockInputWordQuarterSpec mainAir blockAir row start)
    (word : Fin 16) :
    rowMessageWord mainAir row word = inputWord blockAir start word.1 := by
  rcases hquarters with ⟨hmsg1Local, hmsg1Next, hmsg2Local, hmsg2Next⟩
  by_cases hlt4 : word.1 < 4
  · simpa using hmsg1Local ⟨word.1, hlt4⟩
  · by_cases hlt8 : word.1 < 8
    · have hidx : 4 + (word.1 - 4) = word.1 := by omega
      have hfin : (⟨4 + (word.1 - 4), by omega⟩ : Fin 16) = word := by
        ext
        omega
      simpa [hidx, hfin] using hmsg1Next ⟨word.1 - 4, by omega⟩
    · by_cases hlt12 : word.1 < 12
      · have hidx : 8 + (word.1 - 8) = word.1 := by omega
        have hfin : (⟨8 + (word.1 - 8), by omega⟩ : Fin 16) = word := by
          ext
          omega
        simpa [hidx, hfin] using hmsg2Local ⟨word.1 - 8, by omega⟩
      · have hidx : 12 + (word.1 - 12) = word.1 := by omega
        have hfin : (⟨12 + (word.1 - 12), by omega⟩ : Fin 16) = word := by
          ext
          omega
        simpa [hidx, hfin] using hmsg2Next ⟨word.1 - 12, by omega⟩

private theorem rowMessageWords_eq_blockInputWords_of_quarters
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hquarters : rowBlockInputWordQuarterSpec mainAir blockAir row start) :
    rowMessageWords mainAir row = blockInputWords blockAir start := by
  unfold rowMessageWords blockInputWords
  refine congrArg Array.ofFn ?_
  funext word
  exact rowMessageWord_eq_inputWord_of_quarters mainAir blockAir row start hquarters word

theorem compressWordEquivSpec_of_shared_payload_and_block_soundness
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hmain : wrapperPayloadSpec mainAir row)
    (hshared : sharedWrapperPayloadSpec mainAir blockAir row start)
    (hstart : start ≤ Circuit.last_row blockAir)
    (hsel : encoder_selector_idx blockAir start = 0)
    (hrot : rotation_consistent blockAir)
    (hc : blockHasherConstraints blockAir)
    (h_raw_perm : privateBusRawPermutationSemantics blockAir)
    (htrace_fit : traceLengthFitsField blockAir)
    (h_bus_wf : ∀ mult a b c op,
      (mult, [a, b, c, op]) ∈ Circuit.buses blockAir Sha2BitwiseBus →
      mult = 1 → a.val < 256 ∧ b.val < 256) :
    compressWordEquivSpec mainAir row := by
  have hblockBoundary :=
    blockCompressionBoundarySpec_of_soundness_assumptions
      blockAir start hstart hsel hrot hc h_raw_perm htrace_fit h_bus_wf
  rcases hblockBoundary with ⟨hwindow, hrot', hsched_bits, hblock⟩
  have hpackage :=
    rowBlockCompressionPackage_of_shared_payload
      mainAir blockAir row start hmain hshared hblock
  have hstartState :=
    rowBlockStartState_of_block_package mainAir blockAir row start hpackage
  have houtputState :=
    rowBlockOutputState_of_block_package mainAir blockAir row start hpackage
  rcases hstartState with ⟨_, hstartEq⟩
  rcases houtputState with ⟨hcols, houtputEq⟩
  have hinput :=
    rowBlockInputWordQuarterSpec_of_columns
      mainAir blockAir row start hcols hwindow hrot' hsched_bits
  have hmsgEq :=
    rowMessageWords_eq_blockInputWords_of_quarters mainAir blockAir row start hinput
  simpa [compressWordEquivSpec, sha512CompressWords, hstartEq.symm, hmsgEq.symm] using houtputEq

end SharedBridge

end Sha2CompressionBridge_sha512
