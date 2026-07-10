import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.TraceSpec
import VmExtensions.Soundness.Sha2MainAir_sha256.ColumnBridge

set_option autoImplicit false
set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 20_000

namespace VmExtensions.Sha2CompressOpcode

open Sha2BlockHasherVmAir_sha256.BlockSpec

/-- The SHA-256 state is stored as 32 bytes, grouped into eight little-endian words. -/
abbrev StateBytes := Vector (BitVec 8) 32

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
    let word := i.val / 4
    let byte := i.val % 4
    wordByteLE (workingVarAt state word) byte)

/-- Pure SHA-256 compression on decoded state and input words. -/
def sha256CompressWords (initialState : WorkingVars) (messageWords : Array Word) : WorkingVars :=
  let schedule := expandSchedule messageWords
  let finalState := (compressionTrace initialState schedule)[64]!
  initialState.add finalState

/-- Latched SHA-256 `compress` inputs at the row boundary. -/
structure Sha256CompressLatchedInput where
  outputPtr : BitVec 32
  prevStatePtr : BitVec 32
  inputPtr : BitVec 32
  PC : BitVec 32
  prevState : WorkingVars
  messageWords : Fin 16 → Word

open BabyBear
open Sha2CompressionBridge_sha256
open Sha2MainAir_sha256.Soundness

def beFieldBytesNat (bytes : Fin 4 → FBB) : Nat :=
  (bytes ⟨0, by decide⟩).val * 16777216 +
    (bytes ⟨1, by decide⟩).val * 65536 +
    (bytes ⟨2, by decide⟩).val * 256 +
    (bytes ⟨3, by decide⟩).val

def beFieldBytesToWord (bytes : Fin 4 → FBB) : Word :=
  UInt32.ofNat (beFieldBytesNat bytes)

def rowMessageWord
    {CMain : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain]
    (mainAir : CMain FBB ExtF) (row : ℕ) (word : Fin 16) : Word :=
  beFieldBytesToWord
    (fun byte => Sha2MainAir_sha256.constraints.message_byte mainAir (4 * word.1 + byte.1) row)

def rowMessageWords
    {CMain : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain]
    (mainAir : CMain FBB ExtF) (row : ℕ) : Array Word :=
  Array.ofFn (fun word : Fin 16 => rowMessageWord mainAir row word)

private def bitsWordByte (bits : BitsWord) (byteIdx : Fin 4) : FBB :=
  ∑ bit : Fin 8, bits ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩ * 2 ^ bit.1

private theorem bitsWordByte_eq_nat_sum
    (bits : BitsWord) (hb : isBitsWord bits) (byteIdx : Fin 4) :
    bitsWordByte bits byteIdx =
      ((∑ bit : Fin 8,
          (bits ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) : FBB) := by
  rw [bitsWordByte, Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro bit _
  rcases hb ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩ with hbit | hbit <;> simp [hbit]

private theorem bitsWordByte_nat_sum_lt
    (bits : BitsWord) (hb : isBitsWord bits) (byteIdx : Fin 4) :
    (∑ bit : Fin 8,
        (bits ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) < 2 ^ 8 := by
  have hle :
      (∑ bit : Fin 8,
          (bits ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) ≤
        ∑ bit : Fin 8, 2 ^ bit.1 := by
    refine Finset.sum_le_sum ?_
    intro bit _
    rcases hb ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩ with hbit | hbit <;> simp [hbit]
  have hpow : (∑ bit : Fin 8, 2 ^ bit.1 : ℕ) < 2 ^ 8 := by
    norm_num [Fin.sum_univ_eq_sum_range]
  exact lt_of_le_of_lt hle hpow

private theorem bitsWordByte_val_eq_nat_sum
    (bits : BitsWord) (hb : isBitsWord bits) (byteIdx : Fin 4) :
    (bitsWordByte bits byteIdx).val =
      ∑ bit : Fin 8,
        (bits ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 := by
  have hs_lt :
      (∑ bit : Fin 8,
          (bits ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) < 2 ^ 8 :=
    bitsWordByte_nat_sum_lt bits hb byteIdx
  have hs_prime :
      (∑ bit : Fin 8,
          (bits ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) < BB_prime := by
    exact lt_trans hs_lt (by norm_num)
  have hcast := congrArg Fin.val (bitsWordByte_eq_nat_sum bits hb byteIdx)
  change
    (bitsWordByte bits byteIdx).val =
      (∑ bit : Fin 8,
        (bits ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) % BB_prime at hcast
  rw [Nat.mod_eq_of_lt hs_prime] at hcast
  exact hcast

private theorem bitsWordByte_val_lt
    (bits : BitsWord) (hb : isBitsWord bits) (byteIdx : Fin 4) :
    (bitsWordByte bits byteIdx).val < 256 := by
  have hs_lt :
      (∑ bit : Fin 8,
          (bits ⟨(3 - byteIdx.1) * 8 + bit.1, by omega⟩).val * 2 ^ bit.1 : ℕ) < 2 ^ 8 :=
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

private theorem composeLo16_eq_bitsWordBytes (bits : BitsWord) :
    composeLo16 bits =
      bitsWordByte bits ⟨3, by decide⟩ + bitsWordByte bits ⟨2, by decide⟩ * 256 := by
  have h0 :
      bitsWordByte bits ⟨3, by decide⟩ =
        ∑ x : Fin 8, bits ⟨x.1, by omega⟩ * 2 ^ x.1 := by
    simp [bitsWordByte]
  have h8 :
      bitsWordByte bits ⟨2, by decide⟩ =
        ∑ x : Fin 8, bits ⟨8 + x.1, by omega⟩ * 2 ^ x.1 := by
    simp [bitsWordByte]
  rw [composeLo16_explicit, h0, h8, Fin.sum_univ_eight, Fin.sum_univ_eight]
  norm_num
  ring_nf

private theorem composeHi16_eq_bitsWordBytes (bits : BitsWord) :
    composeHi16 bits =
      bitsWordByte bits ⟨1, by decide⟩ + bitsWordByte bits ⟨0, by decide⟩ * 256 := by
  have h16 :
      bitsWordByte bits ⟨1, by decide⟩ =
        ∑ x : Fin 8, bits ⟨16 + x.1, by omega⟩ * 2 ^ x.1 := by
    simp [bitsWordByte]
  have h24 :
      bitsWordByte bits ⟨0, by decide⟩ =
        ∑ x : Fin 8, bits ⟨24 + x.1, by omega⟩ * 2 ^ x.1 := by
    simp [bitsWordByte]
  rw [composeHi16_explicit, h16, h24, Fin.sum_univ_eight, Fin.sum_univ_eight]
  norm_num
  ring_nf

private theorem composeLo16_val_eq_bitsWordBytes
    (bits : BitsWord) (hb : isBitsWord bits) :
    (composeLo16 bits).val =
      (bitsWordByte bits ⟨3, by decide⟩).val +
        (bitsWordByte bits ⟨2, by decide⟩).val * 256 := by
  have hlo := bitsWordByte_val_lt bits hb ⟨3, by decide⟩
  have hhi := bitsWordByte_val_lt bits hb ⟨2, by decide⟩
  have hval := congrArg Fin.val (composeLo16_eq_bitsWordBytes bits)
  rw [byte_pair_val_eq _ _ hlo hhi] at hval
  exact hval

private theorem composeHi16_val_eq_bitsWordBytes
    (bits : BitsWord) (hb : isBitsWord bits) :
    (composeHi16 bits).val =
      (bitsWordByte bits ⟨1, by decide⟩).val +
        (bitsWordByte bits ⟨0, by decide⟩).val * 256 := by
  have hlo := bitsWordByte_val_lt bits hb ⟨1, by decide⟩
  have hhi := bitsWordByte_val_lt bits hb ⟨0, by decide⟩
  have hval := congrArg Fin.val (composeHi16_eq_bitsWordBytes bits)
  rw [byte_pair_val_eq _ _ hlo hhi] at hval
  exact hval

private theorem beFieldBytesToWord_eq_bitsWordToUInt32
    (bits : BitsWord) (hb : isBitsWord bits) :
    beFieldBytesToWord (fun byte => bitsWordByte bits byte) = bitsWordToUInt32 bits := by
  rw [beFieldBytesToWord, bitsWordToUInt32_eq_compose16 bits hb,
    composeLo16_val_eq_bitsWordBytes bits hb, composeHi16_val_eq_bitsWordBytes bits hb]
  have hnat :
      (bitsWordByte bits ⟨0, by decide⟩).val * 16777216 +
        (bitsWordByte bits ⟨1, by decide⟩).val * 65536 +
        (bitsWordByte bits ⟨2, by decide⟩).val * 256 +
        (bitsWordByte bits ⟨3, by decide⟩).val =
      (bitsWordByte bits ⟨3, by decide⟩).val +
        (bitsWordByte bits ⟨2, by decide⟩).val * 256 +
        ((bitsWordByte bits ⟨1, by decide⟩).val +
          (bitsWordByte bits ⟨0, by decide⟩).val * 256) * 2 ^ 16 := by
    ring
  simpa [beFieldBytesNat] using congrArg UInt32.ofNat hnat

private theorem bitsWordByte_eq_schedule_byte
    {CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CBlock]
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4) (byte : Fin 4) :
    bitsWordByte (scheduleBitsWord blockAir row slot.1) byte =
      Sha2BlockHasherVmAir_sha256.constraints.compose_schedule_byte blockAir slot.1 byte.1 row := by
  have hsum :
      (∑ bit : Fin 8,
        Sha2BlockHasherVmAir_sha256.constraints.msg_schedule_w blockAir slot.1
          ((3 - byte.1) * 8 + bit.1) row * 2 ^ bit.1) =
      ∑ bit ∈ Finset.range 8,
        Sha2BlockHasherVmAir_sha256.constraints.msg_schedule_w blockAir slot.1
          ((3 - byte.1) * 8 + bit) row * 2 ^ bit := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun bit =>
          Sha2BlockHasherVmAir_sha256.constraints.msg_schedule_w blockAir slot.1
            ((3 - byte.1) * 8 + bit) row * 2 ^ bit)
        (n := 8))
  simpa [bitsWordByte, scheduleBitsWord,
    Sha2BlockHasherVmAir_sha256.constraints.compose_schedule_byte] using hsum.symm

private theorem bitsWordByte_eq_next_schedule_byte
    {CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CBlock]
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4) (byte : Fin 4) :
    bitsWordByte (nextScheduleBitsWord blockAir row slot.1) byte =
      Sha2BlockHasherVmAir_sha256.constraints.compose_next_schedule_byte
        blockAir slot.1 byte.1 row := by
  have hsum :
      (∑ bit : Fin 8,
        Sha2BlockHasherVmAir_sha256.constraints.next_msg_schedule_w blockAir slot.1
          ((3 - byte.1) * 8 + bit.1) row * 2 ^ bit.1) =
      ∑ bit ∈ Finset.range 8,
        Sha2BlockHasherVmAir_sha256.constraints.next_msg_schedule_w blockAir slot.1
          ((3 - byte.1) * 8 + bit) row * 2 ^ bit := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := fun bit =>
          Sha2BlockHasherVmAir_sha256.constraints.next_msg_schedule_w blockAir slot.1
            ((3 - byte.1) * 8 + bit) row * 2 ^ bit)
        (n := 8))
  simpa [bitsWordByte, nextScheduleBitsWord,
    Sha2BlockHasherVmAir_sha256.constraints.compose_next_schedule_byte] using hsum.symm

private theorem beFieldBytesToWord_eq_scheduleWordAtRow_of_bits
    {CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CBlock]
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4)
    (hb : isBitsWord (scheduleBitsWord blockAir row slot.1)) :
    beFieldBytesToWord
      (fun byte =>
        Sha2BlockHasherVmAir_sha256.constraints.compose_schedule_byte blockAir slot.1 byte.1 row) =
      scheduleWordAtRow blockAir row slot.1 := by
  have hbytes :
      (fun byte : Fin 4 =>
        Sha2BlockHasherVmAir_sha256.constraints.compose_schedule_byte blockAir slot.1 byte.1 row) =
      (fun byte : Fin 4 => bitsWordByte (scheduleBitsWord blockAir row slot.1) byte) := by
    funext byte
    symm
    exact bitsWordByte_eq_schedule_byte blockAir row slot byte
  calc
    beFieldBytesToWord
        (fun byte =>
          Sha2BlockHasherVmAir_sha256.constraints.compose_schedule_byte blockAir slot.1 byte.1 row) =
        bitsWordToUInt32 (scheduleBitsWord blockAir row slot.1) := by
          rw [hbytes]
          exact beFieldBytesToWord_eq_bitsWordToUInt32 _ hb
    _ = scheduleWordAtRow blockAir row slot.1 := by
      symm
      exact scheduleWordAtRow_eq_bitsWordToUInt32 blockAir row slot.1

private theorem beFieldBytesToWord_eq_nextScheduleWordAtRow_of_bits
    {CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CBlock]
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot : Fin 4)
    (hrot : rotation_consistent blockAir)
    (hvalid : row ≤ Circuit.last_row blockAir)
    (hb : isBitsWord (nextScheduleBitsWord blockAir row slot.1)) :
    beFieldBytesToWord
      (fun byte =>
        Sha2BlockHasherVmAir_sha256.constraints.compose_next_schedule_byte
          blockAir slot.1 byte.1 row) =
      scheduleWordAtRow blockAir (nextRow blockAir row) slot.1 := by
  have hbytes :
      (fun byte : Fin 4 =>
        Sha2BlockHasherVmAir_sha256.constraints.compose_next_schedule_byte
          blockAir slot.1 byte.1 row) =
      (fun byte : Fin 4 => bitsWordByte (nextScheduleBitsWord blockAir row slot.1) byte) := by
    funext byte
    symm
    exact bitsWordByte_eq_next_schedule_byte blockAir row slot byte
  calc
    beFieldBytesToWord
        (fun byte =>
          Sha2BlockHasherVmAir_sha256.constraints.compose_next_schedule_byte
            blockAir slot.1 byte.1 row) =
        bitsWordToUInt32 (nextScheduleBitsWord blockAir row slot.1) := by
          rw [hbytes]
          exact beFieldBytesToWord_eq_bitsWordToUInt32 _ hb
    _ = bitsWordToUInt32 (scheduleBitsWord blockAir (nextRow blockAir row) slot.1) := by
      exact congrArg bitsWordToUInt32
        (nextScheduleBitsWord_eq_scheduleBitsWord_nextRow blockAir row slot.1 hrot hvalid)
    _ = scheduleWordAtRow blockAir (nextRow blockAir row) slot.1 := by
      symm
      exact scheduleWordAtRow_eq_bitsWordToUInt32 blockAir (nextRow blockAir row) slot.1

private theorem wrapperMsg1Entry_local_byte
    {CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CBlock]
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot byte : Fin 4) :
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir row).local_msg_bytes.get
      ⟨4 * slot.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha256.constraints.compose_schedule_byte
          blockAir slot.1 byte.1 row := by
  fin_cases slot <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry]

private theorem wrapperMsg1Entry_next_byte
    {CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CBlock]
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot byte : Fin 4) :
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir row).next_msg_bytes.get
      ⟨4 * slot.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha256.constraints.compose_next_schedule_byte
          blockAir slot.1 byte.1 row := by
  fin_cases slot <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry]

private theorem wrapperMsg2Entry_local_byte
    {CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CBlock]
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot byte : Fin 4) :
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir row).local_msg_bytes.get
      ⟨4 * slot.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha256.constraints.compose_schedule_byte
          blockAir slot.1 byte.1 row := by
  fin_cases slot <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry]

private theorem wrapperMsg2Entry_next_byte
    {CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CBlock]
    (blockAir : CBlock FBB ExtF) (row : ℕ) (slot byte : Fin 4) :
    (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir row).next_msg_bytes.get
      ⟨4 * slot.1 + byte.1, by omega⟩ =
        Sha2BlockHasherVmAir_sha256.constraints.compose_next_schedule_byte
          blockAir slot.1 byte.1 row := by
  fin_cases slot <;> fin_cases byte <;>
    simp [Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry]

private theorem rowMessageWord_eq_msg1LocalWord_of_columns
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨word.1, by omega⟩ =
      beFieldBytesToWord
        (fun byte =>
          (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start).local_msg_bytes.get
            ⟨4 * word.1 + byte.1, by omega⟩) := by
  rcases hcols with ⟨_, _, hmsg1Local, _, _, _⟩
  have hbytes :
      (fun byte : Fin 4 =>
        Sha2MainAir_sha256.constraints.message_byte mainAir (4 * word.1 + byte.1) row) =
      (fun byte : Fin 4 =>
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start).local_msg_bytes.get
          ⟨4 * word.1 + byte.1, by omega⟩) := by
    funext byte
    simpa using hmsg1Local ⟨4 * word.1 + byte.1, by omega⟩
  simp [rowMessageWord, hbytes]

private theorem rowMessageWord_eq_msg1NextWord_of_columns
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨4 + word.1, by omega⟩ =
      beFieldBytesToWord
        (fun byte =>
          (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start).next_msg_bytes.get
            ⟨4 * word.1 + byte.1, by omega⟩) := by
  rcases hcols with ⟨_, _, _, hmsg1Next, _, _⟩
  have hbytes :
      (fun byte : Fin 4 =>
        Sha2MainAir_sha256.constraints.message_byte mainAir (4 * (4 + word.1) + byte.1) row) =
      (fun byte : Fin 4 =>
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start).next_msg_bytes.get
          ⟨4 * word.1 + byte.1, by omega⟩) := by
    funext byte
    have hidx : 4 * (4 + word.1) + byte.1 = 16 + (4 * word.1 + byte.1) := by omega
    simpa [hidx] using hmsg1Next ⟨4 * word.1 + byte.1, by omega⟩
  simp [rowMessageWord, hbytes]

private theorem rowMessageWord_eq_msg2LocalWord_of_columns
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨8 + word.1, by omega⟩ =
      beFieldBytesToWord
        (fun byte =>
          (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)).local_msg_bytes.get
            ⟨4 * word.1 + byte.1, by omega⟩) := by
  rcases hcols with ⟨_, _, _, _, hmsg2Local, _⟩
  have hbytes :
      (fun byte : Fin 4 =>
        Sha2MainAir_sha256.constraints.message_byte mainAir (4 * (8 + word.1) + byte.1) row) =
      (fun byte : Fin 4 =>
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)).local_msg_bytes.get
          ⟨4 * word.1 + byte.1, by omega⟩) := by
    funext byte
    have hidx : 4 * (8 + word.1) + byte.1 = 32 + (4 * word.1 + byte.1) := by omega
    simpa [hidx] using hmsg2Local ⟨4 * word.1 + byte.1, by omega⟩
  simp [rowMessageWord, hbytes]

private theorem rowMessageWord_eq_msg2NextWord_of_columns
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨12 + word.1, by omega⟩ =
      beFieldBytesToWord
        (fun byte =>
          (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)).next_msg_bytes.get
            ⟨4 * word.1 + byte.1, by omega⟩) := by
  rcases hcols with ⟨_, _, _, _, _, hmsg2Next⟩
  have hbytes :
      (fun byte : Fin 4 =>
        Sha2MainAir_sha256.constraints.message_byte mainAir (4 * (12 + word.1) + byte.1) row) =
      (fun byte : Fin 4 =>
        (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)).next_msg_bytes.get
          ⟨4 * word.1 + byte.1, by omega⟩) := by
    funext byte
    have hidx : 4 * (12 + word.1) + byte.1 = 48 + (4 * word.1 + byte.1) := by omega
    simpa [hidx] using hmsg2Next ⟨4 * word.1 + byte.1, by omega⟩
  simp [rowMessageWord, hbytes]

private def rowBlockInputWordQuarterSpec
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
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
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
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
            (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start).local_msg_bytes.get
              ⟨4 * word.1 + byte.1, by omega⟩) :=
      rowMessageWord_eq_msg1LocalWord_of_columns mainAir blockAir row start hcols word
    _ =
        beFieldBytesToWord
          (fun byte =>
            Sha2BlockHasherVmAir_sha256.constraints.compose_schedule_byte
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
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (hwindow : blockWindowSupported blockAir start)
    (hrot : rotation_consistent blockAir)
    (hsched_bits : scheduleBitsBooleanOnBlock blockAir start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨4 + word.1, by omega⟩ =
      inputWord blockAir start (4 + word.1) := by
  have hvalid : start ≤ Circuit.last_row blockAir := by
    have hsupp : start + 16 ≤ Circuit.last_row blockAir := by
      simpa [blockWindowSupported] using hwindow
    omega
  have hnext : nextRow blockAir start = start + 1 := by
    have hsupp : start + 16 ≤ Circuit.last_row blockAir := by
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
            (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg1Entry blockAir start).next_msg_bytes.get
              ⟨4 * word.1 + byte.1, by omega⟩) :=
      rowMessageWord_eq_msg1NextWord_of_columns mainAir blockAir row start hcols word
    _ =
        beFieldBytesToWord
          (fun byte =>
            Sha2BlockHasherVmAir_sha256.constraints.compose_next_schedule_byte
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
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
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
            (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)).local_msg_bytes.get
              ⟨4 * word.1 + byte.1, by omega⟩) :=
      rowMessageWord_eq_msg2LocalWord_of_columns mainAir blockAir row start hcols word
    _ =
        beFieldBytesToWord
          (fun byte =>
            Sha2BlockHasherVmAir_sha256.constraints.compose_schedule_byte
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
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hcols : rowBlockColumnAgreementSpec mainAir blockAir row start)
    (hwindow : blockWindowSupported blockAir start)
    (hrot : rotation_consistent blockAir)
    (hsched_bits : scheduleBitsBooleanOnBlock blockAir start)
    (word : Fin 4) :
    rowMessageWord mainAir row ⟨12 + word.1, by omega⟩ =
      inputWord blockAir start (12 + word.1) := by
  have hvalid : start + 2 ≤ Circuit.last_row blockAir := by
    have hsupp : start + 16 ≤ Circuit.last_row blockAir := by
      simpa [blockWindowSupported] using hwindow
    omega
  have hnext : nextRow blockAir (start + 2) = start + 3 := by
    have hsupp : start + 16 ≤ Circuit.last_row blockAir := by
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
            (Sha2BlockHasherVmAir_sha256.constraints.wrapperMsg2Entry blockAir (start + 2)).next_msg_bytes.get
              ⟨4 * word.1 + byte.1, by omega⟩) :=
      rowMessageWord_eq_msg2NextWord_of_columns mainAir blockAir row start hcols word
    _ =
        beFieldBytesToWord
          (fun byte =>
            Sha2BlockHasherVmAir_sha256.constraints.compose_next_schedule_byte
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
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
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
    {CMain : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain]
    (mainAir : CMain FBB ExtF) (row : ℕ) : Prop :=
  rowNewState mainAir row =
    sha256CompressWords (rowPrevState mainAir row) (rowMessageWords mainAir row)

/-- Byte image of the row's written SHA-256 state. -/
def rowOutputBytes
    {CMain : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain]
    (mainAir : CMain FBB ExtF) (row : ℕ) : StateBytes :=
  workingVarsToStateBytes (rowNewState mainAir row)


private theorem rowMessageWord_eq_inputWord_of_quarters
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
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
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
    (mainAir : CMain FBB ExtF) (blockAir : CBlock FBB ExtF) (row start : ℕ)
    (hquarters : rowBlockInputWordQuarterSpec mainAir blockAir row start) :
    rowMessageWords mainAir row = blockInputWords blockAir start := by
  unfold rowMessageWords blockInputWords
  refine congrArg Array.ofFn ?_
  funext word
  exact rowMessageWord_eq_inputWord_of_quarters mainAir blockAir row start hquarters word

theorem compressWordEquivSpec_of_shared_payload_and_block_soundness
    {CMain CBlock : Type → Type → Type} {ExtF : Type}
    [Field ExtF] [Circuit FBB ExtF CMain] [Circuit FBB ExtF CBlock]
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
      (mult, [a, b, c, op]) ∈ Circuit.buses blockAir BitwiseBus →
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
  simpa [compressWordEquivSpec, sha256CompressWords, hstartEq.symm, hmsgEq.symm] using houtputEq

end VmExtensions.Sha2CompressOpcode
