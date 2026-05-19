import OpenvmFv.Fundamentals.BabyBear
import VmExtensions.Constraints.Sha2BlockHasherVmAir_sha512

set_option autoImplicit false

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

/--
`Sha2BlockHasherSubAir` stores SHA-512 blocks in a 21-row window:

- row `start - 1` carries the incoming working variables for the block,
- rows `start .. start + 19` are the 20 round rows, each containing 4 rounds,
- row `start + 20` is the digest row.

This file packages that layout into a block-scoped contract over the extracted matrix.
-/

abbrev Word := UInt64

structure WorkingVars where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word
deriving Repr, DecidableEq, Inhabited

def WorkingVars.add (x y : WorkingVars) : WorkingVars where
  a := x.a + y.a
  b := x.b + y.b
  c := x.c + y.c
  d := x.d + y.d
  e := x.e + y.e
  f := x.f + y.f
  g := x.g + y.g
  h := x.h + y.h

def rotr (x : Word) (n : Nat) : Word :=
  (x >>> n.toUInt64) ||| (x <<< (64 - n).toUInt64)

def ch (x y z : Word) : Word :=
  (x &&& y) ^^^ ((~~~x) &&& z)

def maj (x y z : Word) : Word :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bigSigma0 (x : Word) : Word :=
  rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39

def bigSigma1 (x : Word) : Word :=
  rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41

def smallSigma0 (x : Word) : Word :=
  rotr x 1 ^^^ rotr x 8 ^^^ (x >>> 7)

def smallSigma1 (x : Word) : Word :=
  rotr x 19 ^^^ rotr x 61 ^^^ (x >>> 6)

def sha512K : Array Word :=
  #[
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
  ]

def roundStep (state : WorkingVars) (k w : Word) : WorkingVars :=
  let t1 := state.h + bigSigma1 state.e + ch state.e state.f state.g + k + w
  let t2 := bigSigma0 state.a + maj state.a state.b state.c
  {
    a := t1 + t2
    b := state.a
    c := state.b
    d := state.c
    e := state.d + t1
    f := state.e
    g := state.f
    h := state.g
  }

abbrev BitsWord := Fin 64 → FBB

def composeBits (bits : BitsWord) : FBB :=
  Finset.univ.sum (fun (i : Fin 64) => bits i * (2 : FBB) ^ i.val)

def composeU16Limb (bits : BitsWord) (limb : Fin 4) : FBB :=
  Finset.univ.sum (fun (i : Fin 16) =>
    bits ⟨i.val + 16 * limb.val, by omega⟩ * (2 : FBB) ^ i.val)

def composeLo16 (bits : BitsWord) : FBB :=
  composeU16Limb bits ⟨0, by decide⟩

def composeHi16 (bits : BitsWord) : FBB :=
  composeU16Limb bits ⟨3, by decide⟩

def isBitsWord (bits : BitsWord) : Prop :=
  ∀ i : Fin 64, bits i = 0 ∨ bits i = 1

def fieldXor (x y : FBB) : FBB :=
  x + y - 2 * x * y

def fieldAnd (x y : FBB) : FBB :=
  x * y

def fieldNot (x : FBB) : FBB :=
  1 - x

def fieldCh (x y z : BitsWord) : BitsWord :=
  fun i => fieldXor (fieldAnd (x i) (y i)) (fieldAnd (fieldNot (x i)) (z i))

def fieldMaj (x y z : BitsWord) : BitsWord :=
  fun i => fieldXor (fieldXor (fieldAnd (x i) (y i)) (fieldAnd (x i) (z i)))
                     (fieldAnd (y i) (z i))

def fieldRotr (x : BitsWord) (n : Nat) : BitsWord :=
  fun i => x ⟨(i.val + n) % 64, Nat.mod_lt _ (by omega)⟩

def fieldShr (x : BitsWord) (n : Nat) : BitsWord :=
  fun i => if h : i.val + n < 64 then x ⟨i.val + n, h⟩ else 0

def fieldBigSigma0 (x : BitsWord) : BitsWord :=
  fun i => fieldXor (fieldXor ((fieldRotr x 28) i) ((fieldRotr x 34) i)) ((fieldRotr x 39) i)

def fieldBigSigma1 (x : BitsWord) : BitsWord :=
  fun i => fieldXor (fieldXor ((fieldRotr x 14) i) ((fieldRotr x 18) i)) ((fieldRotr x 41) i)

def fieldSmallSigma0 (x : BitsWord) : BitsWord :=
  fun i => fieldXor (fieldXor ((fieldRotr x 1) i) ((fieldRotr x 8) i)) ((fieldShr x 7) i)

def fieldSmallSigma1 (x : BitsWord) : BitsWord :=
  fun i => fieldXor (fieldXor ((fieldRotr x 19) i) ((fieldRotr x 61) i)) ((fieldShr x 6) i)

def bitsWordToUInt64 (bits : BitsWord) : Word :=
  (Finset.univ.sum (fun (i : Fin 64) => (bits i).val * (2 ^ i.val))).toUInt64

def bitsLEToWord (bits : Nat → FBB) : Word :=
  ((List.range 64).foldl (fun acc i => acc + (bits i).val * (2 ^ i)) (0 : Nat)).toUInt64

def bytesLEToWord (bytes : Nat → FBB) : Word :=
  ((List.range 8).foldl (fun acc i => acc + (bytes i).val * (256 ^ i)) (0 : Nat)).toUInt64

def limbs16LEToWord (limbs : Nat → FBB) : Word :=
  ((List.range 4).foldl (fun acc i => acc + (limbs i).val * (65536 ^ i)) (0 : Nat)).toUInt64

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-- Sum of six ternary encoder digits supplied abstractly. -/
def encoder_digit_sum_from (enc : ℕ → FBB) : FBB :=
  enc 0 + enc 1 + enc 2 + enc 3 + enc 4 + enc 5

/-- Sum of the 6 ternary encoder digits. -/
def encoder_digit_sum (air : C FBB ExtF) (row : ℕ) : FBB :=
  encoder_digit_sum_from (fun i => encoder_idx air i row)

/-- Quadratic selector for the ternary values `{0, 1, 2}`. -/
def encoder_choose2 (x : FBB) : FBB :=
  x * (x - 1) * 1006632961

/--
Decoded SHA-512 block-row selector used by the row-index transition constraints.

The 22 valid encoder points correspond to selector values `0..21`.
-/
def encoder_selector_from (enc : ℕ → FBB) : FBB :=
  let s := encoder_digit_sum_from enc
  enc 5 * (2 - s) +
  2 * encoder_choose2 (enc 5) +
  3 * enc 4 * (2 - s) +
  4 * enc 4 * enc 5 +
  5 * encoder_choose2 (enc 4) +
  6 * enc 3 * (2 - s) +
  7 * enc 3 * enc 5 +
  8 * enc 3 * enc 4 +
  9 * encoder_choose2 (enc 3) +
  10 * enc 2 * (2 - s) +
  11 * enc 2 * enc 5 +
  12 * enc 2 * enc 4 +
  13 * enc 2 * enc 3 +
  14 * encoder_choose2 (enc 2) +
  15 * enc 1 * (2 - s) +
  16 * enc 1 * enc 5 +
  17 * enc 1 * enc 4 +
  18 * enc 1 * enc 3 +
  19 * enc 1 * enc 2 +
  20 * encoder_choose2 (enc 1) +
  21 * enc 0 * (2 - s)

def encoder_selector_idx (air : C FBB ExtF) (row : ℕ) : FBB :=
  encoder_selector_from (fun i => encoder_idx air i row)

def next_encoder_selector_idx (air : C FBB ExtF) (row : ℕ) : FBB :=
  encoder_selector_from (fun i => encoder_idx_next air i row)

def prevRow (air : C FBB ExtF) (start : ℕ) : ℕ :=
  if start = 0 then Circuit.last_row air else start - 1

def nextRow (air : C FBB ExtF) (row : ℕ) : ℕ :=
  if row = Circuit.last_row air then 0 else row + 1

/-- The row that carries the state after `offset * 4` rounds of the block
    starting at `start`.

    `offset = 0` is the predecessor row, while `offset = 1..20` are the
    twenty round rows `start .. start + 19`. -/
def blockStateRow (air : C FBB ExtF) (start offset : ℕ) : ℕ :=
  if start = 0 then
    if offset = 0 then Circuit.last_row air else offset - 1
  else
    start + offset - 1

/--
Rotation-1 accesses in the SHA-512 wrapper matrix agree with rotation-0 accesses
at the successor row, with the last row wrapping around to the first row.
-/
def rotation_consistent (air : C FBB ExtF) : Prop :=
  (∀ column row, row < Circuit.last_row air →
    Circuit.main air (id := 0) (column := column) (row := row) (rotation := 1) =
      Circuit.main air (id := 0) (column := column) (row := row + 1) (rotation := 0)) ∧
  (∀ column,
    Circuit.main air (id := 0) (column := column) (row := Circuit.last_row air) (rotation := 1) =
      Circuit.main air (id := 0) (column := column) (row := 0) (rotation := 0))

def aWord (air : C FBB ExtF) (row slot : ℕ) : Word :=
  bitsLEToWord (fun bit => work_vars_a air slot bit row)

def eWord (air : C FBB ExtF) (row slot : ℕ) : Word :=
  bitsLEToWord (fun bit => work_vars_e air slot bit row)

def scheduleWordAtRow (air : C FBB ExtF) (row slot : ℕ) : Word :=
  bitsWordToUInt64 (fun i => msg_schedule_w air slot i.val row)

def digestFinalHashWord (air : C FBB ExtF) (row word : ℕ) : Word :=
  bytesLEToWord (fun byte => final_hash air word byte row)

def digestPrevHashWord (air : C FBB ExtF) (row word : ℕ) : Word :=
  limbs16LEToWord (fun limb => prev_hash air word limb row)

def aBitsWord (air : C FBB ExtF) (row slot : ℕ) : BitsWord :=
  fun i => work_vars_a air slot i.val row

def eBitsWord (air : C FBB ExtF) (row slot : ℕ) : BitsWord :=
  fun i => work_vars_e air slot i.val row

def scheduleBitsWord (air : C FBB ExtF) (row slot : ℕ) : BitsWord :=
  fun i => msg_schedule_w air slot i.val row

/--
The eight working variables carried from `row` into `row + 1`.

This is the ordering used by the AIR transition constraints:
`a[3], a[2], a[1], a[0], e[3], e[2], e[1], e[0]`.
-/
def carriedState (air : C FBB ExtF) (row : ℕ) : WorkingVars where
  a := aWord air row 3
  b := aWord air row 2
  c := aWord air row 1
  d := aWord air row 0
  e := eWord air row 3
  f := eWord air row 2
  g := eWord air row 1
  h := eWord air row 0

def digestPrevHashState (air : C FBB ExtF) (row : ℕ) : WorkingVars where
  a := digestPrevHashWord air row 0
  b := digestPrevHashWord air row 1
  c := digestPrevHashWord air row 2
  d := digestPrevHashWord air row 3
  e := digestPrevHashWord air row 4
  f := digestPrevHashWord air row 5
  g := digestPrevHashWord air row 6
  h := digestPrevHashWord air row 7

def digestFinalHashState (air : C FBB ExtF) (row : ℕ) : WorkingVars where
  a := digestFinalHashWord air row 0
  b := digestFinalHashWord air row 1
  c := digestFinalHashWord air row 2
  d := digestFinalHashWord air row 3
  e := digestFinalHashWord air row 4
  f := digestFinalHashWord air row 5
  g := digestFinalHashWord air row 6
  h := digestFinalHashWord air row 7

/-- The digest row's chaining `hash` field, distinct from `final_hash`.

    This field carries the next block's `prev_hash` payload, not the current
    block's `final_hash`. -/
def digestChainingHashState (air : C FBB ExtF) (row : ℕ) : WorkingVars :=
  carriedState air row

def inputWord (air : C FBB ExtF) (start idx : ℕ) : Word :=
  scheduleWordAtRow air (start + idx / 4) (idx % 4)

def blockInputWords (air : C FBB ExtF) (start : ℕ) : Array Word :=
  Array.ofFn (n := 16) (fun i => inputWord air start i.val)

def expandSchedule (input : Array Word) : Array Word :=
  Id.run do
    let mut w := input
    for offset in List.range 64 do
      let t := offset + 16
      let nextWord :=
        smallSigma1 (w[t - 2]!) +
        w[t - 7]! +
        smallSigma0 (w[t - 15]!) +
        w[t - 16]!
      w := w.push nextWord
    pure w

def compressionTrace (startState : WorkingVars) (schedule : Array Word) : Array WorkingVars :=
  Id.run do
    let mut trace := #[startState]
    let mut state := startState
    for t in List.range 80 do
      state := roundStep state (sha512K[t]!) (schedule[t]!)
      trace := trace.push state
    pure trace

def blockStartState (air : C FBB ExtF) (start : ℕ) : WorkingVars :=
  carriedState air (blockStateRow air start 0)

/-- The 21-row block window rooted at `start` lies entirely inside the concrete
    trace, so all rows `start .. start + 20` are actual trace rows. -/
def blockWindowSupported (air : C FBB ExtF) (start : ℕ) : Prop :=
  start + 20 ≤ Circuit.last_row air

def wordU16Limb (w : Word) (limb : ℕ) : FBB :=
  (((w.toNat / 2 ^ (16 * limb)) % 2 ^ 16 : ℕ) : FBB)

def workingVarsU16Limb (state : WorkingVars) (word limb : ℕ) : FBB :=
  let w := match word with
    | 0 => state.a | 1 => state.b | 2 => state.c | 3 => state.d
    | 4 => state.e | 5 => state.f | 6 => state.g | 7 => state.h
    | _ => 0
  wordU16Limb w limb

def blockWindowHasShape (air : C FBB ExtF) (start : ℕ) : Prop :=
  let prev := prevRow air start
  (encoder_selector_idx air prev = 20 ∨ encoder_selector_idx air prev = 21) ∧
  (∀ offset, offset < 20 →
    encoder_selector_idx air (start + offset) = (offset : FBB) ∧
    is_round_row air (start + offset) = 1 ∧
    is_digest_row air (start + offset) = 0) ∧
  encoder_selector_idx air (start + 20) = 20 ∧
  is_round_row air (start + 20) = 0 ∧
  is_digest_row air (start + 20) = 1

def blockCompressionSpec (air : C FBB ExtF) (start : ℕ) : Prop :=
  let initialState := blockStartState air start
  let messageWords := blockInputWords air start
  let schedule := expandSchedule messageWords
  let finalState := (compressionTrace initialState schedule)[80]!
  blockWindowHasShape air start ∧
  digestPrevHashState air (start + 20) = initialState ∧
  digestFinalHashState air (start + 20) = initialState.add finalState

def flagsWellFormed (air : C FBB ExtF) (row : ℕ) : Prop :=
  (is_round_row air row = 0 ∨ is_round_row air row = 1) ∧
  (is_first_4_rows air row = 0 ∨ is_first_4_rows air row = 1) ∧
  (is_digest_row air row = 0 ∨ is_digest_row air row = 1) ∧
  (is_round_row air row + is_digest_row air row = 0 ∨
   is_round_row air row + is_digest_row air row = 1) ∧
  (∀ i, i < 6 → encoder_idx air i row = 0 ∨
                  encoder_idx air i row = 1 ∨
                  encoder_idx air i row = 2)

def allWorkVarBitsBoolean (air : C FBB ExtF) (row : ℕ) : Prop :=
  (∀ slot bit, slot < 4 → bit < 64 →
    work_vars_a air slot bit row = 0 ∨ work_vars_a air slot bit row = 1) ∧
  (∀ slot bit, slot < 4 → bit < 64 →
    work_vars_e air slot bit row = 0 ∨ work_vars_e air slot bit row = 1)

def paddingPreservesWorkVars (air : C FBB ExtF) (row : ℕ) : Prop :=
  (row ≤ Circuit.last_row air) →
    ((1 - (is_round_row air (nextRow air row) + is_digest_row air (nextRow air row))) = 1) →
      ∀ slot bit, slot < 4 → bit < 64 →
        work_vars_a air slot bit row = work_vars_a air slot bit (nextRow air row) ∧
        work_vars_e air slot bit row = work_vars_e air slot bit (nextRow air row)

/-- Proof-side interface exposing the bitwise-bus carry range facts used by the
    round-step arithmetic bridge. The implemented AIR only range-checks these
    carries to bytes; it does not constrain them to be boolean. -/
def roundCarryRangeAssumption (air : C FBB ExtF) : Prop :=
  ∀ row slot limb, slot < 4 → limb < 4 →
    next_is_round_row air row = 1 →
    (next_carry_a air slot limb row).val < 256 ∧
    (next_carry_e air slot limb row).val < 256

/-- Byte-range bounds for the carry cells stored on a single round row.

    This is the arithmetic interface actually consumed by the round-step bridge:
    it talks directly about the carry columns on the round row being proved,
    without mentioning how those bounds are obtained. -/
def roundCarryBoundsAt (air : C FBB ExtF) (row : ℕ) : Prop :=
  ∀ slot limb, slot < 4 → limb < 4 →
    (carry_a air slot limb row).val < 256 ∧
    (carry_e air slot limb row).val < 256

/-- Block-local carry-range assumption for the 20 round rows in the block
    window starting at `start`.

    This is strictly weaker than `roundCarryRangeAssumption`: the compression
    proof only needs byte bounds for the carry columns on the concrete round
    rows it traverses. -/
def roundCarryRangeOnBlock (air : C FBB ExtF) (start : ℕ) : Prop :=
  ∀ offset, offset < 20 → roundCarryBoundsAt air (start + offset)

/-- Trace length fits within the BabyBear field, preventing wrap-around of
    field-valued counters like `global_block_idx`. -/
def traceLengthFitsField (air : C FBB ExtF) : Prop :=
  Circuit.last_row air + 1 < BB_prime

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
