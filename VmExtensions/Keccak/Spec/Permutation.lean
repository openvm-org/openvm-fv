/-
  Byte-level Keccak-f[1600] permutation.

  Wraps the lane-level `keccakP` from `Basic.lean` with byte↔lane conversions,
  exposing `keccakF : SpongeState → SpongeState` as the main interface.
-/
import VmExtensions.Keccak.Spec.Basic
import VmExtensions.Keccak.Spec.Absorb

set_option autoImplicit false

namespace Keccak

/-! # Byte ↔ Lane Conversions -/

/-- Pack 8 little-endian bytes starting at position `8*lane` into a UInt64. -/
def spongeToLane (s : SpongeState) (lane : Fin 25) : UInt64 :=
  let base := 8 * lane.val
  (s[base + 7]'(by omega)).toUInt64 <<< 56 |||
  (s[base + 6]'(by omega)).toUInt64 <<< 48 |||
  (s[base + 5]'(by omega)).toUInt64 <<< 40 |||
  (s[base + 4]'(by omega)).toUInt64 <<< 32 |||
  (s[base + 3]'(by omega)).toUInt64 <<< 24 |||
  (s[base + 2]'(by omega)).toUInt64 <<< 16 |||
  (s[base + 1]'(by omega)).toUInt64 <<< 8 |||
  (s[base + 0]'(by omega)).toUInt64

/-- Convert a 200-byte SpongeState to a 25-lane State. -/
def spongeToState (s : SpongeState) : State :=
  ⟨Array.ofFn fun i : Fin 25 => spongeToLane s i,
   by simp⟩

/-- Extract byte `k` (0 ≤ k < 8) from a UInt64 in little-endian order. -/
def laneGetByte (v : UInt64) (k : Fin 8) : UInt8 :=
  (v >>> (8 * k.val).toUInt64).toUInt8

/-- Convert a 25-lane State back to a 200-byte SpongeState.
    Byte `i` = byte `(i % 8)` of lane `(i / 8)`, little-endian. -/
def stateToSponge (st : State) : SpongeState :=
  ⟨ByteArray.mk <| Array.ofFn fun i : Fin 200 =>
    let lane : Nat := i.val / 8
    let byte_idx : Fin 8 := ⟨i.val % 8, by omega⟩
    laneGetByte (st[lane]'(by
      have hi : i.val < 200 := i.isLt
      omega)) byte_idx,
   by simp [ByteArray.size]⟩

/-! # Main Interface -/

/-- The Keccak-f[1600] permutation at byte level. -/
def keccakF (s : SpongeState) : SpongeState :=
  stateToSponge (keccakP (spongeToState s))

end Keccak
