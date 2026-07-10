/-
  Spec bridge types for KeccakfPermAir.

  Bridges between the bus-level u16-limb representation (`KeccakBusState`)
  and the keccak spec's `SpongeState` (200 bytes).
-/
import VmExtensions.Keccak.Spec.Permutation
import VmExtensions.Soundness.Keccakf.Interface

set_option autoImplicit false

namespace KeccakfPermAir.Spec

open Keccakf.Interface

/-- Decode a single u16 limb into two little-endian bytes. -/
def decodeLimb (limb : UInt16) : UInt8 × UInt8 :=
  (limb.toUInt8, (limb >>> 8).toUInt8)

/-- Decode 100 u16 limbs (= 50 words × 2 limbs each) into a 200-byte SpongeState.
    Limb ordering: limb `2*w` is the low half of word `w`, limb `2*w+1` is the high half.
    Each limb produces two bytes (lo, hi) in little-endian order. -/
def decodeBusState (s : KeccakBusState) : SpongeState :=
  let bytes : Array UInt8 := Array.ofFn fun (i : Fin 200) =>
    let limb_idx := i.val / 2
    let byte_in_limb := i.val % 2
    let limb := s[limb_idx]'(by omega)
    if byte_in_limb = 0 then limb.toUInt8
    else (limb >>> 8).toUInt8
  ⟨ByteArray.mk bytes, by show bytes.size = 200; simp [bytes, Array.size_ofFn]⟩

/-- The native permutation relation: `post` is the keccak-f permutation of `pre`
    in the bus-level u16-limb representation. -/
def BusKeccakPermutes (pre post : KeccakBusState) : Prop :=
  decodeBusState post = Keccak.keccakF (decodeBusState pre)

end KeccakfPermAir.Spec
