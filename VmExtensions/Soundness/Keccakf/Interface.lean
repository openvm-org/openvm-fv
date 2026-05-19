/-
  Shared bus-level semantics for the Keccakf sub-AIR soundness surface.

  Fixes the concrete state representation, message normalization, timestamp
  bound, limb-to-byte decoding, and permutation relation shared by
  `KeccakfOpAir` and `KeccakfPermAir`.
-/
import VmExtensions.Keccak.Spec.Permutation

set_option autoImplicit false

namespace Keccakf.Interface

/-! ## Bus-level state representation -/

/-- The shared bus-level keccak state: 100 little-endian u16 limbs.
    Both AIR branches use this exact type for their message payloads. -/
abbrev KeccakBusState := Vector UInt16 100

/-! ## Timestamp bound -/

/-- The shared timestamp bound for normalized keccak-state messages.
    Matches the OpenVM interaction-layer timestamp range. -/
def timestampBound : Nat := 2 ^ 29

/-! ## Normalized keccak-state message -/

/-- A normalized bus message carrying a keccak state, a pre/post flag, and a timestamp.
    Equality on this record is full fieldwise equality on all three fields. -/
structure KeccakStateMsg where
  /-- `false` for pre-state (input), `true` for post-state (output). -/
  isPost : Bool
  /-- The timestamp associated with this message. -/
  timestamp : Nat
  /-- The keccak state payload as 100 little-endian u16 limbs. -/
  state : KeccakBusState

/-- Construct a normalized pre-state message (`isPost := false`). -/
def mkPreMsg (timestamp : Nat) (state : KeccakBusState) : KeccakStateMsg where
  isPost := false
  timestamp := timestamp
  state := state

/-- Construct a normalized post-state message (`isPost := true`). -/
def mkPostMsg (timestamp : Nat) (state : KeccakBusState) : KeccakStateMsg where
  isPost := true
  timestamp := timestamp
  state := state

/-! ### Fieldwise equality lemmas for normalized constructors -/

theorem mkPreMsg_inj {t₁ t₂ : Nat} {s₁ s₂ : KeccakBusState}
    (h : mkPreMsg t₁ s₁ = mkPreMsg t₂ s₂) : t₁ = t₂ ∧ s₁ = s₂ := by
  simp [mkPreMsg, KeccakStateMsg.mk.injEq] at h
  exact h

theorem mkPostMsg_inj {t₁ t₂ : Nat} {s₁ s₂ : KeccakBusState}
    (h : mkPostMsg t₁ s₁ = mkPostMsg t₂ s₂) : t₁ = t₂ ∧ s₁ = s₂ := by
  simp [mkPostMsg, KeccakStateMsg.mk.injEq] at h
  exact h

theorem mkPreMsg_ne_mkPostMsg (t₁ t₂ : Nat) (s₁ s₂ : KeccakBusState) :
    mkPreMsg t₁ s₁ ≠ mkPostMsg t₂ s₂ := by
  simp [mkPreMsg, mkPostMsg, KeccakStateMsg.mk.injEq]

/-! ## Limb-to-byte decoding -/

/-- Extract the low byte of a `UInt16`. -/
def UInt16.loByte (v : UInt16) : UInt8 := v.toUInt8

/-- Extract the high byte of a `UInt16`. -/
def UInt16.hiByte (v : UInt16) : UInt8 := (v >>> 8).toUInt8

/-- Decode 100 little-endian u16 limbs into a 200-byte `SpongeState`.
    Limb `k` maps to bytes `2k` (low) and `2k+1` (high). -/
def decodeBusState (bs : KeccakBusState) : SpongeState :=
  ⟨ByteArray.mk <| Array.ofFn fun i : Fin 200 =>
    let limb_idx := i.val / 2
    let limb := bs[limb_idx]'(by omega)
    if i.val % 2 = 0 then UInt16.loByte limb else UInt16.hiByte limb,
   by simp [ByteArray.size]⟩

/-! ## Bus-native permutation relation -/

/-- The concrete bus-native permutation relation.
    States that decoding the post-state and applying `keccakF` to the decoded
    pre-state yield the same `SpongeState`. -/
def BusKeccakPermutes (pre post : KeccakBusState) : Prop :=
  decodeBusState post = Keccak.keccakF (decodeBusState pre)

end Keccakf.Interface
