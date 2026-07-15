/-
  Encode/decode roundtrip lemmas for KeccakBusState ↔ SpongeState.

  `encodeBusState` is the inverse of `decodeBusState`: it packs a 200-byte
  SpongeState into 100 u16 limbs. The roundtrip theorems guarantee that
  `decode ∘ encode = id` and `encode ∘ decode = id`.
-/
import VmExtensions.Soundness.KeccakfPermAir.Spec
import VmExtensions.Soundness.Keccakf.Interface
import Std.Tactic.BVDecide

set_option autoImplicit false

namespace KeccakfPermAir.Spec

open Keccakf.Interface

/-! ## Encoding -/

/-- Encode two bytes into one u16 limb (little-endian). -/
def encodeLimb (lo hi : UInt8) : UInt16 :=
  lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/-- Encode a 200-byte SpongeState into 100 u16 limbs. -/
def encodeBusState (s : SpongeState) : KeccakBusState :=
  Vector.ofFn fun (i : Fin 100) =>
    encodeLimb (s[2 * i.val]'(by omega)) (s[2 * i.val + 1]'(by omega))

/-! ## Limb-level roundtrip lemmas -/

/-- Low byte of encodeLimb. -/
theorem encodeLimb_low (lo hi : UInt8) : (encodeLimb lo hi).toUInt8 = lo := by
  cases lo with | ofBitVec blo => ?_
  cases hi with | ofBitVec bhi => ?_
  show UInt8.ofBitVec ((blo.zeroExtend 16 ||| bhi.zeroExtend 16 <<< 8).truncate 8)
    = UInt8.ofBitVec blo
  congr 1
  ext i hi
  simp_all

/-- High byte of encodeLimb. -/
theorem encodeLimb_high (lo hi : UInt8) : ((encodeLimb lo hi) >>> 8).toUInt8 = hi := by
  cases lo with | ofBitVec blo => ?_
  cases hi with | ofBitVec bhi => ?_
  show UInt8.ofBitVec (((blo.zeroExtend 16 ||| bhi.zeroExtend 16 <<< 8) >>> 8).truncate 8)
    = UInt8.ofBitVec bhi
  congr 1
  ext i
  have e2 : decide (8 + i < 16) = true := decide_eq_true_eq.mpr (by omega)
  have e3 : decide (8 + i < 8) = false := decide_eq_false_iff_not.mpr (by omega)
  have e4 : decide (i < 16) = true := decide_eq_true_eq.mpr (by omega)
  simp_all

/-- Any u16 can be reconstructed from its low and high bytes. -/
theorem u16_from_bytes (x : UInt16) :
    encodeLimb x.toUInt8 ((x >>> 8).toUInt8) = x := by
  cases x with | ofBitVec bx => ?_
  show UInt16.ofBitVec ((bx.truncate 8).zeroExtend 16 |||
    ((bx >>> 8).truncate 8).zeroExtend 16 <<< 8) = UInt16.ofBitVec bx
  congr 1
  ext i hi
  by_cases h8 : i < 8
  · simp_all
  · simp
    rw [show 8 + (i - 8) = i from by omega]
    have e1 : decide (i < 8) = false := decide_eq_false_iff_not.mpr (by omega)
    have e2 : decide (i - 8 < 8) = true := decide_eq_true_eq.mpr (by omega)
    simp_all
    cases decide (i < 8) <;> simp

/-! ## State-level roundtrip theorems -/

/-- Decoding after encoding is the identity on SpongeState. -/
theorem decode_encode (s : SpongeState) : decodeBusState (encodeBusState s) = s := by
  apply Subtype.ext
  unfold decodeBusState encodeBusState
  apply congrArg ByteArray.mk
  apply Array.ext
  · simp [Array.size_ofFn, s.property]
  · intro i h₁ h₂
    simp only [Array.size_ofFn] at h₁
    simp only [Array.getElem_ofFn]
    simp only [Vector.getElem_ofFn]
    split
    · -- even byte: byte_in_limb = 0, so we get the low byte
      rename_i h_even
      have h_mod : i % 2 = 0 := by omega
      rw [encodeLimb_low]
      congr 1; omega
    · -- odd byte: byte_in_limb ≠ 0, so we get the high byte
      rename_i h_odd
      have h_mod : i % 2 ≠ 0 := by omega
      rw [encodeLimb_high]
      congr 1; omega

/-- Encoding after decoding is the identity on KeccakBusState.

Strategy: for each limb index `i`, the two decoded bytes at positions `2i` and
`2i+1` are `v[i].toUInt8` and `(v[i] >>> 8).toUInt8` respectively, so
`encodeLimb` reconstructs `v[i]` via `u16_from_bytes`. -/
theorem encode_decode (v : KeccakBusState) : encodeBusState (decodeBusState v) = v := by
  unfold encodeBusState decodeBusState
  ext i
  simp only [Vector.getElem_ofFn]
  dsimp only [GetElem.getElem, instGetElemSpongeStateNatUInt8LtOfNat,
    ByteArray.instGetElemNatUInt8LtSize, ByteArray.get]
  simp only [show ∀ (arr : Array UInt8) (i : Nat) (h : i < arr.size),
    arr.getInternal i h = arr[i] from fun _ _ _ => rfl]
  simp only [Array.getElem_ofFn]
  simp only [show (2 * i) % 2 = 0 from by omega,
    show ¬ ((2 * i + 1) % 2 = 0) from by omega, ite_true, ite_false]
  simp only [show (2 * i) / 2 = i from by omega,
    show (2 * i + 1) / 2 = i from by omega]
  exact u16_from_bytes (Vector.get v ⟨i, by omega⟩)

end KeccakfPermAir.Spec
