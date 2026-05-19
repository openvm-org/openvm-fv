/-
  Bridge between `xorBytesNat` (pure math on ℕ → ℕ)
  and `xorBytes` (typed SpongeState / ByteArray / UInt8).

  Shows that `xorBytesNat` computes the same thing as `xorBytes`
  when mediated through `.toNat`.
-/
import VmExtensions.Spec.Xorin
import VmExtensions.Keccak.Spec.Absorb

set_option autoImplicit false

namespace Xorin.Bridge

open Xorin.Spec

/-! # Conversion Functions -/

/-- Extract bytes from a SpongeState at offset as a Nat function. -/
def spongeToNatFn (s : SpongeState) (offset : ℕ) : ℕ → ℕ :=
  fun i => if h : offset + i < 200 then
    (s.val[offset + i]'(by have := s.property; omega)).toNat
  else 0

/-- Extract bytes from a ByteArray as a Nat function. -/
def byteArrayToNatFn (ba : ByteArray) : ℕ → ℕ :=
  fun i => if h : i < ba.size then (ba[i]'h).toNat else 0

/-! # Conversion Lemmas -/

@[simp] theorem spongeToNatFn_get (s : SpongeState) (offset i : ℕ)
    (h : offset + i < 200) :
    spongeToNatFn s offset i =
    (s.val[offset + i]'(by have := s.property; omega)).toNat := by
  simp [spongeToNatFn, dif_pos h]

@[simp] theorem byteArrayToNatFn_get (ba : ByteArray) (i : ℕ) (h : i < ba.size) :
    byteArrayToNatFn ba i = (ba[i]'h).toNat := by
  simp [byteArrayToNatFn, dif_pos h]

theorem spongeToNatFn_byte_bound (s : SpongeState) (offset i : ℕ)
    (h : offset + i < 200) :
    spongeToNatFn s offset i < 256 := by
  simp [spongeToNatFn, dif_pos h]
  exact UInt8.toNat_lt _

theorem byteArrayToNatFn_byte_bound (ba : ByteArray) (i : ℕ) (h : i < ba.size) :
    byteArrayToNatFn ba i < 256 := by
  simp [byteArrayToNatFn, dif_pos h]
  exact UInt8.toNat_lt _

/-! # Core Bridge Theorem -/

/-- For any position `i` in range, viewing the `xorBytes` result through
    `spongeToNatFn` equals `xorBytesNat` applied to the converted inputs. -/
theorem xorBytes_toNat_eq_xorBytesNat
    (state : SpongeState) (input : ByteArray)
    (offset len : Nat)
    (h_bound : offset + len ≤ 200) (h_input : len ≤ input.size)
    (i : Nat) (h_range : offset + i < 200) :
    spongeToNatFn (xorBytes state input offset len h_bound h_input) offset i =
    xorBytesNat (spongeToNatFn state offset) (byteArrayToNatFn input) len i := by
  by_cases hi : i < len
  · -- Active case: both sides reduce to XOR
    rw [spongeToNatFn_get _ _ _ h_range]
    rw [xorBytesNat_active _ _ _ _ hi]
    rw [spongeToNatFn_get _ _ _ h_range]
    rw [byteArrayToNatFn_get _ _ (by omega)]
    have h_eq := xorBytes_get_active state input offset len h_bound h_input i hi
    simp only [ByteArray.getElem_eq_data_getElem] at h_eq ⊢
    rw [h_eq]
    exact UInt8.toNat_xor _ _
  · -- Inactive case: both sides reduce to original state
    rw [xorBytesNat_inactive _ _ _ _ hi]
    rw [spongeToNatFn_get _ _ _ h_range]
    rw [spongeToNatFn_get _ _ _ h_range]
    congr 1
    have h_eq := xorBytes_get_inactive state input offset len h_bound h_input
      (offset + i) h_range (Or.inr (by omega))
    simp only [ByteArray.getElem_eq_data_getElem] at h_eq ⊢
    exact h_eq

/-! # Execute Bridge -/

/-- If the pure spec inputs match the sponge/ByteArray data,
    the postimage matches the `xorBytes` result. -/
theorem execute_xorin_postimage_eq_xorBytes
    (state : SpongeState) (input : ByteArray)
    (offset : ℕ) (inp : XorinInput)
    (h_bound : offset + inp.xorin_len ≤ 200)
    (h_input : inp.xorin_len ≤ input.size)
    (h_pre : ∀ i, i < inp.xorin_len →
      inp.preimage i = spongeToNatFn state offset i)
    (h_inp : ∀ i, i < inp.xorin_len →
      inp.input i = byteArrayToNatFn input i)
    (i : Nat) (hi : i < inp.xorin_len) :
    (execute_xorin_pure inp).postimage i =
    spongeToNatFn
      (xorBytes state input offset inp.xorin_len h_bound h_input) offset i := by
  simp only [execute_xorin_pure, xorBytesNat_active _ _ _ _ hi]
  rw [h_pre i hi, h_inp i hi]
  rw [← xorBytesNat_active _ _ _ _ hi]
  exact (xorBytes_toNat_eq_xorBytesNat state input offset inp.xorin_len
    h_bound h_input i (by omega)).symm

/-! # Validity Bridge -/

/-- Sponge/ByteArray data satisfies `XorinInput.Valid` byte bounds. -/
theorem xorinInput_valid_of_sponge
    (state : SpongeState) (input : ByteArray)
    (offset len : ℕ) (pc ts bp ip : ℕ)
    (h_bound : offset + len ≤ 200) (h_input : len ≤ input.size)
    (h_mod : len % 4 = 0) (h_max : len ≤ XORIN_MAX_LEN) :
    XorinInput.Valid {
      pc := pc, start_timestamp := ts,
      buffer_ptr := bp, input_ptr := ip,
      xorin_len := len,
      preimage := spongeToNatFn state offset,
      input := byteArrayToNatFn input } where
  len_mod_4 := h_mod
  len_le_max := h_max
  preimage_byte_bound := fun i (hi : i < len) =>
    spongeToNatFn_byte_bound state offset i (by omega)
  input_byte_bound := fun i (hi : i < len) =>
    byteArrayToNatFn_byte_bound input i (by omega)

end Xorin.Bridge
