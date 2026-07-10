/-
  Public absorb interface for the Keccak sponge construction.

  This module provides byte-level XOR semantics for the sponge absorb step,
  independent of the private internals in `Basic.lean`.
-/
import Batteries.Data.ByteArray

set_option autoImplicit false

/-! # Constants -/

/-- Keccak rate in bytes (r = 1600 − 2·256 = 136 bytes for Keccak-256). -/
def KECCAK_RATE : Nat := 136

/-- Keccak state size in bytes (b = 1600 bits = 200 bytes). -/
def KECCAK_STATE_SIZE : Nat := 200

/-! # SpongeState -/

/-- A 200-byte array representing the Keccak sponge state at byte level. -/
def SpongeState := { val : ByteArray // val.size = 200 }

/-- Create a zero-initialized sponge state. -/
def mkSpongeState : SpongeState :=
  ⟨ByteArray.mk (Array.replicate 200 0), by
    change (Array.replicate 200 0).size = 200
    simp
  ⟩

instance : GetElem SpongeState Nat UInt8 (fun _ i => i < 200) where
  getElem s i h := s.val[i]'(by have := s.property; omega)

@[simp] theorem SpongeState.size_eq (s : SpongeState) : s.val.size = 200 := s.property

/-! # ByteArray helper lemmas for Nat-based set API -/

@[simp] private theorem ByteArray_size_set (a : ByteArray) (i : Nat) (v : UInt8)
    (h : i < a.size) : (a.set i v).size = a.size :=
  Array.size_set h

@[simp] private theorem ByteArray_getElem_set (a : ByteArray) (i : Nat) (v : UInt8)
    (hi : i < a.size) {j : Nat} {hj : j < (a.set i v).size} :
    (a.set i v)[j]'hj =
    if i = j then v else a[j]'(by simp [ByteArray_size_set] at hj; exact hj) := by
  simp only [ByteArray.getElem_eq_data_getElem]
  simp [ByteArray.data_set, Array.getElem_set]

/-! # Internal helper: xorBytesAux -/

/-- XOR `n` bytes from `input` into `acc` at positions `[offset, offset+n)`.
    Uses decidable-if guards so the function is total without preconditions. -/
private def xorBytesAux (acc : ByteArray) (input : ByteArray) (offset : Nat) :
    Nat → ByteArray
  | 0 => acc
  | n + 1 =>
    let prev := xorBytesAux acc input offset n
    if h₁ : offset + n < prev.size then
      if h₂ : n < input.size then
        prev.set (offset + n) (prev[offset + n]'h₁ ^^^ input[n]'h₂)
      else prev
    else prev

/-- Size is preserved by `xorBytesAux`. -/
@[simp] private theorem xorBytesAux_size {acc : ByteArray} {input : ByteArray}
    {offset n : Nat} :
    (xorBytesAux acc input offset n).size = acc.size := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold xorBytesAux
    by_cases h₁ : offset + n < (xorBytesAux acc input offset n).size
    · by_cases h₂ : n < input.size
      · have h₁' : offset + n < acc.size := by simpa [ih] using h₁
        simp [h₁', h₂, ih]
      · have h₁' : offset + n < acc.size := by simpa [ih] using h₁
        simp [h₁', h₂, ih]
    · have h₁' : ¬ offset + n < acc.size := by simpa [ih] using h₁
      simp [h₁', ih]

/-- Inactive bytes are unchanged by `xorBytesAux`. -/
private theorem xorBytesAux_get_inactive {acc : ByteArray} {input : ByteArray}
    {offset n : Nat}
    (h_acc : acc.size = 200) (h_bound : offset + n ≤ 200) (h_input : n ≤ input.size)
    {j : Nat} (hj : j < 200) (h_outside : j < offset ∨ j ≥ offset + n) :
    (xorBytesAux acc input offset n)[j]'(by simp [xorBytesAux_size]; omega) =
    acc[j]'(by omega) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold xorBytesAux
    have h_g1 : offset + n < (xorBytesAux acc input offset n).size := by
      simp [xorBytesAux_size]; omega
    have h_g2 : n < input.size := by omega
    simp only [dif_pos h_g1, dif_pos h_g2]
    have hne : offset + n ≠ j := by omega
    simp only [ByteArray_getElem_set, hne, ↓reduceIte]
    exact ih (by omega) (by omega) (by omega)

/-- Active bytes get XORed by `xorBytesAux`. -/
private theorem xorBytesAux_get_active {acc : ByteArray} {input : ByteArray}
    {offset n : Nat}
    (h_acc : acc.size = 200) (h_bound : offset + n ≤ 200) (h_input : n ≤ input.size)
    {i : Nat} (hi : i < n) :
    (xorBytesAux acc input offset n)[offset + i]'(by simp [xorBytesAux_size]; omega) =
    acc[offset + i]'(by omega) ^^^ input[i]'(by omega) := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold xorBytesAux
    have h_g1 : offset + n < (xorBytesAux acc input offset n).size := by
      simp [xorBytesAux_size]; omega
    have h_g2 : n < input.size := by omega
    simp only [dif_pos h_g1, dif_pos h_g2]
    by_cases heq : i = n
    · subst heq
      simp only [ByteArray_getElem_set, ↓reduceIte]
      congr 1
      exact xorBytesAux_get_inactive h_acc (by omega) (by omega) (by omega)
        (Or.inr (Nat.le_refl _))
    · have hne : offset + n ≠ offset + i := by omega
      simp only [ByteArray_getElem_set, hne, ↓reduceIte]
      exact ih (by omega) (by omega) (by omega)

/-! # Public API -/

/-- XOR `len` bytes from `input` into `state` at positions `[offset, offset+len)`.
    For `i ∈ [0, len)`: `result[offset + i] = state[offset + i] ^^^ input[i]`.
    All other bytes are unchanged. -/
def xorBytes (state : SpongeState) (input : ByteArray) (offset len : Nat)
    (_h_bound : offset + len ≤ 200) (_h_input : len ≤ input.size) : SpongeState :=
  ⟨xorBytesAux state.val input offset len,
   by simp [xorBytesAux_size, state.property]⟩

/-- Size preservation: `xorBytes` produces a 200-byte state. -/
@[simp] theorem xorBytes_size (state : SpongeState) (input : ByteArray)
    (offset len : Nat)
    (h_bound : offset + len ≤ 200) (h_input : len ≤ input.size) :
    (xorBytes state input offset len h_bound h_input).val.size = 200 :=
  (xorBytes state input offset len h_bound h_input).property

/-- Active bytes get XORed: for `i < len`,
    `result[offset + i] = state[offset + i] ^^^ input[i]`. -/
theorem xorBytes_get_active (state : SpongeState) (input : ByteArray)
    (offset len : Nat)
    (h_bound : offset + len ≤ 200) (h_input : len ≤ input.size)
    (i : Nat) (h_i : i < len) :
    (xorBytes state input offset len h_bound h_input).val[offset + i]'(by
      simp [xorBytes, xorBytesAux_size, state.property]; omega) =
    state.val[offset + i]'(by have := state.property; omega) ^^^
    input[i]'(by omega) :=
  xorBytesAux_get_active state.property h_bound h_input h_i

/-- Inactive bytes unchanged: for `j` outside `[offset, offset + len)`,
    `result[j] = state[j]`. -/
theorem xorBytes_get_inactive (state : SpongeState) (input : ByteArray)
    (offset len : Nat)
    (h_bound : offset + len ≤ 200) (h_input : len ≤ input.size)
    (j : Nat) (h_j : j < 200) (h_outside : j < offset ∨ j ≥ offset + len) :
    (xorBytes state input offset len h_bound h_input).val[j]'(by
      simp [xorBytes, xorBytesAux_size, state.property]; omega) =
    state.val[j]'(by have := state.property; omega) :=
  xorBytesAux_get_inactive state.property h_bound h_input h_j h_outside

/-- Rate-bounded XOR: convenience wrapper enforcing `offset + len ≤ KECCAK_RATE`. -/
def xorBytesRate (state : SpongeState) (input : ByteArray) (offset len : Nat)
    (h_rate : offset + len ≤ KECCAK_RATE) (h_input : len ≤ input.size) :
    SpongeState :=
  xorBytes state input offset len (by unfold KECCAK_RATE at h_rate; omega) h_input
