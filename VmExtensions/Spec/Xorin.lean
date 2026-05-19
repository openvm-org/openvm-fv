/-
  Pure mathematical model of the XORIN opcode.

  Defines what XORIN reads, computes, and outputs at byte level.
  This module is independent of circuit types and Keccak sponge types.
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Xorin.Spec

/-! # Constants -/

/-- Maximum XORIN byte length (Keccak-256 rate in bytes). -/
def XORIN_MAX_LEN : Nat := 136

/-- Number of 4-byte words in the padding array. -/
def NUM_PADDING_WORDS : Nat := 34

/-! # Byte-Level XOR -/

/-- XOR first `len` bytes of `preimage` with `input`. Inactive bytes unchanged. -/
def xorBytesNat (preimage input : ℕ → ℕ) (len : ℕ) : ℕ → ℕ :=
  fun i => if i < len then (preimage i) ^^^ (input i) else preimage i

@[simp] theorem xorBytesNat_active (preimage input : ℕ → ℕ) (len : ℕ) (i : ℕ) (hi : i < len) :
    xorBytesNat preimage input len i = (preimage i) ^^^ (input i) := by
  simp [xorBytesNat, hi]

@[simp] theorem xorBytesNat_inactive (preimage input : ℕ → ℕ) (len : ℕ) (i : ℕ)
    (hi : ¬(i < len)) :
    xorBytesNat preimage input len i = preimage i := by
  simp [xorBytesNat, hi]

theorem xorBytesNat_byte_bound (preimage input : ℕ → ℕ) (len : ℕ)
    (hp : ∀ i, i < len → preimage i < 256)
    (hq : ∀ i, i < len → input i < 256) (i : ℕ) (hi : i < len) :
    xorBytesNat preimage input len i < 256 := by
  simp [xorBytesNat, hi]
  exact Nat.xor_lt_two_pow (n := 8) (hp i hi) (hq i hi)

/-! # Input/Output Structures -/

/-- Inputs to the XORIN opcode. -/
structure XorinInput where
  pc : ℕ
  start_timestamp : ℕ
  buffer_ptr : ℕ
  input_ptr : ℕ
  xorin_len : ℕ
  preimage : ℕ → ℕ
  input : ℕ → ℕ

/-- Outputs of the XORIN opcode. -/
structure XorinOutput where
  next_pc : ℕ
  end_timestamp : ℕ
  postimage : ℕ → ℕ

/-- Validity predicate: length and byte bounds. -/
structure XorinInput.Valid (inp : XorinInput) : Prop where
  len_mod_4 : inp.xorin_len % 4 = 0
  len_le_max : inp.xorin_len ≤ XORIN_MAX_LEN
  preimage_byte_bound : ∀ i, i < inp.xorin_len → inp.preimage i < 256
  input_byte_bound : ∀ i, i < inp.xorin_len → inp.input i < 256

/-! # Pure Execution Model -/

/-- Number of active (non-padding) 4-byte words. -/
def num_active_words (len : ℕ) : ℕ := len / 4

/-- Pure XORIN execution. -/
def execute_xorin_pure (inp : XorinInput) : XorinOutput where
  next_pc := inp.pc + 4
  end_timestamp := inp.start_timestamp + 3 + 3 * num_active_words inp.xorin_len
  postimage := xorBytesNat inp.preimage inp.input inp.xorin_len

/-! # Property Lemmas -/

@[simp] theorem execute_xorin_pure_next_pc (inp : XorinInput) :
    (execute_xorin_pure inp).next_pc = inp.pc + 4 := rfl

@[simp] theorem execute_xorin_pure_end_timestamp (inp : XorinInput) :
    (execute_xorin_pure inp).end_timestamp =
    inp.start_timestamp + 3 + 3 * (inp.xorin_len / 4) := rfl

theorem execute_xorin_pure_postimage_active (inp : XorinInput) (i : ℕ)
    (hi : i < inp.xorin_len) :
    (execute_xorin_pure inp).postimage i = (inp.preimage i) ^^^ (inp.input i) := by
  simp [execute_xorin_pure, hi]

theorem execute_xorin_pure_postimage_inactive (inp : XorinInput) (i : ℕ)
    (hi : ¬(i < inp.xorin_len)) :
    (execute_xorin_pure inp).postimage i = inp.preimage i := by
  simp [execute_xorin_pure, hi]

theorem execute_xorin_pure_postimage_byte_bound (inp : XorinInput) (hv : inp.Valid)
    (i : ℕ) (hi : i < inp.xorin_len) :
    (execute_xorin_pure inp).postimage i < 256 := by
  simp [execute_xorin_pure]
  exact xorBytesNat_byte_bound _ _ _ hv.preimage_byte_bound hv.input_byte_bound i hi

/-! # Validity Lemmas -/

theorem num_active_words_le (len : ℕ) (h : len ≤ XORIN_MAX_LEN) :
    num_active_words len ≤ NUM_PADDING_WORDS := by
  simp [num_active_words, NUM_PADDING_WORDS, XORIN_MAX_LEN] at *
  omega

theorem xorin_len_eq_four_mul (len : ℕ) (h : len % 4 = 0) :
    len = 4 * num_active_words len := by
  simp [num_active_words]
  omega

end Xorin.Spec
