/-
  Pure mathematical model of the KeccakfOp opcode.

  The KeccakfOp chip reads 200 bytes (preimage) from memory, applies the
  Keccak-f[1600] permutation, and writes back 200 bytes (postimage).

  The state is represented as 100 u16 limbs in the circuit trace (pairs of
  consecutive bytes packed little-endian), but this spec works at byte level.
  That representation detail does not determine the opcode timestamp delta:
  the proving path does one timed register read and fifty timed 4-byte writes.
-/
import Mathlib
import VmExtensions.Keccak.Spec.Permutation

set_option autoImplicit false

namespace KeccakfOp.Spec

/-! # Constants -/

/-- Keccak state size in bytes. -/
def STATE_SIZE : Nat := 200

/-- Number of u16 limbs representing the state in the circuit. -/
def NUM_LIMBS : Nat := 100

/-- Number of 4-byte words in the 200-byte state. -/
def NUM_STATE_WORDS : Nat := STATE_SIZE / 4

/-- Timestamp delta of KeccakfOpAir execution:
    one register read plus one write per 4-byte state word. -/
def TIMESTAMP_DELTA : Nat := 1 + NUM_STATE_WORDS

/-! # Input/Output Structures -/

/-- Inputs to the KeccakfOp opcode. -/
structure KeccakfOpInput where
  pc : ℕ
  start_timestamp : ℕ
  buffer_ptr : ℕ
  preimage : SpongeState

/-- Outputs of the KeccakfOp opcode. -/
structure KeccakfOpOutput where
  next_pc : ℕ
  end_timestamp : ℕ
  postimage : SpongeState

/-! # Pure Execution Model -/

/-- Pure KeccakfOp execution: apply Keccak-f[1600] to the preimage. -/
def execute (inp : KeccakfOpInput) : KeccakfOpOutput where
  next_pc := inp.pc + 4
  end_timestamp := inp.start_timestamp + TIMESTAMP_DELTA
  postimage := Keccak.keccakF inp.preimage

/-! # Property Lemmas -/

@[simp] theorem execute_next_pc (inp : KeccakfOpInput) :
    (execute inp).next_pc = inp.pc + 4 := rfl

@[simp] theorem execute_end_timestamp (inp : KeccakfOpInput) :
    (execute inp).end_timestamp = inp.start_timestamp + TIMESTAMP_DELTA := rfl

@[simp] theorem execute_postimage (inp : KeccakfOpInput) :
    (execute inp).postimage = Keccak.keccakF inp.preimage := rfl

end KeccakfOp.Spec
