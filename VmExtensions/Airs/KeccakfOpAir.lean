/-
  Minimal concrete AIR interface for KeccakfOpAir.

  Contains circuit plumbing plus `last_row`. The `RowLocalFacts` bundle is the
  row-local fact structure derived from column-native views.
-/
import LeanZKCircuit.OpenVM.Circuit
import VmExtensions.Spec.KeccakfOp
import VmExtensions.Soundness.Keccakf.Interface

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfOpAir

open Keccakf.Interface
open KeccakfOp.Spec

def memoryPtrBound : Nat := 2 ^ 29

def REGISTER_AS : Nat := 1

def MEMORY_AS : Nat := 2

def WORD_BYTES : Nat := 4

abbrev KeccakWordBytes := Vector UInt8 WORD_BYTES

/-- Byte `k` of 4-byte word `j` in a `SpongeState`, in memory order. -/
def spongeWordByte (s : SpongeState) (j : Fin NUM_STATE_WORDS) (k : Fin WORD_BYTES) : UInt8 :=
  s[WORD_BYTES * j.val + k.val]'(by
    have hj : j.val < NUM_STATE_WORDS := j.isLt
    have hk : k.val < WORD_BYTES := k.isLt
    have h_idx : WORD_BYTES * j.val + k.val < STATE_SIZE := by
      simp [WORD_BYTES, NUM_STATE_WORDS, STATE_SIZE] at hj hk ⊢
      omega
    simpa [STATE_SIZE] using h_idx)

/-- Word `j` of a `SpongeState`, grouped as 4 bytes in memory order. -/
def spongeWord (s : SpongeState) (j : Fin NUM_STATE_WORDS) : KeccakWordBytes :=
  Vector.ofFn fun k => spongeWordByte s j k

/-- Execution-side facts exposed by a valid opcode row. -/
structure ExecutionLocalFacts
    (input : KeccakfOpInput)
    (output : KeccakfOpOutput) : Prop where
  next_pc : output.next_pc = input.pc + 4
  end_timestamp : output.end_timestamp = input.start_timestamp + TIMESTAMP_DELTA

/-- Instruction-side facts exposed by a valid opcode row. -/
structure InstructionLocalFacts
    (input : KeccakfOpInput)
    (rdPtr : Nat) : Prop where
  rd_ptr_lt : rdPtr < memoryPtrBound

/-- Concrete witness for the single register read that yields `buffer_ptr`. -/
structure BufferPtrReadWitness where
  addressSpace : Nat
  ptr : Nat
  timestamp : Nat
  value : Nat

/-- Concrete schedule witness for the 50 memory writes of the permuted state. -/
structure BufferWriteWitness where
  addressSpace : Nat
  ptr : Fin NUM_STATE_WORDS → Nat
  timestamp : Fin NUM_STATE_WORDS → Nat
  prevWord : Fin NUM_STATE_WORDS → KeccakWordBytes
  data : Fin NUM_STATE_WORDS → KeccakWordBytes

/-- Concrete facts for the single register read that yields `buffer_ptr`. -/
def BufferPtrReadFacts
    (input : KeccakfOpInput)
    (rdPtr : Nat) : Prop :=
  ∃ read : BufferPtrReadWitness,
    read.addressSpace = REGISTER_AS ∧
    read.ptr = rdPtr ∧
    read.timestamp = input.start_timestamp ∧
    read.value = input.buffer_ptr

/-- Concrete facts for the 50 memory writes of the permuted state. -/
def BufferWriteFacts
    (input : KeccakfOpInput)
    (output : KeccakfOpOutput) : Prop :=
  ∃ writes : BufferWriteWitness,
    writes.addressSpace = MEMORY_AS ∧
    (∀ j, writes.ptr j = input.buffer_ptr + WORD_BYTES * j.val) ∧
    (∀ j, writes.timestamp j = input.start_timestamp + 1 + j.val) ∧
    (∀ j, writes.prevWord j = spongeWord input.preimage j) ∧
    (∀ j, writes.data j = spongeWord output.postimage j)

/-- Memory-side facts exposed by a valid opcode row. -/
structure MemoryLocalFacts
    (input : KeccakfOpInput)
    (output : KeccakfOpOutput)
    (rdPtr : Nat) : Prop where
  buffer_ptr_lt : input.buffer_ptr < memoryPtrBound
  register_read : BufferPtrReadFacts input rdPtr
  buffer_writes : BufferWriteFacts input output

/-- Named row-local fact bundle for the opcode side.
    Owns the message-normalization obligations that tie the row message surface
    back to `mkPreMsg` / `mkPostMsg`, plus the timestamp bound. -/
structure RowLocalFacts
    (input : KeccakfOpInput)
    (output : KeccakfOpOutput)
    (rdPtr : Nat)
    (preMsg postMsg : KeccakStateMsg) : Prop where
  execution : ExecutionLocalFacts input output
  instruction : InstructionLocalFacts input rdPtr
  memory : MemoryLocalFacts input output rdPtr
  pre_flag : preMsg.isPost = false
  post_flag : postMsg.isPost = true
  pre_timestamp : preMsg.timestamp = input.start_timestamp
  post_timestamp : postMsg.timestamp = input.start_timestamp
  timestamp_lt : input.start_timestamp < timestampBound

/-- Minimal concrete opcode AIR structure.
    Contains only circuit plumbing and `last_row`. Row-level interpretation
    is provided by column-native views in `KeccakfOpAirViews.lean`. -/
structure Raw_KeccakfOpAir (F : Type) (ExtF : Type) where
  buses (index : ℕ) : List (F × List F)
  keccakStateBusIndex : ℕ
  challenge (index : ℕ) : ExtF
  exposed (index : ℕ) : ExtF
  main (id : ℕ) (column : ℕ) (row : ℕ) (rotation : ℕ) : F
  permutation (column : ℕ) (row : ℕ) (rotation : ℕ) : ExtF
  preprocessed (column : ℕ) (row : ℕ) (rotation : ℕ) : F
  public_values (index : ℕ) : F
  last_row : ℕ

instance {F ExtF} [Field F] [Field ExtF] : Circuit F ExtF Raw_KeccakfOpAir where
  buses := Raw_KeccakfOpAir.buses
  challenge := Raw_KeccakfOpAir.challenge
  exposed := Raw_KeccakfOpAir.exposed
  main := Raw_KeccakfOpAir.main
  permutation := Raw_KeccakfOpAir.permutation
  preprocessed := Raw_KeccakfOpAir.preprocessed
  public_values := Raw_KeccakfOpAir.public_values
  last_row := Raw_KeccakfOpAir.last_row

/-- Validity for `Raw_KeccakfOpAir` (trivially true — no abstract invariants). -/
def Raw_KeccakfOpAir.isValid {F ExtF} (_c : Raw_KeccakfOpAir F ExtF) : Prop := True

/-- Valid KeccakfOpAir: a `Raw_KeccakfOpAir` satisfying `isValid`. -/
abbrev Valid_KeccakfOpAir (F : Type) (ExtF : Type) :=
  { c : Raw_KeccakfOpAir F ExtF // c.isValid }

abbrev Valid_KeccakfOpAir.buses {F ExtF} (c : Valid_KeccakfOpAir F ExtF) := c.1.buses
abbrev Valid_KeccakfOpAir.keccakStateBusIndex {F ExtF}
    (c : Valid_KeccakfOpAir F ExtF) := c.1.keccakStateBusIndex
abbrev Valid_KeccakfOpAir.challenge {F ExtF} (c : Valid_KeccakfOpAir F ExtF) := c.1.challenge
abbrev Valid_KeccakfOpAir.exposed {F ExtF} (c : Valid_KeccakfOpAir F ExtF) := c.1.exposed
abbrev Valid_KeccakfOpAir.main {F ExtF} (c : Valid_KeccakfOpAir F ExtF) := c.1.main
abbrev Valid_KeccakfOpAir.permutation {F ExtF} (c : Valid_KeccakfOpAir F ExtF) := c.1.permutation
abbrev Valid_KeccakfOpAir.preprocessed {F ExtF} (c : Valid_KeccakfOpAir F ExtF) := c.1.preprocessed
abbrev Valid_KeccakfOpAir.public_values {F ExtF} (c : Valid_KeccakfOpAir F ExtF) := c.1.public_values
abbrev Valid_KeccakfOpAir.last_row {F ExtF} (c : Valid_KeccakfOpAir F ExtF) := c.1.last_row

instance {F ExtF} [Field F] [Field ExtF] : Circuit F ExtF Valid_KeccakfOpAir where
  buses := Valid_KeccakfOpAir.buses
  challenge := Valid_KeccakfOpAir.challenge
  exposed := Valid_KeccakfOpAir.exposed
  main := Valid_KeccakfOpAir.main
  permutation := Valid_KeccakfOpAir.permutation
  preprocessed := Valid_KeccakfOpAir.preprocessed
  public_values := Valid_KeccakfOpAir.public_values
  last_row := Valid_KeccakfOpAir.last_row

end KeccakfOpAir
