import OpenvmFv.Fundamentals.BabyBear

import LeanZKCircuit.Interactions

namespace Interaction

/-- ExecutionBus entry -/
@[simp]
def executionBus_entry
  (mul pc timestamp : FBB)
: (FBB × List FBB) :=
  (mul, [ pc, timestamp ])

/-- Assumptions from execution bus entries -/
def executionBus_assumptions
  (mul _ timestamp : FBB)
: Prop :=
  ¬ mul = 0 →
    -- appropriate ranges
    timestamp < 2 ^ 29

/-- MemoryBus entry -/
@[simp]
def memoryBus_entry
  (mul as ptr x0 x1 x2 x3 timestamp : FBB)
: (FBB × List FBB) :=
  (mul, [as, ptr, x0, x1, x2, x3, timestamp])

/-- Assumptions from memory bus entries -/
def memoryBus_assumptions
  (mul as ptr x0 x1 x2 x3 _ : FBB)
: Prop :=
  ¬ mul = 0 →
    -- appropriate ranges
    as.val < 3 ∧
    ptr.val < 2 ^ 29 ∧
    x0.val < 256 ∧
    x1.val < 256 ∧
    x2.val < 256 ∧
    x3.val < 256

/-- RangeBus entry -/
@[simp]
def rangeCheckerBus_entry
  (mul val deg : FBB)
: (FBB × List FBB) :=
  (mul, [ val, deg ])

 /-- Assumptions from range-checker bus entries -/
def rangeCheckerBus_assumptions
  (mul val deg : FBB)
: Prop :=
  ¬ mul = 0 →
    -- `deg` range
    deg.val < 32 ∧
    -- `val` range
    val.val < 2 ^ deg.val

/-- ReadInstructionBus entry, with parameter
    naming as per OpenVM documentation -/
@[simp]
def readInstructionBus_entry
  (mul pc opcode xa xb xc xd xe xf xg : FBB)
: (FBB × List FBB) :=
  (mul, [ pc, opcode, xa, xb, xc, xd, xe, xf, xg ])

/-- ReadInstructionBus entry -/
def readInstructionBus_assumptions
  (mul _ _ _ _ _ _ _ _ _ : FBB)
: Prop :=
  ¬ mul = 0 →
    True


/-- BitwiseBus entry -/
@[simp]
def bitwiseBus_entry
  (mul a b c is_xor : FBB)
: (FBB × List FBB) :=
  (mul, [ a, b, c, is_xor ])

 /-- Assumptions from bitwise bus entries -/
def bitwiseBus_assumptions
  (mul a b c is_xor : FBB)
: Prop :=
  ¬ mul = 0 →
    -- operand range
    a.val < 256 ∧ b.val < 256 ∧
    -- xor indicator range
    (is_xor = 0 ∨ is_xor = 1) ∧
    -- xor or nothing
    c.val = if is_xor = 0 then 0 else a.val ^^^ b.val

end Interaction
