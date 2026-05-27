import Mathlib

import LeanZKCircuit.OpenVM.Circuit

opaque undefined : Prop

@[openvm_encapsulation]
lemma assert_eq [Field F] (a b: F):
  (a - b = 0) = (a = b)
:= by grind

-- @[openvm_encapsulation]
lemma eq_constant_1 {T: Type} (x: T) [inst: OfNat T 1]:
  ((@OfNat.ofNat T (nat_lit 1) inst) = x) = (x = (@OfNat.ofNat T (nat_lit 1) inst))
:= by grind

-- @[openvm_encapsulation]
lemma eq_constant_256 {T: Type} (x: T) [inst: OfNat T 256]:
  ((@OfNat.ofNat T (nat_lit 256) inst) = x) = (x = (@OfNat.ofNat T (nat_lit 256) inst))
:= by grind

section BusIndices
  abbrev ExecutionBus : ℕ := 0
  abbrev MemoryBus : ℕ := 1
  abbrev ProgramBus : ℕ := 2
  abbrev RangeCheckerBus : ℕ := 3
  abbrev BitwiseBus : ℕ := 6
  abbrev RangeTupleCheckerBus : ℕ := 10

  @[openvm_encapsulation]
  lemma execution_bus_simplification:
    (if index = 0 then a else b) =
    if index = ExecutionBus then a else b
  := rfl

  @[openvm_encapsulation]
  lemma memory_bus_simplification:
    (if index = 1 then a else b) =
    if index = MemoryBus then a else b
  := rfl

  @[openvm_encapsulation]
  lemma range_checker_bus_simplification:
    (if index = 3 then a else b) =
    if index = RangeCheckerBus then a else b
  := rfl

  @[openvm_encapsulation]
  lemma read_instruction_bus_simplification:
    (if index = 2 then a else b) =
    if index = ProgramBus then a else b
  := rfl

  @[openvm_encapsulation]
  lemma bitwise_bus_simplification:
    (if index = 6 then a else b) =
    if index = BitwiseBus then a else b
  := rfl

  @[openvm_encapsulation]
  lemma range_tuple_checker_bus_simplification:
    (if index = 10 then a else b) =
    if index = RangeTupleCheckerBus then a else b
  := rfl
end BusIndices
