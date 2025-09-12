import Mathlib

import LeanZKCircuit.OpenVM.Circuit

opaque undefined : Prop

@[openvm_encapsulation]
lemma assert_eq [Field F] (a b: F):
  (a - b = 0) = (a = b)
:= by grind

section BusIndices
  abbrev ExecutionBus : ℕ := 0
  abbrev MemoryBus : ℕ := 1
  abbrev RangeCheckerBus : ℕ := 4
  abbrev ReadInstructionBus : ℕ := 8
  abbrev BitwiseBus : ℕ := 9

  @[openvm_encapsulation]
  lemma Rv32BaseAluAdapterAir_execution_bus:
    (if index = 0 then a else b) =
    if index = ExecutionBus then a else b
  := rfl

  @[openvm_encapsulation]
  lemma Rv32BaseAluAdapterAir_memory_bus:
    (if index = 1 then a else b) =
    if index = MemoryBus then a else b
  := rfl

  @[openvm_encapsulation]
  lemma Rv32BaseAluAdapterAir_range_checker_bus:
    (if index = 4 then a else b) =
    if index = RangeCheckerBus then a else b
  := rfl

  @[openvm_encapsulation]
  lemma Rv32BaseAluAdapterAir_read_instruction_bus:
    (if index = 8 then a else b) =
    if index = ReadInstructionBus then a else b
  := rfl

  @[openvm_encapsulation]
  lemma Rv32BaseAluAdapterAir_bitwise_bus:
    (if index = 9 then a else b) =
    if index = BitwiseBus then a else b
  := rfl
end BusIndices
