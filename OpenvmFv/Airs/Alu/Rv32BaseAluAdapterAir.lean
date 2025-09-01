import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.ExecutionState
import OpenvmFv.Airs.Memory

set_option linter.unusedVariables false

#define_subair "Rv32BaseAluAdapterAir" using "openvm_encapsulation" where
  SubAir["from_state": "ExecutionState" width := 2]
  Column["rd_ptr"]
  Column["rs1_ptr"]
  Column["rs2"]
  Column["rs2_as"]
  SubAir["reads_aux_0": "MemoryReadAuxCols" width := 3]
  SubAir["reads_aux_1": "MemoryReadAuxCols" width := 3]
  SubAir["writes_aux": "MemoryWriteAuxCols_4" width := 7]


def ExecutionBus : ℕ := 0
def MemoryBus : ℕ := 1
def RangeCheckerBus : ℕ := 4
def ReadInstructionBus : ℕ := 8
def BitwiseBus : ℕ := 9

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
