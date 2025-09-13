import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.ExecutionState
import OpenvmFv.Airs.Memory

set_option linter.unusedVariables false

#define_subair "Rv32MultAdapterAir" using "openvm_encapsulation" where
  SubAir["from_state": "ExecutionState" width := 2]
  Column["rd_ptr"]
  Column["rs1_ptr"]
  Column["rs2_ptr"]
  SubAir["reads_aux_0": "MemoryReadAuxCols" width := 3]
  SubAir["reads_aux_1": "MemoryReadAuxCols" width := 3]
  SubAir["writes_aux": "MemoryWriteAuxCols_4" width := 7]
