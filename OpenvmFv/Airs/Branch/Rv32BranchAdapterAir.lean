import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.ExecutionState
import OpenvmFv.Airs.Memory

set_option linter.unusedVariables false

#define_subair "Rv32BranchAdapterAir" using "openvm_encapsulation" where
  SubAir["from_state": "ExecutionState" width := 2]
  Column["rs1_ptr"]
  Column["rs2_ptr"]
  SubAir["reads_aux": "MemoryReadAuxCols" width := 3]
