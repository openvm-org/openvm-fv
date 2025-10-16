import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.ExecutionState
import OpenvmFv.Airs.Memory

set_option linter.unusedVariables false

#define_subair "Rv32RdWriteAdapterAir" using "openvm_encapsulation" where
  SubAir["from_state": "ExecutionState" width := 2]
  Column["rd_ptr"]
  SubAir["rd_aux_cols": "MemoryWriteAuxCols_4" width := 7]
