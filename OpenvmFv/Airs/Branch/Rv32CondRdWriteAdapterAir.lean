import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.Branch.Rv32RdWriteAdapterAir

set_option linter.unusedVariables false

#define_subair "Rv32CondRdWriteAdapterAir" using "openvm_encapsulation" where
  SubAir["inner": "Rv32RdWriteAdapterAir" width := 10]
  Column["needs_write"]
