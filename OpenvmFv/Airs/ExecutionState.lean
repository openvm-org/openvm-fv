import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Tactics.Air.define_air

set_option linter.unusedVariables false

#define_air "ExecutionState" using "openvm_encapsulation" where
  Column["pc"]
  Column["timestamp"]
