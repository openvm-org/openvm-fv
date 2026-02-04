import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

#define_subair "ExecutionState" using "openvm_encapsulation" where
  Column["pc"]
  Column["timestamp"]
