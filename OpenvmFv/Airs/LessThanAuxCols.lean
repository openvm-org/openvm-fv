import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

#define_subair "LessThanAuxCols_2" using "openvm_encapsulation" where
  Column["lower_decomp_0"]
  Column["lower_decomp_1"]
