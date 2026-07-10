import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

#define_subair "VariableRangeCols" using "openvm_encapsulation" where
  Column["value"]
  Column["max_bits"]
  Column["two_to_max_bits"]
  Column["mult"]

#define_air "VariableRangeCheckerAir" using "openvm_encapsulation" where
  MainSubAir["main_cols" : "VariableRangeCols" width := 4]
