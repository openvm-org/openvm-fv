import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

#define_air "VariableRangeCols" using "openvm_encapsulation" where
  Column["mult"]

#define_air "VariableRangeCheckerAir" using "openvm_encapsulation" where
  SubAir["air" : "VariableRangeCols" width := 1]

#print Valid_VariableRangeCheckerAir
