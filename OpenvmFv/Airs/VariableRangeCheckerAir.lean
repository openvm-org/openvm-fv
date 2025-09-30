import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

#define_subair "VariableRangePreprocessedCols" using "openvm_encapsulation" where
  Column["value"]
  Column["max_bits"]

#define_subair "VariableRangeCols" using "openvm_encapsulation" where
  Column["mult"]

#define_air "VariableRangeCheckerAir" using "openvm_encapsulation" where
  MainSubAir["main_cols" : "VariableRangeCols" width := 1]
  PreprocessedSubAir["preprocessed_cols" : "VariableRangePreprocessedCols" width := 2]
