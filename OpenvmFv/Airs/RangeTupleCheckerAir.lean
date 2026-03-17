import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

#define_subair "RangeTupleCheckerAirCols" using "openvm_encapsulation" where
  Column["tuple_0"]
  Column["tuple_1"]
  Column["mult"]

#define_air "RangeTupleCheckerAir" using "openvm_encapsulation" where
  MainSubAir["main_cols" : "RangeTupleCheckerAirCols" width := 3]
