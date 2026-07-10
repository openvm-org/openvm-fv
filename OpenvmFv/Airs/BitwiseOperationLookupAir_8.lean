import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

#define_subair "BitwiseOperationLookupAir_8Cols" using "openvm_encapsulation" where
  Column["x_bits_0"]
  Column["x_bits_1"]
  Column["x_bits_2"]
  Column["x_bits_3"]
  Column["x_bits_4"]
  Column["x_bits_5"]
  Column["x_bits_6"]
  Column["x_bits_7"]
  Column["y_bits_0"]
  Column["y_bits_1"]
  Column["y_bits_2"]
  Column["y_bits_3"]
  Column["y_bits_4"]
  Column["y_bits_5"]
  Column["y_bits_6"]
  Column["y_bits_7"]
  Column["mult_range"]
  Column["mult_xor"]

#define_air "BitwiseOperationLookupAir_8" using "openvm_encapsulation" where
  MainSubAir["main_cols" : "BitwiseOperationLookupAir_8Cols" width := 18]
