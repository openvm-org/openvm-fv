import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.Memory

set_option linter.unusedVariables false

#define_air "AccessAdapterAir_2" using "openvm_encapsulation" where
  Column["is_valid"]
  Column["is_split"]
  SubAir["address" : "MemoryAddress" width := 2]
  Column["values_0"]
  Column["values_1"]
  Column["left_timestamp"]
  Column["right_timestamp"]
  Column["is_right_larger"]
  Column["lt_aux_0"]
  Column["lt_aux_1"]

#define_air "AccessAdapterAir_4" using "openvm_encapsulation" where
  Column["is_valid"]
  Column["is_split"]
  SubAir["address" : "MemoryAddress" width := 2]
  Column["values_0"]
  Column["values_1"]
  Column["values_2"]
  Column["values_3"]
  Column["left_timestamp"]
  Column["right_timestamp"]
  Column["is_right_larger"]
  Column["lt_aux_0"]
  Column["lt_aux_1"]
