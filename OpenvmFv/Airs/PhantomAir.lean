import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

#define_air "PhantomAir" using "openvm_encapsulation" where
  Column["pc"]
  Column["operand_0"]
  Column["operand_1"]
  Column["operand_2"]
  Column["timestamp"]
  Column["is_valid"]
