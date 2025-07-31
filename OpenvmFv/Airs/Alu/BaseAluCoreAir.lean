import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

#define_air "BaseAluCoreAir" using "openvm_encapsulation" where
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  Column["c_0"]
  Column["c_1"]
  Column["c_2"]
  Column["c_3"]
  Column["opcode_add_flag"]
  Column["opcode_sub_flag"]
  Column["opcode_xor_flag"]
  Column["opcode_or_flag"]
  Column["opcode_and_flag"]
