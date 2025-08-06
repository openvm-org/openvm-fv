import LeanZKCircuit.Command.Air.define_air
import OpenvmFv.Airs.Alu.BaseAluCoreAir
import OpenvmFv.Airs.Alu.Rv32BaseAluAdapterAir

set_option linter.unusedVariables false

#define_air "VmAirWrapper_alu" using "openvm_encapsulation" where
  SubAir["adapter": "Rv32BaseAluAdapterAir" width := 19]
  SubAir["core": "BaseAluCoreAir" width := 17]
