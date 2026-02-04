import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.Alu.MultiplicationCoreAir
import OpenvmFv.Airs.Alu.Rv32MultAdapterAir

set_option linter.unusedVariables false

#define_air "VmAirWrapper_mul" using "openvm_encapsulation" where
  MainSubAir["adapter": "Rv32MultAdapterAir" width := 18]
  MainSubAir["core": "MultiplicationCoreAir_4_8" width := 13]
