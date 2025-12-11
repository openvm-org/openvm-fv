import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.Branch.Rv32JalrCoreAir
import OpenvmFv.Airs.Branch.Rv32JalrAdapterAir

import OpenvmFv.Fundamentals.BabyBear

set_option linter.unusedVariables false

#define_air "VmAirWrapper_jalr" using "openvm_encapsulation" where
  MainSubAir["adapter": "Rv32JalrAdapterAir" width := 15]
  MainSubAir["core": "Rv32JalrCoreAir_4" width := 13]

-- def Valid_VmAirWrapper_jallui.to_pc
--   [Field F] [Field ExtF]
--   (c : Valid_VmAirWrapper_jallui F ExtF) (row rotation : ℕ)
-- : F :=
--   c.adapter.inner.from_state.pc row rotation +
--   c.core.is_lui row rotation * 4 +
--   c.core.is_jal row rotation * c.core.imm row rotation

-- @[openvm_encapsulation]
-- lemma VMAirWrapper_jallui.to_pc_def
--   [Field F] [Field ExtF]
--   (c : Valid_VmAirWrapper_jallui F ExtF) (row rotation : ℕ)
-- :
--   c.adapter.inner.from_state.pc row rotation +
--   c.core.is_lui row rotation * 4 +
--   c.core.is_jal row rotation * c.core.imm row rotation =
--   c.to_pc row rotation
-- := rfl
