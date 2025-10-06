import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.Branch.BranchLessThanCoreAir
import OpenvmFv.Airs.Branch.Rv32BranchAdapterAir

set_option linter.unusedVariables false

#define_air "VmAirWrapper_branch_lt" using "openvm_encapsulation" where
  MainSubAir["adapter": "Rv32BranchAdapterAir" width := 10]
  MainSubAir["core": "BranchLessThanCoreAir_4_8" width := 22]


def Valid_VmAirWrapper_branch_lt.to_pc
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_branch_lt F ExtF) (row rotation: ℕ)
: F :=
  c.core.to_pc row rotation (c.adapter.from_state.pc row rotation)

@[openvm_encapsulation]
lemma VmAirWrapper_branch_lt.to_pc_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_branch_lt F ExtF) (row rotation: ℕ)
:
  c.adapter.from_state.pc row rotation +
  c.core.cmp_result row rotation * c.core.imm row rotation +
  (1 - c.core.cmp_result row rotation) * 4 =
  c.to_pc row rotation
:= rfl
