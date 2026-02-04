import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.Branch.BranchEqualCoreAir
import OpenvmFv.Airs.Branch.Rv32BranchAdapterAir

set_option linter.unusedVariables false

#define_air "VmAirWrapper_branch_eq" using "openvm_encapsulation" where
  MainSubAir["adapter": "Rv32BranchAdapterAir" width := 10]
  MainSubAir["core": "BranchEqualCoreAir_4" width := 16]


def Valid_VmAirWrapper_branch_eq.to_pc
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_branch_eq F ExtF) (row rotation: ℕ)
: F :=
  c.core.to_pc row rotation (c.adapter.from_state.pc row rotation)

@[openvm_encapsulation]
lemma VmAirWrapper_branch_eq.to_pc_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_branch_eq F ExtF) (row rotation: ℕ)
:
  c.adapter.from_state.pc row rotation +
  c.core.cmp_result row rotation * c.core.imm row rotation +
  (1 - c.core.cmp_result row rotation) * 4 =
  c.to_pc row rotation
:= rfl
