import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.Branch.Rv32AuipcCoreAir
import OpenvmFv.Airs.Branch.Rv32RdWriteAdapterAir

set_option linter.unusedVariables false

#define_air "VmAirWrapper_auipc" using "openvm_encapsulation" where
  MainSubAir["adapter": "Rv32RdWriteAdapterAir" width := 10]
  MainSubAir["core": "Rv32AuipcCoreAir" width := 10]


-- def Valid_VmAirWrapper_branch_eq.to_pc
--   [Field F] [Field ExtF]
--   (c : Valid_VmAirWrapper_branch_eq F ExtF) (row rotation: ℕ)
-- : F :=
--   c.core.to_pc row rotation (c.adapter.from_state.pc row rotation)

-- @[openvm_encapsulation]
-- lemma VmAirWrapper_branch_eq.to_pc_def
--   [Field F] [Field ExtF]
--   (c : Valid_VmAirWrapper_branch_eq F ExtF) (row rotation: ℕ)
-- :
--   c.adapter.from_state.pc row rotation +
--   c.core.cmp_result row rotation * c.core.imm row rotation +
--   (1 - c.core.cmp_result row rotation) * 4 =
--   c.to_pc row rotation
-- := rfl

@[openvm_encapsulation]
lemma VmAirWrapper_auipc.pc_msl
  [Field F]
  (c : Valid_VmAirWrapper_auipc F ExtF) (row rotation: ℕ)
:
  (c.adapter.from_state.pc row rotation - c.core.intermed_val row rotation) * 2013265801 =
  c.core.pc_msl row rotation (c.adapter.from_state.pc row rotation)
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_auipc.carry_1_def
  [Field F]
  (c : Valid_VmAirWrapper_auipc F ExtF) (row rotation : ℕ)
:
  2005401601 * (
    c.core.pc_limbs_0 row rotation +
    c.core.imm_limbs_0 row rotation -
    c.core.rd_data_1 row rotation
  ) =
c.core.carry row rotation (c.adapter.from_state.pc row rotation) 1
:= by
  simp [
    Valid_Rv32AuipcCoreAir.carry,
    Valid_Rv32AuipcCoreAir.carry_divide,
    Valid_Rv32AuipcCoreAir.pc_limbs
  ]

@[openvm_encapsulation]
lemma VmAirWrapper_auipc.carry_2_def
  [Field F]
  (c : Valid_VmAirWrapper_auipc F ExtF) (row rotation : ℕ)
:
  2005401601 * (
    c.core.pc_limbs_1 row rotation +
    c.core.imm_limbs_1 row rotation -
    c.core.rd_data_2 row rotation +
    c.core.carry row rotation (c.adapter.from_state.pc row rotation) 1
  ) =
c.core.carry row rotation (c.adapter.from_state.pc row rotation) 2
:= by
  simp [
    Valid_Rv32AuipcCoreAir.carry,
    Valid_Rv32AuipcCoreAir.carry_divide,
    Valid_Rv32AuipcCoreAir.pc_limbs
  ]

@[openvm_encapsulation]
lemma VmAirWrapper_auipc.carry_3_def
  [Field F]
  (c : Valid_VmAirWrapper_auipc F ExtF) (row rotation : ℕ)
:
  2005401601 * (
    c.core.pc_msl row rotation (c.adapter.from_state.pc row rotation) +
    c.core.imm_limbs_2 row rotation -
    c.core.rd_data_3 row rotation +
    c.core.carry row rotation (c.adapter.from_state.pc row rotation) 2
  ) =
c.core.carry row rotation (c.adapter.from_state.pc row rotation) 3
:= by
  simp [
    Valid_Rv32AuipcCoreAir.carry,
    Valid_Rv32AuipcCoreAir.carry_divide,
    Valid_Rv32AuipcCoreAir.pc_limbs,
    Valid_Rv32AuipcCoreAir.pc_msl
  ]
