import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.Branch.Rv32JalrCoreAir
import OpenvmFv.Airs.Branch.Rv32JalrAdapterAir

import OpenvmFv.Fundamentals.BabyBear

set_option linter.unusedVariables false

#define_air "VmAirWrapper_jalr" using "openvm_encapsulation" where
  MainSubAir["adapter": "Rv32JalrAdapterAir" width := 15]
  MainSubAir["core": "Rv32JalrCoreAir_4" width := 13]

@[openvm_encapsulation]
lemma VmAirWrapper_jalr.rs1_limbs_01_def
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
:
  c.rs1_data_0 row rotation +
  c.rs1_data_1 row rotation * 256 =
  c.rs1_limbs_01 row rotation
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_jalr.rs1_limbs_23_def
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
:
  c.rs1_data_2 row rotation +
  c.rs1_data_3 row rotation * 256 =
  c.rs1_limbs_23 row rotation
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_jalr.carry_def
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
:
  (c.rs1_limbs_01 row rotation +
  c.imm row rotation -
  c.to_pc_limbs_0 row rotation * 2 -
  c.to_pc_least_sig_bit row rotation) *
  2013235201 =
  c.carry row rotation
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_jalr.imm_extended_limb_def
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
:
  c.imm_sign row rotation * 65535 =
  c.imm_extended_limb row rotation
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_jalr.carry'_def
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
:
  (c.rs1_limbs_23 row rotation +
  c.imm_extended_limb row rotation +
  c.carry row rotation -
  c.to_pc_limbs_1 row rotation) *
  2013235201 =
  c.carry' row rotation
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_jalr.to_pc_def
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
:
  c.to_pc_limbs_0 row rotation * 2 +
  c.to_pc_limbs_1 row rotation * 65536 =
  c.to_pc row rotation
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_jalr.write_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_jalr F ExtF) (row rotation : ℕ)
:
  [
    1,
    c.adapter.rd_ptr row rotation,
    c.adapter.from_state.pc row rotation + 4 -
    (
      c.core.rd_data_0 row rotation * 256 +
      c.core.rd_data_1 row rotation * 65536 +
      c.core.rd_data_2 row rotation * 16777216
    ),
    c.core.rd_data_0 row rotation,
    c.core.rd_data_1 row rotation,
    c.core.rd_data_2 row rotation,
    c.adapter.from_state.timestamp row rotation + 1
  ] =
  [
    1,
    c.adapter.rd_ptr row rotation,
    c.core.rd_data row rotation (c.adapter.from_state.pc row rotation) 0,
    c.core.rd_data row rotation (c.adapter.from_state.pc row rotation) 1,
    c.core.rd_data row rotation (c.adapter.from_state.pc row rotation) 2,
    c.core.rd_data row rotation (c.adapter.from_state.pc row rotation) 3,
    c.adapter.from_state.timestamp row rotation + 1
  ]
:= by
  simp [
    Valid_Rv32JalrCoreAir_4.rd_data,
    Valid_Rv32JalrCoreAir_4.least_sig_limb,
    Valid_Rv32JalrCoreAir_4.composed
  ]

@[openvm_encapsulation]
lemma VmAirWrapper_jalr.bitwise_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_jalr F ExtF) (row rotation : ℕ)
:
  [
    c.adapter.from_state.pc row rotation + 4 -
    (
      c.core.rd_data_0 row rotation * 256 +
      c.core.rd_data_1 row rotation * 65536 +
      c.core.rd_data_2 row rotation * 16777216
    ),
    c.core.rd_data_0 row rotation,
    0,
    0
  ]=
  [
    c.core.rd_data row rotation (c.adapter.from_state.pc row rotation) 0,
    c.core.rd_data row rotation (c.adapter.from_state.pc row rotation) 1,
    0,
    0
  ]
:= by
  simp [
    Valid_Rv32JalrCoreAir_4.rd_data,
    Valid_Rv32JalrCoreAir_4.least_sig_limb,
    Valid_Rv32JalrCoreAir_4.composed
  ]
