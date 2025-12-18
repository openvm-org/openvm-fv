import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.LoadStore.LoadSignExtendCoreAir
import OpenvmFv.Airs.LoadStore.Rv32LoadStoreAdapterAir

set_option linter.unusedVariables false

#define_air "VmAirWrapper_load_sign_extend" using "openvm_encapsulation" where
  MainSubAir["adapter": "Rv32LoadStoreAdapterAir" width := 23]
  MainSubAir["core": "LoadSignExtendCoreAir_4" width := 13]

def Valid_VmAirWrapper_load_sign_extend.is_store
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
: F :=
  c.core.is_valid row rotation -
  c.core.is_load row rotation

@[openvm_encapsulation]
lemma VmAirWrapper_load_sign_extend.is_store_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
:
  c.core.is_valid row rotation -
  c.core.is_load row rotation =
  c.is_store row rotation
:= rfl

def Valid_VmAirWrapper_load_sign_extend.shift_amount
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
: F :=
  c.core.load_shift_amount row rotation +
  c.core.store_shift_amount row rotation

@[openvm_encapsulation]
lemma VmAirWrapper_load_sign_extend.shift_amount_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
:
  c.core.load_shift_amount row rotation +
  c.core.store_shift_amount row rotation =
  c.shift_amount row rotation
:= rfl

def Valid_VmAirWrapper_load_sign_extend.read_as
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
: F :=
  c.core.is_load row rotation * c.adapter.mem_as row rotation +
  (1 - c.core.is_load row rotation)

@[openvm_encapsulation]
lemma VmAirWrapper_load_sign_extend.read_as
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
:
  c.core.is_valid row rotation * c.adapter.mem_as row rotation +
  (1 - c.core.is_valid row rotation) =
  c.read_as row rotation
:= rfl

def Valid_VmAirWrapper_load_sign_extend.read_ptr
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
: F :=
  c.core.is_load row rotation * c.adapter.mem_ptr row rotation +
  (1 - c.core.is_load row rotation) * c.adapter.rd_rs2_ptr row rotation -
  c.core.load_shift_amount row rotation

@[openvm_encapsulation]
lemma VmAirWrapper_load_sign_extend.read_ptr_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
:
  c.core.is_valid row rotation * c.adapter.mem_ptr row rotation +
  (1 - c.core.is_valid row rotation) * c.adapter.rd_rs2_ptr row rotation -
  c.core.load_shift_amount row rotation =
  c.read_ptr row rotation
:= rfl

def Valid_VmAirWrapper_load_sign_extend.write_as
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
: F :=
  c.core.is_load row rotation +
  (1 - c.core.is_load row rotation) * c.adapter.mem_as row rotation

@[openvm_encapsulation]
lemma VmAirWrapper_load_sign_extend.write_as_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
:
  c.core.is_valid row rotation +
  (1 - c.core.is_valid row rotation) * c.adapter.mem_as row rotation =
  c.write_as row rotation
:= rfl

def Valid_VmAirWrapper_load_sign_extend.write_ptr
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
: F :=
  c.core.is_load row rotation * c.adapter.rd_rs2_ptr row rotation +
  (1 - c.core.is_load row rotation) * c.adapter.mem_ptr row rotation -
  c.core.store_shift_amount row rotation

@[openvm_encapsulation]
lemma VmAirWrapper_load_sign_extend.write_ptr_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
:
  c.core.is_valid row rotation * c.adapter.rd_rs2_ptr row rotation +
  (1 - c.core.is_valid row rotation) * c.adapter.mem_ptr row rotation =
  c.write_ptr row rotation
:= by
  simp [
    Valid_VmAirWrapper_load_sign_extend.write_ptr,
    Valid_LoadSignExtendCoreAir_4.store_shift_amount,
    Valid_LoadSignExtendCoreAir_4.is_load
  ]

def Valid_VmAirWrapper_load_sign_extend.to_pc
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
: F :=
  c.adapter.from_state.pc row rotation + 4

@[openvm_encapsulation]
lemma VmAirWrapper_load_sign_extend.to_pc_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
:
  c.adapter.from_state.pc row rotation + 4 =
  c.to_pc row rotation
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_load_sign_extend.write_def
  [Field F] [Field ExtF]
  (c : Valid_VmAirWrapper_load_sign_extend F ExtF)
  (row rotation : ℕ)
:
  [
    c.write_as row rotation,
    c.write_ptr row rotation,
    (c.core.opcode_loadh_flag row rotation + c.core.opcode_loadb_flag0 row rotation) *
    c.core.shifted_read_data_0 row rotation +
    c.core.opcode_loadb_flag1 row rotation * c.core.shifted_read_data_1 row rotation,
    c.core.shifted_read_data_1 row rotation * c.core.opcode_loadh_flag row rotation +
    (c.core.opcode_loadb_flag0 row rotation + c.core.opcode_loadb_flag1 row rotation) * c.core.limb_mask row rotation,
    c.core.limb_mask row rotation,
    c.core.limb_mask row rotation,
    c.adapter.from_state.timestamp row rotation + 2
  ] =
  [
    c.write_as row rotation,
    c.write_ptr row rotation,
    c.core.write_data row rotation 0,
    c.core.write_data row rotation 1,
    c.core.write_data row rotation 2,
    c.core.write_data row rotation 3,
    c.adapter.from_state.timestamp row rotation + 2
  ]
:= by
  simp [
    Valid_LoadSignExtendCoreAir_4.write_data
  ]
