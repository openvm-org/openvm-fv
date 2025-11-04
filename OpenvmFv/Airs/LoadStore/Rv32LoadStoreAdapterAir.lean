import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.ExecutionState
import OpenvmFv.Airs.Memory

set_option linter.unusedVariables false

#define_subair "Rv32LoadStoreAdapterAir" using "openvm_encapsulation" where
  SubAir["from_state": "ExecutionState" width := 2]
  Column["rs1_ptr"]
  Column["rs1_data_0"]
  Column["rs1_data_1"]
  Column["rs1_data_2"]
  Column["rs1_data_3"]
  SubAir["rs1_aux_cols": "MemoryReadAuxCols" width := 3]
  Column["rd_rs2_ptr"]
  SubAir["read_data_aux": "MemoryReadAuxCols" width := 3]
  Column["imm"]
  Column["imm_sign"]
  Column["mem_ptr_limbs_0"]
  Column["mem_ptr_limbs_1"]
  Column["mem_as"]
  SubAir["write_base_aux": "MemoryBaseAuxCols" width := 3]
  Column["needs_write"]

def Valid_Rv32LoadStoreAdapterAir.limbs_01
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
: F :=
  c.rs1_data_0 row rotation +
  c.rs1_data_1 row rotation * 256

@[openvm_encapsulation]
lemma Rv32LoadStoreAdapterAir.limbs_01_def
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
:
  c.rs1_data_0 row rotation +
  c.rs1_data_1 row rotation * 256 =
  c.limbs_01 row rotation
:= rfl

def Valid_Rv32LoadStoreAdapterAir.limbs_23
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
: F :=
  c.rs1_data_2 row rotation +
  c.rs1_data_3 row rotation * 256

@[openvm_encapsulation]
lemma Rv32LoadStoreAdapterAir.limbs_23_def
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
:
  c.rs1_data_2 row rotation +
  c.rs1_data_3 row rotation * 256 =
  c.limbs_23 row rotation
:= rfl

def Valid_Rv32LoadStoreAdapterAir.inv
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
: F :=
  2013235201

def Valid_Rv32LoadStoreAdapterAir.carry
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
: F :=
  (c.limbs_01 row rotation +
  c.imm row rotation -
  c.mem_ptr_limbs_0 row rotation) *
  c.inv

@[openvm_encapsulation]
lemma Rv32LoadStoreAdapterAir.carry_def
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
:
  (c.limbs_01 row rotation +
  c.imm row rotation -
  c.mem_ptr_limbs_0 row rotation) *
  2013235201 =
  c.carry row rotation
:= rfl

def Valid_Rv32LoadStoreAdapterAir.imm_extended_limb
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
: F :=
  c.imm_sign row rotation * 65535

@[openvm_encapsulation]
lemma Rv32LoadStoreAdapterAir.imm_extended_limb_def
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
:
  c.imm_sign row rotation * 65535 =
  c.imm_extended_limb row rotation
:= rfl

def Valid_Rv32LoadStoreAdapterAir.carry'
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
: F :=
  (c.limbs_23 row rotation +
  c.imm_extended_limb row rotation +
  c.carry row rotation -
  c.mem_ptr_limbs_1 row rotation) *
  c.inv

@[openvm_encapsulation]
lemma Rv32LoadStoreAdapterAir.carry'_def
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
:
  (c.limbs_23 row rotation +
  c.imm_extended_limb row rotation +
  c.carry row rotation -
  c.mem_ptr_limbs_1 row rotation) *
  2013235201 =
  c.carry' row rotation
:= rfl

def Valid_Rv32LoadStoreAdapterAir.mem_ptr
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
: F :=
  c.mem_ptr_limbs_0 row rotation +
  c.mem_ptr_limbs_1 row rotation * 65536

@[openvm_encapsulation]
lemma Rv32LoadStoreAdapterAir.mem_ptr_def
  [Field F]
  (c : Valid_Rv32LoadStoreAdapterAir F)
  (row rotation : ℕ)
:
  c.mem_ptr_limbs_0 row rotation +
  c.mem_ptr_limbs_1 row rotation * 65536 =
  c.mem_ptr row rotation
:= rfl
