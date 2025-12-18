import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Fundamentals.BabyBear

set_option linter.unusedVariables false

#define_subair "Rv32JalrCoreAir_4" using "openvm_encapsulation" where
  Column["imm"]
  Column["rs1_data_0"]
  Column["rs1_data_1"]
  Column["rs1_data_2"]
  Column["rs1_data_3"]
  Column["rd_data_0"]
  Column["rd_data_1"]
  Column["rd_data_2"]
  Column["is_valid"]
  Column["to_pc_least_sig_bit"]
  Column["to_pc_limbs_0"]
  Column["to_pc_limbs_1"]
  Column["imm_sign"]

def Valid_Rv32JalrCoreAir_4.composed
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
: F :=
  c.rd_data_0 row rotation * 256 +
  c.rd_data_1 row rotation * 65536 +
  c.rd_data_2 row rotation * 16777216


def Valid_Rv32JalrCoreAir_4.least_sig_limb
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
  (from_pc : F)
: F :=
  from_pc + 4 - c.composed row rotation

def Valid_Rv32JalrCoreAir_4.rd_data
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
  (from_pc : F)
: Fin 4 → F :=
  λ idx => match idx with
    | 0 => c.least_sig_limb row rotation from_pc
    | 1 => c.rd_data_0 row rotation
    | 2 => c.rd_data_1 row rotation
    | 3 => c.rd_data_2 row rotation

def Valid_Rv32JalrCoreAir_4.rs1_limbs_01
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
: F :=
  c.rs1_data_0 row rotation +
  c.rs1_data_1 row rotation * 256

def Valid_Rv32JalrCoreAir_4.rs1_limbs_23
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
: F :=
  c.rs1_data_2 row rotation +
  c.rs1_data_3 row rotation * 256

-- 2^16 ⁻¹
def Valid_Rv32JalrCoreAir_4.inv
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F)
: F :=
  2013235201

def Valid_Rv32JalrCoreAir_4.carry
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
: F :=
  (c.rs1_limbs_01 row rotation +
  c.imm row rotation -
  c.to_pc_limbs_0 row rotation * 2 -
  c.to_pc_least_sig_bit row rotation) *
  c.inv

def Valid_Rv32JalrCoreAir_4.imm_extended_limb
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
: F :=
  c.imm_sign row rotation * 65535

def Valid_Rv32JalrCoreAir_4.carry'
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
: F :=
  (c.rs1_limbs_23 row rotation +
  c.imm_extended_limb row rotation +
  c.carry row rotation -
  c.to_pc_limbs_1 row rotation) *
  c.inv

def Valid_Rv32JalrCoreAir_4.to_pc
  [Field F]
  (c : Valid_Rv32JalrCoreAir_4 F) (row rotation : ℕ)
: F :=
  c.to_pc_limbs_0 row rotation * 2 +
  c.to_pc_limbs_1 row rotation * 65536

-- No need to fold expected opcode as it's constant
