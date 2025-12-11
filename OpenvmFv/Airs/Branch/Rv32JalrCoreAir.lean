import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

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

-- def Valid_Rv32JalLuiCoreAir_4.is_valid
--   [Field F]
--   (c : Valid_Rv32JalLuiCoreAir_4 F) (row rotation : ℕ)
-- : F :=
--   c.is_lui row rotation +
--   c.is_jal row rotation

-- @[openvm_encapsulation]
-- lemma Rv32JalLuiCoreAir_4.is_valid_def
--   [Field F]
--   (c : Valid_Rv32JalLuiCoreAir_4 F) (row rotation : ℕ)
-- :
--   c.is_lui row rotation +
--   c.is_jal row rotation =
--   c.is_valid row rotation
-- := rfl

-- -- last_limb_bits = 30 - 8 * (4-1) = 30 - 24 = 6
-- -- additional_bits = 2^6 + 2^7

-- def Valid_Rv32JalLuiCoreAir_4.additional_bits
--   [Field F]
--   (c : Valid_Rv32JalLuiCoreAir_4 F)
-- : F :=
--   2^6 + 2^7

-- @[openvm_encapsulation]
-- lemma Rv32JalLuiCoreAir_4.additional_bits
--   [Field F]
--   (c : Valid_Rv32JalLuiCoreAir_4 F)
-- :
--   192 =
--   c.additional_bits
-- := by
--   unfold Valid_Rv32JalLuiCoreAir_4.additional_bits
--   grind

-- def Valid_Rv32JalLuiCoreAir_4.intermed_val
--   [Field F]
--   (c : Valid_Rv32JalLuiCoreAir_4 F) (row rotation : ℕ)
-- : F :=
--   c.rd_data_1 row rotation +
--   c.rd_data_2 row rotation * 256 +
--   c.rd_data_3 row rotation * 65536

-- @[openvm_encapsulation]
-- lemma Rv32JalLuiCoreAir_4.intermed_val_def
--   [Field F]
--   (c : Valid_Rv32JalLuiCoreAir_4 F) (row rotation : ℕ)
-- :
--   c.rd_data_1 row rotation +
--   c.rd_data_2 row rotation * 256 +
--   c.rd_data_3 row rotation * 65536 =
--   c.intermed_val row rotation
-- := rfl

-- def Valid_Rv32JalLuiCoreAir_4.intermed_val'
--   [Field F]
--   (c : Valid_Rv32JalLuiCoreAir_4 F) (row rotation : ℕ)
-- : F :=
--   c.rd_data_0 row rotation +
--   c.intermed_val row rotation * 256

-- @[openvm_encapsulation]
-- lemma Rv32JalLuiCoreAir_4.intermed_val'_def
--   [Field F]
--   (c : Valid_Rv32JalLuiCoreAir_4 F) (row rotation : ℕ)
-- :
--   c.rd_data_0 row rotation +
--   c.intermed_val row rotation * 256 =
--   c.intermed_val' row rotation
-- := rfl

-- def Valid_Rv32JalLuiCoreAir_4.expected_opcode
--   [Field F]
--   (c : Valid_Rv32JalLuiCoreAir_4 F) (row rotation : ℕ)
-- : F :=
--   560 +
--   c.is_lui row rotation

-- @[openvm_encapsulation]
-- lemma Rv32JalLuiCoreAir_4.expected_opcode_def
--   [Field F]
--   (c : Valid_Rv32JalLuiCoreAir_4 F) (row rotation : ℕ)
-- :
--   560 +
--   c.is_lui row rotation =
--   c.expected_opcode row rotation
-- := rfl
