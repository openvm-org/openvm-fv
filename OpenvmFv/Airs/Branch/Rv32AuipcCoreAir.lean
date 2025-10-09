import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air
import OpenvmFv.Airs.Alu.AdapterAirContext

set_option linter.unusedVariables false

#define_subair "Rv32AuipcCoreAir" using "openvm_encapsulation" where
  Column["is_valid"]
  Column["imm_limbs_0"]
  Column["imm_limbs_1"]
  Column["imm_limbs_2"]
  Column["pc_limbs_0"]
  Column["pc_limbs_1"]
  Column["rd_data_0"]
  Column["rd_data_1"]
  Column["rd_data_2"]
  Column["rd_data_3"]

def Valid_Rv32AuipcCoreAir.intermed_val
  [Field F]
  (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
: F :=
  c.rd_data_0 row rotation +
  (
    c.pc_limbs_0 row rotation * 256 +
    c.pc_limbs_1 row rotation * 65536
  )

@[openvm_encapsulation]
lemma Rv32AuipcCoreAir.is_valid_def
  [Field F]
  (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
:
  c.rd_data_0 row rotation +
  (
    c.pc_limbs_0 row rotation * 256 +
    c.pc_limbs_1 row rotation * 65536
  ) =
  c.intermed_val row rotation
:= rfl

def Valid_Rv32AuipcCoreAir.pc_msl
  [Field F]
  (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
  (from_pc : F)
: F :=
  (from_pc - c.intermed_val row rotation) * 2013265801

def Valid_Rv32AuipcCoreAir.pc_limbs
  [Field F]
  (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
  (from_pc : F)
: Fin 4 → F :=
  λ idx => match idx with
    | 0 => c.rd_data_0 row rotation
    | 1 => c.pc_limbs_0 row rotation
    | 2 => c.pc_limbs_1 row rotation
    | 3 => c.pc_msl row rotation from_pc

def Valid_Rv32AuipcCoreAir.carry_divide
  [Field F]
  (c : Valid_Rv32AuipcCoreAir F)
: F := 2005401601

def Valid_Rv32AuipcCoreAir.carry
  [Field F]
  (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
  (from_pc : F)
: Fin 4 → F :=
  λ idx => match idx with
    | 0 => 0
    | 1 =>
      c.carry_divide * (
        c.pc_limbs row rotation from_pc 1 +
        c.imm_limbs_0 row rotation -
        c.rd_data_1 row rotation +
        c.carry row rotation from_pc 0
      )
    | 2 =>
      c.carry_divide * (
        c.pc_limbs row rotation from_pc 2 +
        c.imm_limbs_1 row rotation -
        c.rd_data_2 row rotation +
        c.carry row rotation from_pc 1
      )
    | 3 => c.carry_divide * (
        c.pc_limbs row rotation from_pc 3 +
        c.imm_limbs_2 row rotation -
        c.rd_data_3 row rotation +
        c.carry row rotation from_pc 2
      )

def Valid_Rv32AuipcCoreAir.imm
  [Field F]
  (c : Valid_Rv32AuipcCoreAir F) (row rotation : ℕ)
: F :=
  c.imm_limbs_0 row rotation +
  c.imm_limbs_1 row rotation * 256 +
  c.imm_limbs_2 row rotation * 65536

@[openvm_encapsulation]
lemma Rv32AuipcCoreAir.imm_def
  [Field F]
  (c : Valid_Rv32AuipcCoreAir F) (row rotation : ℕ)
:
  c.imm_limbs_0 row rotation +
  c.imm_limbs_1 row rotation * 256 +
  c.imm_limbs_2 row rotation * 65536 =
  c.imm row rotation
:= rfl


-- def Valid_Rv32AuipcCoreAir.cmp_eq
--   [Field F]
--   (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
-- : F :=
--   c.cmp_result row rotation * c.opcode_beq_flag row rotation +
--   (1 - c.cmp_result row rotation) * c.opcode_bne_flag row rotation

-- @[openvm_encapsulation]
-- lemma Rv32AuipcCoreAir.cmp_eq_def
--   [Field F]
--   (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
-- :
--   c.cmp_result row rotation * c.opcode_beq_flag row rotation +
--   (1 - c.cmp_result row rotation) * c.opcode_bne_flag row rotation =
--   c.cmp_eq row rotation
-- := rfl

-- def Valid_Rv32AuipcCoreAir.sum
--   [Field F]
--   (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
-- : F :=
--   ((((c.cmp_eq row rotation +
--   (c.a_0 row rotation - c.b_0 row rotation) * c.diff_inv_marker_0 row rotation) +
--   (c.a_1 row rotation - c.b_1 row rotation) * c.diff_inv_marker_1 row rotation) +
--   (c.a_2 row rotation - c.b_2 row rotation) * c.diff_inv_marker_2 row rotation) +
--   (c.a_3 row rotation - c.b_3 row rotation) * c.diff_inv_marker_3 row rotation)

-- @[openvm_encapsulation]
-- lemma Rv32AuipcCoreAir.sum_def
--   [Field F]
--   (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
-- :
--   ((((c.cmp_eq row rotation +
--   (c.a_0 row rotation - c.b_0 row rotation) * c.diff_inv_marker_0 row rotation) +
--   (c.a_1 row rotation - c.b_1 row rotation) * c.diff_inv_marker_1 row rotation) +
--   (c.a_2 row rotation - c.b_2 row rotation) * c.diff_inv_marker_2 row rotation) +
--   (c.a_3 row rotation - c.b_3 row rotation) * c.diff_inv_marker_3 row rotation) =
--   c.sum row rotation
-- := rfl

-- def Valid_Rv32AuipcCoreAir.expected_opcode
--   [Field F]
--   (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
-- : F :=
--   c.opcode_bne_flag row rotation +
--   544

-- @[openvm_encapsulation]
-- lemma Rv32AuipcCoreAir.expected_opcode_def
--   [Field F]
--   (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
-- :
--   c.opcode_bne_flag row rotation +
--   544 =
--   c.expected_opcode row rotation
-- := rfl

-- def Valid_Rv32AuipcCoreAir.pc_step
--   [Field F]
--   (c : Valid_Rv32AuipcCoreAir F)
-- : F :=
--   4

-- def Valid_Rv32AuipcCoreAir.to_pc
--   [Field F]
--   (c : Valid_Rv32AuipcCoreAir F) (row rotation: ℕ)
--   (from_pc : F)
-- : F :=
--   from_pc +
--   c.cmp_result row rotation * c.imm row rotation +
--   (1 - c.cmp_result row rotation) * c.pc_step
