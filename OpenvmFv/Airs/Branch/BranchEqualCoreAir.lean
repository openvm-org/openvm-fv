import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air
import OpenvmFv.Airs.Alu.AdapterAirContext

set_option linter.unusedVariables false

#define_subair "BranchEqualCoreAir_4" using "openvm_encapsulation" where
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  Column["cmp_result"]
  Column["imm"]
  Column["opcode_beq_flag"]
  Column["opcode_bne_flag"]
  Column["diff_inv_marker_0"]
  Column["diff_inv_marker_1"]
  Column["diff_inv_marker_2"]
  Column["diff_inv_marker_3"]

def Valid_BranchEqualCoreAir_4.is_valid
  [Field F]
  (c : Valid_BranchEqualCoreAir_4 F) (row rotation: ℕ)
: F :=
  c.opcode_beq_flag row rotation +
  c.opcode_bne_flag row rotation

@[openvm_encapsulation]
lemma BranchEqualCoreAir_4.is_valid_def
  [Field F]
  (c : Valid_BranchEqualCoreAir_4 F) (row rotation: ℕ)
:
  c.opcode_beq_flag row rotation +
  c.opcode_bne_flag row rotation =
  c.is_valid row rotation
:= rfl

def Valid_BranchEqualCoreAir_4.cmp_eq
  [Field F]
  (c : Valid_BranchEqualCoreAir_4 F) (row rotation: ℕ)
: F :=
  c.cmp_result row rotation * c.opcode_beq_flag row rotation +
  (1 - c.cmp_result row rotation) * c.opcode_bne_flag row rotation

@[openvm_encapsulation]
lemma BranchEqualCoreAir_4.cmp_eq_def
  [Field F]
  (c : Valid_BranchEqualCoreAir_4 F) (row rotation: ℕ)
:
  c.cmp_result row rotation * c.opcode_beq_flag row rotation +
  (1 - c.cmp_result row rotation) * c.opcode_bne_flag row rotation =
  c.cmp_eq row rotation
:= rfl

def Valid_BranchEqualCoreAir_4.sum
  [Field F]
  (c : Valid_BranchEqualCoreAir_4 F) (row rotation: ℕ)
: F :=
  ((((c.cmp_eq row rotation +
  (c.a_0 row rotation - c.b_0 row rotation) * c.diff_inv_marker_0 row rotation) +
  (c.a_1 row rotation - c.b_1 row rotation) * c.diff_inv_marker_1 row rotation) +
  (c.a_2 row rotation - c.b_2 row rotation) * c.diff_inv_marker_2 row rotation) +
  (c.a_3 row rotation - c.b_3 row rotation) * c.diff_inv_marker_3 row rotation)

@[openvm_encapsulation]
lemma BranchEqualCoreAir_4.sum_def
  [Field F]
  (c : Valid_BranchEqualCoreAir_4 F) (row rotation: ℕ)
:
  ((((c.cmp_eq row rotation +
  (c.a_0 row rotation - c.b_0 row rotation) * c.diff_inv_marker_0 row rotation) +
  (c.a_1 row rotation - c.b_1 row rotation) * c.diff_inv_marker_1 row rotation) +
  (c.a_2 row rotation - c.b_2 row rotation) * c.diff_inv_marker_2 row rotation) +
  (c.a_3 row rotation - c.b_3 row rotation) * c.diff_inv_marker_3 row rotation) =
  c.sum row rotation
:= rfl

def Valid_BranchEqualCoreAir_4.expected_opcode
  [Field F]
  (c : Valid_BranchEqualCoreAir_4 F) (row rotation: ℕ)
: F :=
  c.opcode_bne_flag row rotation +
  544

@[openvm_encapsulation]
lemma BranchEqualCoreAir_4.expected_opcode_def
  [Field F]
  (c : Valid_BranchEqualCoreAir_4 F) (row rotation: ℕ)
:
  c.opcode_bne_flag row rotation +
  544 =
  c.expected_opcode row rotation
:= rfl

def Valid_BranchEqualCoreAir_4.pc_step
  [Field F]
  (c : Valid_BranchEqualCoreAir_4 F)
: F :=
  4

def Valid_BranchEqualCoreAir_4.to_pc
  [Field F]
  (c : Valid_BranchEqualCoreAir_4 F) (row rotation: ℕ)
  (from_pc : F)
: F :=
  from_pc +
  c.cmp_result row rotation * c.imm row rotation +
  (1 - c.cmp_result row rotation) * c.pc_step
