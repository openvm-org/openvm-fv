import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air
import OpenvmFv.Airs.Alu.AdapterAirContext

set_option linter.unusedVariables false

#define_subair "BranchLessThanCoreAir_4_8" using "openvm_encapsulation" where
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
  Column["opcode_blt_flag"]
  Column["opcode_bltu_flag"]
  Column["opcode_bge_flag"]
  Column["opcode_bgeu_flag"]
  Column["a_msb_f"]
  Column["b_msb_f"]
  Column["cmp_lt"]
  Column["diff_marker_0"]
  Column["diff_marker_1"]
  Column["diff_marker_2"]
  Column["diff_marker_3"]
  Column["diff_val"]

def Valid_BranchLessThanCoreAir_4_8.is_valid
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
: F :=
  c.opcode_blt_flag row rotation +
  c.opcode_bltu_flag row rotation +
  c.opcode_bge_flag row rotation +
  c.opcode_bgeu_flag row rotation

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.is_valid_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  c.opcode_blt_flag row rotation +
  c.opcode_bltu_flag row rotation +
  c.opcode_bge_flag row rotation +
  c.opcode_bgeu_flag row rotation =
  c.is_valid row rotation
:= rfl

def Valid_BranchLessThanCoreAir_4_8.lt
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
: F :=
  c.opcode_blt_flag row rotation +
  c.opcode_bltu_flag row rotation

def Valid_BranchLessThanCoreAir_4_8.ge
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
: F :=
  c.opcode_bge_flag row rotation +
  c.opcode_bgeu_flag row rotation

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.cmp_lt_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  c.cmp_result row rotation * (
    c.opcode_blt_flag row rotation +
    c.opcode_bltu_flag row rotation
  ) +
  (1 - c.cmp_result row rotation) * (
    c.opcode_bge_flag row rotation +
    c.opcode_bgeu_flag row rotation
  ) =
  c.cmp_result row rotation * c.lt row rotation +
  (1 - c.cmp_result row rotation) * c.ge row rotation
:= rfl

def Valid_BranchLessThanCoreAir_4_8.a_diff
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
: F :=
  c.a_3 row rotation - c.a_msb_f row rotation

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.a_diff_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  c.a_3 row rotation - c.a_msb_f row rotation =
  c.a_diff row rotation
:= rfl

def Valid_BranchLessThanCoreAir_4_8.b_diff
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
: F :=
  c.b_3 row rotation - c.b_msb_f row rotation

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.b_diff_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  c.b_3 row rotation - c.b_msb_f row rotation =
  c.b_diff row rotation
:= rfl

def Valid_BranchLessThanCoreAir_4_8.diff
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
: Fin 4 → F :=
  λ idx => match idx with
    | 0 => (c.b_0 row rotation - c.a_0 row rotation) * (2 * c.cmp_lt row rotation - 1)
    | 1 => (c.b_1 row rotation - c.a_1 row rotation) * (2 * c.cmp_lt row rotation - 1)
    | 2 => (c.b_2 row rotation - c.a_2 row rotation) * (2 * c.cmp_lt row rotation - 1)
    | 3 => (c.b_msb_f row rotation - c.a_msb_f row rotation) * (2 * c.cmp_lt row rotation - 1)

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.diff_0_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  (c.b_0 row rotation - c.a_0 row rotation) * (2 * c.cmp_lt row rotation - 1) =
  c.diff row rotation 0
:= rfl

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.diff_1_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  (c.b_1 row rotation - c.a_1 row rotation) * (2 * c.cmp_lt row rotation - 1) =
  c.diff row rotation 1
:= rfl

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.diff_2_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  (c.b_2 row rotation - c.a_2 row rotation) * (2 * c.cmp_lt row rotation - 1) =
  c.diff row rotation 2
:= rfl

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.diff_3_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  (c.b_msb_f row rotation - c.a_msb_f row rotation) * (2 * c.cmp_lt row rotation - 1) =
  c.diff row rotation 3
:= rfl

def Valid_BranchLessThanCoreAir_4_8.prefix_sum
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
: Fin 4 → F :=
  λ idx => match idx with
    | 0 => c.diff_marker_3 row rotation + c.diff_marker_2 row rotation + c.diff_marker_1 row rotation + c.diff_marker_0 row rotation
    | 1 => c.diff_marker_3 row rotation + c.diff_marker_2 row rotation + c.diff_marker_1 row rotation
    | 2 => c.diff_marker_3 row rotation + c.diff_marker_2 row rotation
    | 3 => c.diff_marker_3 row rotation

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.prefix_sum_3_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  c.diff_marker_3 row rotation =
  c.prefix_sum row rotation 3
:= rfl

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.prefix_sum_2_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  c.prefix_sum row rotation 3 + c.diff_marker_2 row rotation =
  c.prefix_sum row rotation 2
:= rfl

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.prefix_sum_1_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  c.prefix_sum row rotation 2 + c.diff_marker_1 row rotation =
  c.prefix_sum row rotation 1
:= rfl

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.prefix_sum_0_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  c.prefix_sum row rotation 1 + c.diff_marker_0 row rotation =
  c.prefix_sum row rotation 0
:= rfl

def Valid_BranchLessThanCoreAir_4_8.expected_opcode
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
: F :=
  c.opcode_bltu_flag row rotation +
  c.opcode_bge_flag row rotation * 2 +
  c.opcode_bgeu_flag row rotation * 3 +
  549

@[openvm_encapsulation]
lemma BranchLessThanCoreAir_4_8.expected_opcode_def
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
:
  c.opcode_bltu_flag row rotation +
  c.opcode_bge_flag row rotation * 2 +
  c.opcode_bgeu_flag row rotation * 3 +
  549 =
  c.expected_opcode row rotation
:= rfl

def Valid_BranchLessThanCoreAir_4_8.pc_step
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F)
: F :=
  4

def Valid_BranchLessThanCoreAir_4_8.to_pc
  [Field F]
  (c : Valid_BranchLessThanCoreAir_4_8 F) (row rotation: ℕ)
  (from_pc : F)
: F :=
  from_pc +
  c.cmp_result row rotation * c.imm row rotation +
  (1 - c.cmp_result row rotation) * c.pc_step
