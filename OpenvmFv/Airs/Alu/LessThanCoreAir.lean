import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air
import OpenvmFv.Airs.Alu.AdapterAirContext

set_option linter.unusedVariables false

#define_subair "LessThanCoreAir_4" using "openvm_encapsulation" where
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  Column["c_0"]
  Column["c_1"]
  Column["c_2"]
  Column["c_3"]
  Column["cmp_result"]
  Column["opcode_slt_flag"]
  Column["opcode_sltu_flag"]
  Column["b_msb_f"]
  Column["c_msb_f"]
  Column["diff_marker_0"]
  Column["diff_marker_1"]
  Column["diff_marker_2"]
  Column["diff_marker_3"]
  Column["diff_val"]

def Valid_LessThanCoreAir_4.is_valid
  [Field F]
  (c : Valid_LessThanCoreAir_4 F) (row rotation: ℕ)
: F :=
  c.opcode_slt_flag row rotation +
  c.opcode_sltu_flag row rotation

@[openvm_encapsulation]
lemma LessThanCoreAir_4.is_valid_def
  [Field F]
  (c : Valid_LessThanCoreAir_4 F) (row rotation: ℕ)
:
    c.opcode_slt_flag row rotation +
  c.opcode_sltu_flag row rotation =
  c.is_valid row rotation
:= rfl

def Valid_LessThanCoreAir_4.diff
  [Field F]
  (c : Valid_LessThanCoreAir_4 F) (row rotation: ℕ)
: Fin 4 → F :=
  λ i =>
    (
      match i with
        | 3 => c.c_msb_f row rotation - c.b_msb_f row rotation
        | 2 => c.c_2 row rotation - c.b_2 row rotation
        | 1 => c.c_1 row rotation - c.b_1 row rotation
        | 0 => c.c_0 row rotation - c.b_0 row rotation
    ) *
    (2 * c.cmp_result row rotation - 1)

@[openvm_encapsulation]
lemma LessThanCoreAir_4.diff_def_0
  [Field F]
  (c : Valid_LessThanCoreAir_4 F)
  (row rotation: ℕ)
: (c.c_0 row rotation - c.b_0 row rotation) * (2 * c.cmp_result row rotation - 1) =
  c.diff row rotation 0
:= rfl

@[openvm_encapsulation]
lemma LessThanCoreAir_4.diff_def_1
  [Field F]
  (c : Valid_LessThanCoreAir_4 F)
  (row rotation: ℕ)
: (c.c_1 row rotation - c.b_1 row rotation) * (2 * c.cmp_result row rotation - 1) =
  c.diff row rotation 1
:= rfl

@[openvm_encapsulation]
lemma LessThanCoreAir_4.diff_def_2
  [Field F]
  (c : Valid_LessThanCoreAir_4 F)
  (row rotation: ℕ)
: (c.c_2 row rotation - c.b_2 row rotation) * (2 * c.cmp_result row rotation - 1) =
  c.diff row rotation 2
:= rfl

@[openvm_encapsulation]
lemma LessThanCoreAir_4.diff_def_3
  [Field F]
  (c : Valid_LessThanCoreAir_4 F)
  (row rotation: ℕ)
: (c.c_msb_f row rotation - c.b_msb_f row rotation) * (2 * c.cmp_result row rotation - 1) =
  c.diff row rotation 3
:= rfl

def Valid_LessThanCoreAir_4.prefix_sum
  [Field F]
  (c : Valid_LessThanCoreAir_4 F) (row rotation: ℕ)
: Fin 4 → F :=
  λ i => match i with
    | 3 => c.diff_marker_3 row rotation
    | 2 => c.diff_marker_3 row rotation + c.diff_marker_2 row rotation
    | 1 => c.diff_marker_3 row rotation + c.diff_marker_2 row rotation + c.diff_marker_1 row rotation
    | 0 => c.diff_marker_3 row rotation + c.diff_marker_2 row rotation + c.diff_marker_1 row rotation + c.diff_marker_0 row rotation

@[openvm_encapsulation]
lemma LessThanCoreAir_4.prefix_sum_2_def
  [Field F]
  (c : Valid_LessThanCoreAir_4 F)
  (row rotation: ℕ)
: (c.diff_marker_3 row rotation + c.diff_marker_2 row rotation) =
  (c.prefix_sum row rotation 2)
:= rfl

@[openvm_encapsulation]
lemma LessThanCoreAir_4.prefix_sum_1_def
  [Field F]
  (c : Valid_LessThanCoreAir_4 F)
  (row rotation: ℕ)
: (c.prefix_sum row rotation 2 + c.diff_marker_1 row rotation) =
  (c.prefix_sum row rotation 1)
:= rfl

@[openvm_encapsulation]
lemma LessThanCoreAir_4.prefix_sum_0_def
  [Field F]
  (c : Valid_LessThanCoreAir_4 F)
  (row rotation: ℕ)
: (c.prefix_sum row rotation 1 + c.diff_marker_0 row rotation) =
  (c.prefix_sum row rotation 0)
:= rfl

def Valid_LessThanCoreAir_4.class_offset
  [Field F]
  (c : Valid_LessThanCoreAir_4 F)
: F :=
  520

def Valid_LessThanCoreAir_4.ctx
  [Field F]
  (c : Valid_LessThanCoreAir_4 F)
  (row rotation: ℕ)
: AdapterAirContext F :=
  AdapterAirContext.mk
    .none --to_pc
    λ x y => match x,y with -- reads
      | 0, 0 => c.b_0 row rotation
      | 0, 1 => c.b_1 row rotation
      | 0, 2 => c.b_2 row rotation
      | 0, 3 => c.b_3 row rotation
      | 1, 0 => c.c_0 row rotation
      | 1, 1 => c.c_1 row rotation
      | 1, 2 => c.c_2 row rotation
      | 1, 3 => c.c_3 row rotation
    λ x => match x with --writes
      | 0 => c.cmp_result row rotation
      | 1 => 0
      | 2 => 0
      | 3 => 0
    (
      MinimalInstruction.mk
        (c.is_valid row rotation) --is_valid
        (
          c.class_offset + --opcode
          (
            c.opcode_slt_flag row rotation * 0 +
            c.opcode_sltu_flag row rotation * 1
          )
        )
    )

@[openvm_encapsulation]
lemma LessThanCoreAir_4.ctx.instruction.opcode_def
  [Field F]
  (c : Valid_LessThanCoreAir_4 F)
  (row rotation: ℕ)
: 520 + c.opcode_sltu_flag row rotation =
  (c.ctx row rotation).instruction.opcode
:= by
  unfold Valid_LessThanCoreAir_4.ctx Valid_LessThanCoreAir_4.class_offset
  simp
