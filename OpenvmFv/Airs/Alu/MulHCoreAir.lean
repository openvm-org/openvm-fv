import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air
import OpenvmFv.Airs.Alu.AdapterAirContext

set_option linter.unusedVariables false

#define_subair "MulHCoreAir_4_8" using "openvm_encapsulation" where
  Column["a_0"]
  Column["a_1"]
  Column["a_2"]
  Column["a_3"]
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  Column["c_0"]
  Column["c_1"]
  Column["c_2"]
  Column["c_3"]
  Column["a_mul_0"]
  Column["a_mul_1"]
  Column["a_mul_2"]
  Column["a_mul_3"]
  Column["b_ext"]
  Column["c_ext"]
  Column["opcode_mulh_flag"]
  Column["opcode_mulhsu_flag"]
  Column["opcode_mulhu_flag"]

def Valid_MulHCoreAir_4_8.is_valid
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.opcode_mulh_flag row rotation +
  c.opcode_mulhsu_flag row rotation +
  c.opcode_mulhu_flag row rotation

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.is_valid_def
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: c.opcode_mulh_flag row rotation + c.opcode_mulhsu_flag row rotation + c.opcode_mulhu_flag row rotation =
  c.is_valid row rotation
:= by
  rfl

def Valid_MulHCoreAir_4_8.carry_divide
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
: F := 2005401601

mutual
  def Valid_MulHCoreAir_4_8.carry_mul
    [Field F]
    (c : Valid_MulHCoreAir_4_8 F) (row rotation : ℕ)
  : Fin 4 → F :=
    λ i => match i with
      | 0 => c.carry_divide * (c.expected_limb_mul row rotation 0 - c.a_mul_0 row rotation)
      | 1 => c.carry_divide * (c.expected_limb_mul row rotation 1 - c.a_mul_1 row rotation)
      | 2 => c.carry_divide * (c.expected_limb_mul row rotation 2 - c.a_mul_2 row rotation)
      | 3 => c.carry_divide * (c.expected_limb_mul row rotation 3 - c.a_mul_3 row rotation)

  -- So named because the name expected_limb is used in two different local definitions in the rust
  def Valid_MulHCoreAir_4_8.expected_limb_mul
    [Field F]
    (c : Valid_MulHCoreAir_4_8 F) (row rotation : ℕ)
  : Fin 4 → F :=
    λ i => match i with
      | 0 => 0 + (0 + c.b_0 row rotation * c.c_0 row rotation)
      | 1 => c.carry_mul row rotation 0 + (0 + c.b_0 row rotation * c.c_1 row rotation + c.b_1 row rotation * c.c_0 row rotation)
      | 2 => c.carry_mul row rotation 1 + (0 + c.b_0 row rotation * c.c_2 row rotation + c.b_1 row rotation * c.c_1 row rotation + c.b_2 row rotation * c.c_0 row rotation)
      | 3 => c.carry_mul row rotation 2 + (0 + c.b_0 row rotation * c.c_3 row rotation + c.b_1 row rotation * c.c_2 row rotation + c.b_2 row rotation * c.c_1 row rotation + c.b_3 row rotation * c.c_0 row rotation)
end

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.carry_mul_0
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * ((c.b_0 row rotation * c.c_0 row rotation) - c.a_mul_0 row rotation) =
  c.carry_mul row rotation 0
:= by
  simp [
    Valid_MulHCoreAir_4_8.carry_mul.eq_def,
    Valid_MulHCoreAir_4_8.carry_divide.eq_def,
    Valid_MulHCoreAir_4_8.expected_limb_mul.eq_def
  ]

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.carry_mul_1
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * (c.carry_mul row rotation 0 + (c.b_0 row rotation * c.c_1 row rotation + c.b_1 row rotation * c.c_0 row rotation) - c.a_mul_1 row rotation) =
  c.carry_mul row rotation 1
:= by
  simp [
    Valid_MulHCoreAir_4_8.carry_mul.eq_def,
    Valid_MulHCoreAir_4_8.carry_divide.eq_def,
    Valid_MulHCoreAir_4_8.expected_limb_mul.eq_def
  ]

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.carry_mul_2
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * (c.carry_mul row rotation 1 + (c.b_0 row rotation * c.c_2 row rotation + c.b_1 row rotation * c.c_1 row rotation + c.b_2 row rotation * c.c_0 row rotation) - c.a_mul_2 row rotation) =
  c.carry_mul row rotation 2
:= by
  simp [
    Valid_MulHCoreAir_4_8.carry_mul.eq_def,
    Valid_MulHCoreAir_4_8.carry_divide.eq_def,
    Valid_MulHCoreAir_4_8.expected_limb_mul.eq_def
  ]

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.carry_mul_3
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * (c.carry_mul row rotation 2 + (c.b_0 row rotation * c.c_3 row rotation + c.b_1 row rotation * c.c_2 row rotation + c.b_2 row rotation * c.c_1 row rotation + c.b_3 row rotation * c.c_0 row rotation) - c.a_mul_3 row rotation) =
  c.carry_mul row rotation 3
:= by
  simp [
    Valid_MulHCoreAir_4_8.carry_mul.eq_def,
    Valid_MulHCoreAir_4_8.carry_divide.eq_def,
    Valid_MulHCoreAir_4_8.expected_limb_mul.eq_def
  ]

mutual
  def Valid_MulHCoreAir_4_8.carry
    [Field F]
    (c : Valid_MulHCoreAir_4_8 F) (row rotation : ℕ)
  : Fin 4 → F :=
    λ i => match i with
      | 0 => c.carry_divide * (c.expected_limb row rotation 0 - c.a_0 row rotation)
      | 1 => c.carry_divide * (c.expected_limb row rotation 1 - c.a_1 row rotation)
      | 2 => c.carry_divide * (c.expected_limb row rotation 2 - c.a_2 row rotation)
      | 3 => c.carry_divide * (c.expected_limb row rotation 3 - c.a_3 row rotation)

  def Valid_MulHCoreAir_4_8.expected_limb
    [Field F]
    (c : Valid_MulHCoreAir_4_8 F) (row rotation : ℕ)
  : Fin 4 → F :=
    λ i => match i with
      | 0 =>
        c.carry_mul row rotation 3 +
        c.b_1 row rotation * c.c_3 row rotation +
        c.b_2 row rotation * c.c_2 row rotation +
        c.b_3 row rotation * c.c_1 row rotation +
        (c.b_0 row rotation * c.c_ext row rotation) + (c.c_0 row rotation * c.b_ext row rotation)
      | 1 =>
        c.carry row rotation 0 +
        c.b_2 row rotation * c.c_2 row rotation +
        c.b_3 row rotation * c.c_1 row rotation +
        (c.b_0 row rotation * c.c_ext row rotation) + (c.c_0 row rotation * c.b_ext row rotation) +
        (c.b_1 row rotation * c.c_ext row rotation) + (c.c_1 row rotation * c.b_ext row rotation)
      | 2 =>
        c.carry row rotation 1 +
        c.b_3 row rotation * c.c_1 row rotation +
        (c.b_0 row rotation * c.c_ext row rotation) + (c.c_0 row rotation * c.b_ext row rotation) +
        (c.b_1 row rotation * c.c_ext row rotation) + (c.c_1 row rotation * c.b_ext row rotation) +
        (c.b_2 row rotation * c.c_ext row rotation) + (c.c_2 row rotation * c.b_ext row rotation)
      | 3 =>
        c.carry row rotation 2 +
        (c.b_0 row rotation * c.c_ext row rotation) + (c.c_0 row rotation * c.b_ext row rotation) +
        (c.b_1 row rotation * c.c_ext row rotation) + (c.c_1 row rotation * c.b_ext row rotation) +
        (c.b_2 row rotation * c.c_ext row rotation) + (c.c_2 row rotation * c.b_ext row rotation) +
        (c.b_3 row rotation * c.c_ext row rotation) + (c.c_3 row rotation * c.b_ext row rotation)
end

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.carry_0
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * (
    c.carry_mul row rotation 3 +
    c.b_1 row rotation * c.c_3 row rotation +
    c.b_2 row rotation * c.c_2 row rotation +
    c.b_3 row rotation * c.c_1 row rotation +
    (c.b_0 row rotation * c.c_ext row rotation) + (c.c_0 row rotation * c.b_ext row rotation) -
    c.a_0 row rotation
  ) =
  c.carry row rotation 0
:= by
  simp [
    Valid_MulHCoreAir_4_8.carry.eq_def,
    Valid_MulHCoreAir_4_8.carry_divide.eq_def,
    Valid_MulHCoreAir_4_8.expected_limb.eq_def
  ]

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.carry_1
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * (
    c.carry row rotation 0 +
    c.b_2 row rotation * c.c_2 row rotation +
    c.b_3 row rotation * c.c_1 row rotation +
    (c.b_0 row rotation * c.c_ext row rotation) + (c.c_0 row rotation * c.b_ext row rotation) +
    (c.b_1 row rotation * c.c_ext row rotation) + (c.c_1 row rotation * c.b_ext row rotation)
    - c.a_1 row rotation
  ) =
  c.carry row rotation 1
:= by
  simp [
    Valid_MulHCoreAir_4_8.carry.eq_def,
    Valid_MulHCoreAir_4_8.carry_divide.eq_def,
    Valid_MulHCoreAir_4_8.expected_limb.eq_def
  ]

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.carry_2
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * (
    c.carry row rotation 1 +
    c.b_3 row rotation * c.c_1 row rotation +
    (c.b_0 row rotation * c.c_ext row rotation) + (c.c_0 row rotation * c.b_ext row rotation) +
    (c.b_1 row rotation * c.c_ext row rotation) + (c.c_1 row rotation * c.b_ext row rotation) +
    (c.b_2 row rotation * c.c_ext row rotation) + (c.c_2 row rotation * c.b_ext row rotation)
    - c.a_2 row rotation
  ) =
  c.carry row rotation 2
:= by
  simp [
    Valid_MulHCoreAir_4_8.carry.eq_def,
    Valid_MulHCoreAir_4_8.carry_divide.eq_def,
    Valid_MulHCoreAir_4_8.expected_limb.eq_def
  ]

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.carry_3
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * (
    c.carry row rotation 2 +
    (c.b_0 row rotation * c.c_ext row rotation) + (c.c_0 row rotation * c.b_ext row rotation) +
    (c.b_1 row rotation * c.c_ext row rotation) + (c.c_1 row rotation * c.b_ext row rotation) +
    (c.b_2 row rotation * c.c_ext row rotation) + (c.c_2 row rotation * c.b_ext row rotation) +
    (c.b_3 row rotation * c.c_ext row rotation) + (c.c_3 row rotation * c.b_ext row rotation)
    - c.a_3 row rotation
  ) =
  c.carry row rotation 3
:= by
  simp [
    Valid_MulHCoreAir_4_8.carry.eq_def,
    Valid_MulHCoreAir_4_8.carry_divide.eq_def,
    Valid_MulHCoreAir_4_8.expected_limb.eq_def
  ]

def Valid_MulHCoreAir_4_8.sign_mask
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
: F := 128

def Valid_MulHCoreAir_4_8.ext_inv
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
: F := 465814468 --255⁻¹

def Valid_MulHCoreAir_4_8.b_sign
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.b_ext row rotation * c.ext_inv

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.b_sign_def
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: c.b_ext row rotation * 465814468 =
  c.b_sign row rotation
:= rfl

def Valid_MulHCoreAir_4_8.c_sign
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.c_ext row rotation * c.ext_inv

@[openvm_encapsulation]
lemma MulHCoreAir_4_8.c_sign_def
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation : ℕ)
: c.c_ext row rotation * 465814468 =
  c.c_sign row rotation
:= rfl

def Valid_MulHCoreAir_4_8.class_offset
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
: F :=
  593

def Valid_MulHCoreAir_4_8.ctx
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
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
      | 0 => c.a_0 row rotation
      | 1 => c.a_1 row rotation
      | 2 => c.a_2 row rotation
      | 3 => c.a_3 row rotation
    (
      MinimalInstruction.mk
        (c.is_valid row rotation) --is_valid
        (
          c.class_offset + --opcode
          (
            c.opcode_mulhsu_flag row rotation * 1 +
            c.opcode_mulhu_flag row rotation * 2
          )
        )
    )

@[openvm_encapsulation]
lemma Valid_MulHCoreAir_4_8.ctx.instruction.opcode_def
  [Field F]
  (c : Valid_MulHCoreAir_4_8 F)
  (row rotation: ℕ)
: 593 +
  (
    c.opcode_mulhsu_flag row rotation +
    c.opcode_mulhu_flag row rotation * 2
  ) =
  (c.ctx row rotation).instruction.opcode
:= by
  unfold Valid_MulHCoreAir_4_8.ctx Valid_MulHCoreAir_4_8.class_offset
  simp
