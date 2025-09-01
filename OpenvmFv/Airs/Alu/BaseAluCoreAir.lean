import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

set_option linter.unusedVariables false

#define_subair "BaseAluCoreAir" using "openvm_encapsulation" where
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
  Column["opcode_add_flag"]
  Column["opcode_sub_flag"]
  Column["opcode_xor_flag"]
  Column["opcode_or_flag"]
  Column["opcode_and_flag"]

def Valid_BaseAluCoreAir.is_valid
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
: F :=
  c.opcode_add_flag row rotation +
  c.opcode_sub_flag row rotation +
  c.opcode_xor_flag row rotation +
  c.opcode_or_flag row rotation +
  c.opcode_and_flag row rotation

@[openvm_encapsulation]
lemma BaseAluCoreAir.is_valid_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  c.opcode_add_flag row rotation +
  c.opcode_sub_flag row rotation +
  c.opcode_xor_flag row rotation +
  c.opcode_or_flag row rotation +
  c.opcode_and_flag row rotation =
  c.is_valid row rotation
:= rfl

def Valid_BaseAluCoreAir.carry_divide
  [Field F]
  (c : Valid_BaseAluCoreAir F)
: F := 2005401601

def Valid_BaseAluCoreAir.carry_add_0
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
: F :=
  c.carry_divide *
  (c.b_0 row rotation + c.c_0 row rotation - c.a_0 row rotation)

@[openvm_encapsulation]
lemma BaseAluCoreAir.carry_add_0_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (2005401601: F) *
  (c.b_0 row rotation + c.c_0 row rotation - c.a_0 row rotation) =
  c.carry_add_0 row rotation
:= rfl

def Valid_BaseAluCoreAir.carry_add_1
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
: F :=
  c.carry_divide *
  (
    c.b_1 row rotation +
    c.c_1 row rotation -
    c.a_1 row rotation +
    c.carry_add_0 row rotation
  )

@[openvm_encapsulation]
lemma BaseAluCoreAir.carry_add_1_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (2005401601: F) *
  (c.b_1 row rotation + c.c_1 row rotation - c.a_1 row rotation + c.carry_add_0 row rotation) =
  c.carry_add_1 row rotation
:= rfl

def Valid_BaseAluCoreAir.carry_add_2
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
: F :=
  c.carry_divide *
  (
    c.b_2 row rotation +
    c.c_2 row rotation -
    c.a_2 row rotation +
    c.carry_add_1 row rotation
  )

@[openvm_encapsulation]
lemma BaseAluCoreAir.carry_add_2_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (2005401601: F) *
  (c.b_2 row rotation + c.c_2 row rotation - c.a_2 row rotation + c.carry_add_1 row rotation) =
  c.carry_add_2 row rotation
:= rfl

def Valid_BaseAluCoreAir.carry_add_3
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
: F :=
  c.carry_divide *
  (
    c.b_3 row rotation +
    c.c_3 row rotation -
    c.a_3 row rotation +
    c.carry_add_2 row rotation
  )

@[openvm_encapsulation]
lemma BaseAluCoreAir.carry_add_3_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (2005401601: F) *
  (c.b_3 row rotation + c.c_3 row rotation - c.a_3 row rotation + c.carry_add_2 row rotation) =
  c.carry_add_3 row rotation
:= rfl

def Valid_BaseAluCoreAir.carry_sub_0
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
: F :=
  c.carry_divide *
  (c.a_0 row rotation + c.c_0 row rotation - c.b_0 row rotation)

@[openvm_encapsulation]
lemma BaseAluCoreAir.carry_sub_0_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (2005401601: F) *
  (c.a_0 row rotation + c.c_0 row rotation - c.b_0 row rotation) =
  c.carry_sub_0 row rotation
:= rfl

def Valid_BaseAluCoreAir.carry_sub_1
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
: F :=
  c.carry_divide *
  (
    c.a_1 row rotation +
    c.c_1 row rotation -
    c.b_1 row rotation +
    c.carry_sub_0 row rotation
  )

@[openvm_encapsulation]
lemma BaseAluCoreAir.carry_sub_1_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (2005401601: F) *
  (c.a_1 row rotation + c.c_1 row rotation - c.b_1 row rotation + c.carry_sub_0 row rotation) =
  c.carry_sub_1 row rotation
:= rfl

def Valid_BaseAluCoreAir.carry_sub_2
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
: F :=
  c.carry_divide *
  (
    c.a_2 row rotation +
    c.c_2 row rotation -
    c.b_2 row rotation +
    c.carry_sub_1 row rotation
  )

@[openvm_encapsulation]
lemma BaseAluCoreAir.carry_sub_2_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (2005401601: F) *
  (c.a_2 row rotation + c.c_2 row rotation - c.b_2 row rotation + c.carry_sub_1 row rotation) =
  c.carry_sub_2 row rotation
:= rfl

def Valid_BaseAluCoreAir.carry_sub_3
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
: F :=
  c.carry_divide *
  (
    c.a_3 row rotation +
    c.c_3 row rotation -
    c.b_3 row rotation +
    c.carry_sub_2 row rotation
  )

@[openvm_encapsulation]
lemma BaseAluCoreAir.carry_sub_3_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (2005401601: F) *
  (c.a_3 row rotation + c.c_3 row rotation - c.b_3 row rotation + c.carry_sub_2 row rotation) =
  c.carry_sub_3 row rotation
:= rfl

def Valid_BaseAluCoreAir.bitwise
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  c.opcode_xor_flag row rotation +
  c.opcode_or_flag row rotation +
  c.opcode_and_flag row rotation

def Valid_BaseAluCoreAir.x_0
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  (1 - c.bitwise row rotation) * c.a_0 row rotation +
  (c.bitwise row rotation) * c.b_0 row rotation

@[openvm_encapsulation]
lemma BaseAluCoreAir.x_0_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (1 - (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation)) *
      c.a_0 row rotation +
  (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation) *
      c.b_0 row rotation =
  c.x_0 row rotation
:= rfl

def Valid_BaseAluCoreAir.x_1
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  (1 - c.bitwise row rotation) * c.a_1 row rotation +
  (c.bitwise row rotation) * c.b_1 row rotation

@[openvm_encapsulation]
lemma BaseAluCoreAir.x_1_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (1 - (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation)) *
      c.a_1 row rotation +
  (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation) *
      c.b_1 row rotation =
  c.x_1 row rotation
:= rfl

def Valid_BaseAluCoreAir.x_2
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  (1 - c.bitwise row rotation) * c.a_2 row rotation +
  (c.bitwise row rotation) * c.b_2 row rotation

@[openvm_encapsulation]
lemma BaseAluCoreAir.x_2_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (1 - (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation)) *
      c.a_2 row rotation +
  (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation) *
      c.b_2 row rotation =
  c.x_2 row rotation
:= rfl

def Valid_BaseAluCoreAir.x_3
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  (1 - c.bitwise row rotation) * c.a_3 row rotation +
  (c.bitwise row rotation) * c.b_3 row rotation

@[openvm_encapsulation]
lemma BaseAluCoreAir.x_3_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (1 - (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation)) *
      c.a_3 row rotation +
  (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation) *
      c.b_3 row rotation =
  c.x_3 row rotation
:= rfl

def Valid_BaseAluCoreAir.y_0
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  (1 - c.bitwise row rotation) * c.a_0 row rotation +
  (c.bitwise row rotation) * c.c_0 row rotation

@[openvm_encapsulation]
lemma BaseAluCoreAir.y_0_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (1 - (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation)) *
      c.a_0 row rotation +
  (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation) *
      c.c_0 row rotation =
  c.y_0 row rotation
:= rfl

def Valid_BaseAluCoreAir.y_1
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  (1 - c.bitwise row rotation) * c.a_1 row rotation +
  (c.bitwise row rotation) * c.c_1 row rotation

@[openvm_encapsulation]
lemma BaseAluCoreAir.y_1_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (1 - (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation)) *
      c.a_1 row rotation +
  (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation) *
      c.c_1 row rotation =
  c.y_1 row rotation
:= rfl

def Valid_BaseAluCoreAir.y_2
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  (1 - c.bitwise row rotation) * c.a_2 row rotation +
  (c.bitwise row rotation) * c.c_2 row rotation

@[openvm_encapsulation]
lemma BaseAluCoreAir.y_2_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (1 - (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation)) *
      c.a_2 row rotation +
  (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation) *
      c.c_2 row rotation =
  c.y_2 row rotation
:= rfl

def Valid_BaseAluCoreAir.y_3
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  (1 - c.bitwise row rotation) * c.a_3 row rotation +
  (c.bitwise row rotation) * c.c_3 row rotation

@[openvm_encapsulation]
lemma BaseAluCoreAir.y_3_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  (1 - (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation)) *
      c.a_3 row rotation +
  (c.opcode_xor_flag row rotation + c.opcode_or_flag row rotation + c.opcode_and_flag row rotation) *
      c.c_3 row rotation =
  c.y_3 row rotation
:= rfl

def Valid_BaseAluCoreAir.x_xor_y_0
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  c.opcode_xor_flag row rotation * c.a_0 row rotation +
  c.opcode_or_flag row rotation * ((2: F) * c.a_0 row rotation - c.b_0 row rotation - c.c_0 row rotation) +
  c.opcode_and_flag row rotation * (c.b_0 row rotation + c.c_0 row rotation - (2 * c.a_0 row rotation))

@[openvm_encapsulation]
lemma BaseAluCoreAir.x_xor_y_0_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  c.opcode_xor_flag row rotation * c.a_0 row rotation +
  c.opcode_or_flag row rotation * (2 * c.a_0 row rotation - c.b_0 row rotation - c.c_0 row rotation) +
  c.opcode_and_flag row rotation * (c.b_0 row rotation + c.c_0 row rotation - 2 * c.a_0 row rotation)
   =
  c.x_xor_y_0 row rotation
:= rfl

def Valid_BaseAluCoreAir.x_xor_y_1
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  c.opcode_xor_flag row rotation * c.a_1 row rotation +
  c.opcode_or_flag row rotation * ((2: F) * c.a_1 row rotation - c.b_1 row rotation - c.c_1 row rotation) +
  c.opcode_and_flag row rotation * (c.b_1 row rotation + c.c_1 row rotation - (2 * c.a_1 row rotation))

@[openvm_encapsulation]
lemma BaseAluCoreAir.x_xor_y_1_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  c.opcode_xor_flag row rotation * c.a_1 row rotation +
  c.opcode_or_flag row rotation * (2 * c.a_1 row rotation - c.b_1 row rotation - c.c_1 row rotation) +
  c.opcode_and_flag row rotation * (c.b_1 row rotation + c.c_1 row rotation - 2 * c.a_1 row rotation)
   =
  c.x_xor_y_1 row rotation
:= rfl

def Valid_BaseAluCoreAir.x_xor_y_2
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  c.opcode_xor_flag row rotation * c.a_2 row rotation +
  c.opcode_or_flag row rotation * ((2: F) * c.a_2 row rotation - c.b_2 row rotation - c.c_2 row rotation) +
  c.opcode_and_flag row rotation * (c.b_2 row rotation + c.c_2 row rotation - (2 * c.a_2 row rotation))

@[openvm_encapsulation]
lemma BaseAluCoreAir.x_xor_y_2_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  c.opcode_xor_flag row rotation * c.a_2 row rotation +
  c.opcode_or_flag row rotation * (2 * c.a_2 row rotation - c.b_2 row rotation - c.c_2 row rotation) +
  c.opcode_and_flag row rotation * (c.b_2 row rotation + c.c_2 row rotation - 2 * c.a_2 row rotation)
   =
  c.x_xor_y_2 row rotation
:= rfl

def Valid_BaseAluCoreAir.x_xor_y_3
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation : ℕ)
: F :=
  c.opcode_xor_flag row rotation * c.a_3 row rotation +
  c.opcode_or_flag row rotation * ((2: F) * c.a_3 row rotation - c.b_3 row rotation - c.c_3 row rotation) +
  c.opcode_and_flag row rotation * (c.b_3 row rotation + c.c_3 row rotation - (2 * c.a_3 row rotation))

@[openvm_encapsulation]
lemma BaseAluCoreAir.x_xor_y_3_def
  [Field F]
  (c : Valid_BaseAluCoreAir F) (row rotation: ℕ)
:
  c.opcode_xor_flag row rotation * c.a_3 row rotation +
  c.opcode_or_flag row rotation * (2 * c.a_3 row rotation - c.b_3 row rotation - c.c_3 row rotation) +
  c.opcode_and_flag row rotation * (c.b_3 row rotation + c.c_3 row rotation - 2 * c.a_3 row rotation)
   =
  c.x_xor_y_3 row rotation
:= rfl

structure MinimalInstruction (F: Type) where
  is_valid : F
  opcode: F

structure AdapterAirContext (F: Type) where
  to_pc : Option F
  reads : Fin 2 → Fin 4 → F
  writes : Fin 4 → F
  instruction : MinimalInstruction F

def Valid_BaseAluCoreAir.class_offset
  [Field F]
  (c : Valid_BaseAluCoreAir F)
: F :=
  512

def Valid_BaseAluCoreAir.ctx
  [Field F]
  (c : Valid_BaseAluCoreAir F)
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
            c.opcode_add_flag row rotation * 0 +
            c.opcode_sub_flag row rotation * 1 +
            c.opcode_xor_flag row rotation * 2 +
            c.opcode_or_flag row rotation * 3 +
            c.opcode_and_flag row rotation * 4
          )
        )
    )


@[openvm_encapsulation]
lemma BaseAluCoreAir.ctx.instruction.opcode_def
  [Field F]
  (c : Valid_BaseAluCoreAir F)
  (row rotation: ℕ)
: 512 +
  (
    c.opcode_sub_flag row rotation +
    c.opcode_xor_flag row rotation * 2 +
    c.opcode_or_flag row rotation * 3 +
    c.opcode_and_flag row rotation * 4
  ) =
  (c.ctx row rotation).instruction.opcode
:= by
  unfold Valid_BaseAluCoreAir.ctx Valid_BaseAluCoreAir.class_offset
  simp
