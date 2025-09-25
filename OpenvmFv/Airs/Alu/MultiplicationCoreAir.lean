import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air
import OpenvmFv.Airs.Alu.AdapterAirContext

set_option linter.unusedVariables false

#define_subair "MultiplicationCoreAir_4_8" using "openvm_encapsulation" where
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
  Column["is_valid"]

def Valid_MultiplicationCoreAir_4_8.carry_divide
  [Field F]
  (c : Valid_MultiplicationCoreAir_4_8 F)
: F := 2005401601

mutual
  def Valid_MultiplicationCoreAir_4_8.carry
    [Field F]
    (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation : ℕ)
  : Fin 4 → F :=
    λ i => match i with
      | 0 => c.carry_divide * (c.expected_limb row rotation 0 - c.a_0 row rotation)
      | 1 => c.carry_divide * (c.expected_limb row rotation 1 - c.a_1 row rotation)
      | 2 => c.carry_divide * (c.expected_limb row rotation 2 - c.a_2 row rotation)
      | 3 => c.carry_divide * (c.expected_limb row rotation 3 - c.a_3 row rotation)

  def Valid_MultiplicationCoreAir_4_8.expected_limb
    [Field F]
    (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation : ℕ)
  : Fin 4 → F :=
    λ i => match i with
      | 0 => 0 + (0 + c.b_0 row rotation * c.c_0 row rotation)
      | 1 => c.carry row rotation 0 + (0 + c.b_0 row rotation * c.c_1 row rotation + c.b_1 row rotation * c.c_0 row rotation)
      | 2 => c.carry row rotation 1 + (0 + c.b_0 row rotation * c.c_2 row rotation + c.b_1 row rotation * c.c_1 row rotation + c.b_2 row rotation * c.c_0 row rotation)
      | 3 => c.carry row rotation 2 + (0 + c.b_0 row rotation * c.c_3 row rotation + c.b_1 row rotation * c.c_2 row rotation + c.b_2 row rotation * c.c_1 row rotation + c.b_3 row rotation * c.c_0 row rotation)
end

@[openvm_encapsulation]
lemma MultiplicationCoreAir_4_8.carry_0
  [Field F]
  (c : Valid_MultiplicationCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * ((c.b_0 row rotation * c.c_0 row rotation) - c.a_0 row rotation) =
  c.carry row rotation 0
:= by
  simp [
    Valid_MultiplicationCoreAir_4_8.carry.eq_def,
    Valid_MultiplicationCoreAir_4_8.carry_divide.eq_def,
    Valid_MultiplicationCoreAir_4_8.expected_limb.eq_def
  ]

@[openvm_encapsulation]
lemma MultiplicationCoreAir_4_8.carry_1
  [Field F]
  (c : Valid_MultiplicationCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * (c.carry row rotation 0 + (c.b_0 row rotation * c.c_1 row rotation + c.b_1 row rotation * c.c_0 row rotation) - c.a_1 row rotation) =
  c.carry row rotation 1
:= by
  simp [
    Valid_MultiplicationCoreAir_4_8.carry.eq_def,
    Valid_MultiplicationCoreAir_4_8.carry_divide.eq_def,
    Valid_MultiplicationCoreAir_4_8.expected_limb.eq_def
  ]

@[openvm_encapsulation]
lemma MultiplicationCoreAir_4_8.carry_2
  [Field F]
  (c : Valid_MultiplicationCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * (c.carry row rotation 1 + (c.b_0 row rotation * c.c_2 row rotation + c.b_1 row rotation * c.c_1 row rotation + c.b_2 row rotation * c.c_0 row rotation) - c.a_2 row rotation) =
  c.carry row rotation 2
:= by
  simp [
    Valid_MultiplicationCoreAir_4_8.carry.eq_def,
    Valid_MultiplicationCoreAir_4_8.carry_divide.eq_def,
    Valid_MultiplicationCoreAir_4_8.expected_limb.eq_def
  ]

@[openvm_encapsulation]
lemma MultiplicationCoreAir_4_8.carry_3
  [Field F]
  (c : Valid_MultiplicationCoreAir_4_8 F)
  (row rotation : ℕ)
: 2005401601 * (c.carry row rotation 2 + (c.b_0 row rotation * c.c_3 row rotation + c.b_1 row rotation * c.c_2 row rotation + c.b_2 row rotation * c.c_1 row rotation + c.b_3 row rotation * c.c_0 row rotation) - c.a_3 row rotation) =
  c.carry row rotation 3
:= by
  simp [
    Valid_MultiplicationCoreAir_4_8.carry.eq_def,
    Valid_MultiplicationCoreAir_4_8.carry_divide.eq_def,
    Valid_MultiplicationCoreAir_4_8.expected_limb.eq_def
  ]

def Valid_MultiplicationCoreAir_4_8.class_offset
  [Field F]
  (c : Valid_MultiplicationCoreAir_4_8 F)
: F :=
  592

def Valid_MultiplicationCoreAir_4_8.ctx
  [Field F]
  (c : Valid_MultiplicationCoreAir_4_8 F)
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
          c.class_offset --opcode
        )
    )

@[openvm_encapsulation]
lemma Valid_MultiplicationCoreAir_4_8.ctx.instruction.opcode_def
  [Field F]
  (c : Valid_MultiplicationCoreAir_4_8 F)
  (row rotation: ℕ)
: 592 =
  (c.ctx row rotation).instruction.opcode
:= by
  unfold Valid_MultiplicationCoreAir_4_8.ctx Valid_MultiplicationCoreAir_4_8.class_offset
  simp
