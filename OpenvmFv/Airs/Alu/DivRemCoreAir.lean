import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air
import OpenvmFv.Airs.Alu.AdapterAirContext

set_option linter.unusedVariables false

#define_subair "DivRemCoreAir_4_8" using "openvm_encapsulation" where
  Column["b_0"]
  Column["b_1"]
  Column["b_2"]
  Column["b_3"]
  Column["c_0"]
  Column["c_1"]
  Column["c_2"]
  Column["c_3"]
  Column["q_0"]
  Column["q_1"]
  Column["q_2"]
  Column["q_3"]
  Column["r_0"]
  Column["r_1"]
  Column["r_2"]
  Column["r_3"]
  Column["zero_divisor"]
  Column["r_zero"]
  Column["b_sign"]
  Column["c_sign"]
  Column["q_sign"]
  Column["sign_xor"]
  Column["c_sum_inv"]
  Column["r_sum_inv"]
  Column["r_prime_0"]
  Column["r_prime_1"]
  Column["r_prime_2"]
  Column["r_prime_3"]
  Column["r_inv_0"]
  Column["r_inv_1"]
  Column["r_inv_2"]
  Column["r_inv_3"]
  Column["lt_marker_0"]
  Column["lt_marker_1"]
  Column["lt_marker_2"]
  Column["lt_marker_3"]
  Column["lt_diff"]
  Column["opcode_div_flag"]
  Column["opcode_divu_flag"]
  Column["opcode_rem_flag"]
  Column["opcode_remu_flag"]

def Valid_DivRemCoreAir_4_8.is_valid
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.opcode_div_flag row rotation +
  c.opcode_divu_flag row rotation +
  c.opcode_rem_flag row rotation +
  c.opcode_remu_flag row rotation

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.is_valid_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.opcode_div_flag row rotation + c.opcode_divu_flag row rotation + c.opcode_rem_flag row rotation + c.opcode_remu_flag row rotation =
  c.is_valid row rotation
:= by
  rfl

def Valid_DivRemCoreAir_4_8.b_ext
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.b_sign row rotation * 255

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.b_ext_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.b_sign row rotation * 255 =
  c.b_ext row rotation
:= by
  rfl

def Valid_DivRemCoreAir_4_8.c_ext
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.c_sign row rotation * 255

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.c_ext_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.c_sign row rotation * 255 =
  c.c_ext row rotation
:= by
  rfl

def Valid_DivRemCoreAir_4_8.carry_divide
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
: F := 2005401601

mutual
  def Valid_DivRemCoreAir_4_8.carry
    [Field F]
    (c : Valid_DivRemCoreAir_4_8 F) (row rotation : ℕ)
  : Fin 4 → F :=
    λ i => match i with
      | 0 => (c.expected_limb row rotation 0 - c.b_0 row rotation) * c.carry_divide
      | 1 => (c.expected_limb row rotation 1 - c.b_1 row rotation) * c.carry_divide
      | 2 => (c.expected_limb row rotation 2 - c.b_2 row rotation) * c.carry_divide
      | 3 => (c.expected_limb row rotation 3 - c.b_3 row rotation) * c.carry_divide

  -- So named because the name expected_limb is used in two different local definitions in the rust
  def Valid_DivRemCoreAir_4_8.expected_limb
    [Field F]
    (c : Valid_DivRemCoreAir_4_8 F) (row rotation : ℕ)
  : Fin 4 → F :=
    λ i => match i with
      | 0 => 0                      + (c.r_0 row rotation + c.c_0 row rotation * c.q_0 row rotation)
      | 1 => c.carry row rotation 0 + (c.r_1 row rotation + c.c_0 row rotation * c.q_1 row rotation + c.c_1 row rotation * c.q_0 row rotation)
      | 2 => c.carry row rotation 1 + (c.r_2 row rotation + c.c_0 row rotation * c.q_2 row rotation + c.c_1 row rotation * c.q_1 row rotation + c.c_2 row rotation * c.q_0 row rotation)
      | 3 => c.carry row rotation 2 + (c.r_3 row rotation + c.c_0 row rotation * c.q_3 row rotation + c.c_1 row rotation * c.q_2 row rotation + c.c_2 row rotation * c.q_1 row rotation + c.c_3 row rotation * c.q_0 row rotation)
end

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_0
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: ((c.r_0 row rotation + c.c_0 row rotation * c.q_0 row rotation) - c.b_0 row rotation) * 2005401601 =
  c.carry row rotation 0
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def,
    Valid_DivRemCoreAir_4_8.expected_limb.eq_def
  ]

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_1
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.carry row rotation 0 + (c.r_1 row rotation + c.c_0 row rotation * c.q_1 row rotation + c.c_1 row rotation * c.q_0 row rotation) - c.b_1 row rotation) * 2005401601 =
  c.carry row rotation 1
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def,
    Valid_DivRemCoreAir_4_8.expected_limb.eq_def
  ]

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_2
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.carry row rotation 1 + (c.r_2 row rotation + c.c_0 row rotation * c.q_2 row rotation + c.c_1 row rotation * c.q_1 row rotation + c.c_2 row rotation * c.q_0 row rotation) - c.b_2 row rotation) * 2005401601 =
  c.carry row rotation 2
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def,
    Valid_DivRemCoreAir_4_8.expected_limb.eq_def
  ]

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_3
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.carry row rotation 2 + (c.r_3 row rotation + c.c_0 row rotation * c.q_3 row rotation + c.c_1 row rotation * c.q_2 row rotation + c.c_2 row rotation * c.q_1 row rotation + c.c_3 row rotation * c.q_0 row rotation) - c.b_3 row rotation) * 2005401601 =
  c.carry row rotation 3
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def,
    Valid_DivRemCoreAir_4_8.expected_limb.eq_def
  ]

def Valid_DivRemCoreAir_4_8.q_ext
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.q_sign row rotation * 255

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.q_ext_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.q_sign row rotation * 255 =
  c.q_ext row rotation
:= by
  rfl

mutual
  def Valid_DivRemCoreAir_4_8.carry_ext
    [Field F]
    (c : Valid_DivRemCoreAir_4_8 F) (row rotation : ℕ)
  : Fin 4 → F :=
    λ i => match i with
      | 0 => (c.expected_limb_ext row rotation 0 - c.b_ext row rotation) * c.carry_divide
      | 1 => (c.expected_limb_ext row rotation 1 - c.b_ext row rotation) * c.carry_divide
      | 2 => (c.expected_limb_ext row rotation 2 - c.b_ext row rotation) * c.carry_divide
      | 3 => (c.expected_limb_ext row rotation 3 - c.b_ext row rotation) * c.carry_divide

  def Valid_DivRemCoreAir_4_8.expected_limb_ext
    [Field F]
    (c : Valid_DivRemCoreAir_4_8 F) (row rotation : ℕ)
  : Fin 4 → F :=
    λ i => match i with
      | 0 =>
        c.carry row rotation 3 +
        (c.c_1 row rotation * c.q_3 row rotation +
        c.c_2 row rotation * c.q_2 row rotation +
        c.c_3 row rotation * c.q_1 row rotation) +
        (c.c_0 row rotation * c.q_ext row rotation + c.q_0 row rotation * c.c_ext row rotation) +
        (1 - c.r_zero row rotation) * c.b_ext row rotation
      | 1 =>
        c.carry_ext row rotation 0 +
        (c.c_2 row rotation * c.q_3 row rotation +
        c.c_3 row rotation * c.q_2 row rotation) +
        (c.c_0 row rotation * c.q_ext row rotation + c.q_0 row rotation * c.c_ext row rotation +
        c.c_1 row rotation * c.q_ext row rotation + c.q_1 row rotation * c.c_ext row rotation) +
        (1 - c.r_zero row rotation) * c.b_ext row rotation
      | 2 =>
        c.carry_ext row rotation 1 +
        c.c_3 row rotation * c.q_3 row rotation +
        (c.c_0 row rotation * c.q_ext row rotation + c.q_0 row rotation * c.c_ext row rotation +
        c.c_1 row rotation * c.q_ext row rotation + c.q_1 row rotation * c.c_ext row rotation +
        c.c_2 row rotation * c.q_ext row rotation + c.q_2 row rotation * c.c_ext row rotation) +
        (1 - c.r_zero row rotation) * c.b_ext row rotation
      | 3 =>
        c.carry_ext row rotation 2 +
        (c.c_0 row rotation * c.q_ext row rotation + c.q_0 row rotation * c.c_ext row rotation +
        c.c_1 row rotation * c.q_ext row rotation + c.q_1 row rotation * c.c_ext row rotation +
        c.c_2 row rotation * c.q_ext row rotation + c.q_2 row rotation * c.c_ext row rotation +
        c.c_3 row rotation * c.q_ext row rotation + c.q_3 row rotation * c.c_ext row rotation) +
        (1 - c.r_zero row rotation) * c.b_ext row rotation
end

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_ext_0_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (
    c.carry row rotation 3 +
    (c.c_1 row rotation * c.q_3 row rotation +
    c.c_2 row rotation * c.q_2 row rotation +
    c.c_3 row rotation * c.q_1 row rotation) +
    (c.c_0 row rotation * c.q_ext row rotation + c.q_0 row rotation * c.c_ext row rotation) +
    (1 - c.r_zero row rotation) * c.b_ext row rotation -
    c.b_ext row rotation
  ) * 2005401601 =
  c.carry_ext row rotation 0
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry_ext.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def,
    Valid_DivRemCoreAir_4_8.expected_limb_ext.eq_def
  ]

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_ext_1_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (
    c.carry_ext row rotation 0 +
    (c.c_2 row rotation * c.q_3 row rotation +
    c.c_3 row rotation * c.q_2 row rotation) +
    (c.c_0 row rotation * c.q_ext row rotation + c.q_0 row rotation * c.c_ext row rotation +
    c.c_1 row rotation * c.q_ext row rotation + c.q_1 row rotation * c.c_ext row rotation) +
    (1 - c.r_zero row rotation) * c.b_ext row rotation
    - c.b_ext row rotation
  ) * 2005401601 =
  c.carry_ext row rotation 1
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry_ext.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def,
    Valid_DivRemCoreAir_4_8.expected_limb_ext.eq_def
  ]

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_ext_2_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (
    c.carry_ext row rotation 1 +
    c.c_3 row rotation * c.q_3 row rotation +
    (c.c_0 row rotation * c.q_ext row rotation + c.q_0 row rotation * c.c_ext row rotation +
    c.c_1 row rotation * c.q_ext row rotation + c.q_1 row rotation * c.c_ext row rotation +
    c.c_2 row rotation * c.q_ext row rotation + c.q_2 row rotation * c.c_ext row rotation) +
    (1 - c.r_zero row rotation) * c.b_ext row rotation -
    c.b_ext row rotation
  ) * 2005401601 =
  c.carry_ext row rotation 2
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry_ext.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def,
    Valid_DivRemCoreAir_4_8.expected_limb_ext.eq_def
  ]

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_ext_3_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (
    c.carry_ext row rotation 2 +
    (c.c_0 row rotation * c.q_ext row rotation + c.q_0 row rotation * c.c_ext row rotation +
    c.c_1 row rotation * c.q_ext row rotation + c.q_1 row rotation * c.c_ext row rotation +
    c.c_2 row rotation * c.q_ext row rotation + c.q_2 row rotation * c.c_ext row rotation +
    c.c_3 row rotation * c.q_ext row rotation + c.q_3 row rotation * c.c_ext row rotation) +
    (1 - c.r_zero row rotation) * c.b_ext row rotation -
    c.b_ext row rotation
  ) * 2005401601 =
  c.carry_ext row rotation 3
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry_ext.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def,
    Valid_DivRemCoreAir_4_8.expected_limb_ext.eq_def
  ]

def Valid_DivRemCoreAir_4_8.special_case
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.zero_divisor row rotation + c.r_zero row rotation

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.special_case_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.zero_divisor row rotation + c.r_zero row rotation =
  c.special_case row rotation
:= by
  rfl

def Valid_DivRemCoreAir_4_8.c_sum
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.c_0 row rotation +
  c.c_1 row rotation +
  c.c_2 row rotation +
  c.c_3 row rotation

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.c_sum_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.c_0 row rotation +
  c.c_1 row rotation +
  c.c_2 row rotation +
  c.c_3 row rotation =
  c.c_sum row rotation
:= by
  rfl

def Valid_DivRemCoreAir_4_8.valid_and_not_zero_divisor
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.is_valid row rotation -
  c.zero_divisor row rotation

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.valid_and_not_zero_divisor_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.is_valid row rotation -
  c.zero_divisor row rotation =
  c.valid_and_not_zero_divisor row rotation
:= by
  rfl

def Valid_DivRemCoreAir_4_8.r_sum
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.r_0 row rotation +
  c.r_1 row rotation +
  c.r_2 row rotation +
  c.r_3 row rotation

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.r_sum_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.r_0 row rotation +
  c.r_1 row rotation +
  c.r_2 row rotation +
  c.r_3 row rotation =
  c.r_sum row rotation
:= by
  rfl

def Valid_DivRemCoreAir_4_8.valid_and_not_special_case
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.is_valid row rotation -
  c.special_case row rotation

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.valid_and_not_special_case_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.is_valid row rotation -
  c.special_case row rotation =
  c.valid_and_not_special_case row rotation
:= by
  rfl

def Valid_DivRemCoreAir_4_8.signed
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.opcode_div_flag row rotation + c.opcode_rem_flag row rotation

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.signed_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.opcode_div_flag row rotation + c.opcode_rem_flag row rotation =
  c.signed row rotation
:= by
  rfl

def Valid_DivRemCoreAir_4_8.nonzero_q
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.q_0 row rotation +
  c.q_1 row rotation +
  c.q_2 row rotation +
  c.q_3 row rotation

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.nonzero_q_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: c.q_0 row rotation +
  c.q_1 row rotation +
  c.q_2 row rotation +
  c.q_3 row rotation =
  c.nonzero_q row rotation
:= by
  rfl

def Valid_DivRemCoreAir_4_8.carry_lt
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F) (row rotation : ℕ)
: Fin 4 → F :=
  λ i => match i with
    | 0 => (c.r_0 row rotation + c.r_prime_0 row rotation) * c.carry_divide
    | 1 => (c.carry_lt row rotation 0 + c.r_1 row rotation + c.r_prime_1 row rotation) * c.carry_divide
    | 2 => (c.carry_lt row rotation 1 + c.r_2 row rotation + c.r_prime_2 row rotation) * c.carry_divide
    | 3 => (c.carry_lt row rotation 2 + c.r_3 row rotation + c.r_prime_3 row rotation) * c.carry_divide

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_lt_0_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.r_0 row rotation + c.r_prime_0 row rotation) * 2005401601 =
  c.carry_lt row rotation 0
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry_lt.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def
  ]

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_lt_1_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.carry_lt row rotation 0 + c.r_1 row rotation + c.r_prime_1 row rotation) * 2005401601 =
  c.carry_lt row rotation 1
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry_lt.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def
  ]

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_lt_2_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.carry_lt row rotation 1 + c.r_2 row rotation + c.r_prime_2 row rotation) * 2005401601 =
  c.carry_lt row rotation 2
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry_lt.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def
  ]

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.carry_lt_3_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.carry_lt row rotation 2 + c.r_3 row rotation + c.r_prime_3 row rotation) * 2005401601 =
  c.carry_lt row rotation 3
:= by
  simp [
    Valid_DivRemCoreAir_4_8.carry_lt.eq_def,
    Valid_DivRemCoreAir_4_8.carry_divide.eq_def
  ]

def Valid_DivRemCoreAir_4_8.diff
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F) (row rotation : ℕ)
: Fin 4 → F :=
  λ i => match i with
    | 0 => c.r_prime_0 row rotation * (2 * c.c_sign row rotation - 1) + c.c_0 row rotation * (1 - 2 * c.c_sign row rotation)
    | 1 => c.r_prime_1 row rotation * (2 * c.c_sign row rotation - 1) + c.c_1 row rotation * (1 - 2 * c.c_sign row rotation)
    | 2 => c.r_prime_2 row rotation * (2 * c.c_sign row rotation - 1) + c.c_2 row rotation * (1 - 2 * c.c_sign row rotation)
    | 3 => c.r_prime_3 row rotation * (2 * c.c_sign row rotation - 1) + c.c_3 row rotation * (1 - 2 * c.c_sign row rotation)

def Valid_DivRemCoreAir_4_8.prefix_sum
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F) (row rotation : ℕ)
: Fin 4 → F :=
  λ i => match i with
    | 0 => c.special_case row rotation + c.lt_marker_3 row rotation + c.lt_marker_2 row rotation + c.lt_marker_1 row rotation + c.lt_marker_0 row rotation
    | 1 => c.special_case row rotation + c.lt_marker_3 row rotation + c.lt_marker_2 row rotation + c.lt_marker_1 row rotation
    | 2 => c.special_case row rotation + c.lt_marker_3 row rotation + c.lt_marker_2 row rotation
    | 3 => c.special_case row rotation + c.lt_marker_3 row rotation

def Valid_DivRemCoreAir_4_8.is_div
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: F :=
  c.opcode_div_flag row rotation + c.opcode_divu_flag row rotation

def Valid_DivRemCoreAir_4_8.a
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F) (row rotation : ℕ)
: Fin 4 → F :=
  λ i => match i with
    | 0 => c.is_div row rotation * c.q_0 row rotation + (1 - c.is_div row rotation) * c.r_0 row rotation
    | 1 => c.is_div row rotation * c.q_1 row rotation + (1 - c.is_div row rotation) * c.r_1 row rotation
    | 2 => c.is_div row rotation * c.q_2 row rotation + (1 - c.is_div row rotation) * c.r_2 row rotation
    | 3 => c.is_div row rotation * c.q_3 row rotation + (1 - c.is_div row rotation) * c.r_3 row rotation

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.a_0_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.opcode_div_flag row rotation + c.opcode_divu_flag row rotation) * c.q_0 row rotation +
  (1 - (c.opcode_div_flag row rotation + c.opcode_divu_flag row rotation)) * c.r_0 row rotation =
  c.a row rotation 0
:= rfl

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.a_1_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.opcode_div_flag row rotation + c.opcode_divu_flag row rotation) * c.q_1 row rotation +
  (1 - (c.opcode_div_flag row rotation + c.opcode_divu_flag row rotation)) * c.r_1 row rotation =
  c.a row rotation 1
:= rfl

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.a_2_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.opcode_div_flag row rotation + c.opcode_divu_flag row rotation) * c.q_2 row rotation +
  (1 - (c.opcode_div_flag row rotation + c.opcode_divu_flag row rotation)) * c.r_2 row rotation =
  c.a row rotation 2
:= rfl

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.a_3_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: (c.opcode_div_flag row rotation + c.opcode_divu_flag row rotation) * c.q_3 row rotation +
  (1 - (c.opcode_div_flag row rotation + c.opcode_divu_flag row rotation)) * c.r_3 row rotation =
  c.a row rotation 3
:= rfl

def Valid_DivRemCoreAir_4_8.class_offset
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
: F :=
  596

def Valid_DivRemCoreAir_4_8.ctx
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
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
      | 0 => c.a row rotation 0
      | 1 => c.a row rotation 1
      | 2 => c.a row rotation 2
      | 3 => c.a row rotation 3
    (
      MinimalInstruction.mk
        (c.is_valid row rotation) --is_valid
        (
          c.class_offset + --opcode
          (
            c.opcode_div_flag row rotation * 0 +
            c.opcode_divu_flag row rotation * 1 +
            c.opcode_rem_flag row rotation * 2 +
            c.opcode_remu_flag row rotation * 3
          )
        )
    )

@[openvm_encapsulation]
lemma DivRemCoreAir_4_8.ctx_opcode_def
  [Field F]
  (c : Valid_DivRemCoreAir_4_8 F)
  (row rotation : ℕ)
: 596 + --opcode
  (
    c.opcode_div_flag row rotation * 0 +
    c.opcode_divu_flag row rotation * 1 +
    c.opcode_rem_flag row rotation * 2 +
    c.opcode_remu_flag row rotation * 3
  ) =
  (c.ctx row rotation).instruction.opcode
:= rfl
