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

-- def Valid_MultiplicationCoreAir_4_8.is_valid
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- : F :=
--   c.opcode_sll_flag row rotation +
--   c.opcode_srl_flag row rotation +
--   c.opcode_sra_flag row rotation

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.is_valid_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- :
--   c.opcode_sll_flag row rotation +
--   c.opcode_srl_flag row rotation +
--   c.opcode_sra_flag row rotation =
--   c.is_valid row rotation
-- := rfl

-- def Valid_MultiplicationCoreAir_4_8.right_shift
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- : F :=
--   c.opcode_srl_flag row rotation +
--   c.opcode_sra_flag row rotation

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.right_shift_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- :
--   c.opcode_srl_flag row rotation +
--   c.opcode_sra_flag row rotation =
--   c.right_shift row rotation
-- := rfl

-- def Valid_MultiplicationCoreAir_4_8.bit_marker_sum
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- : Fin 8 → F :=
--   λ i => match i with
--     | 0 => 0 + c.bit_shift_marker_0 row rotation
--     | 1 => c.bit_marker_sum row rotation 0 + c.bit_shift_marker_1 row rotation
--     | 2 => c.bit_marker_sum row rotation 1 + c.bit_shift_marker_2 row rotation
--     | 3 => c.bit_marker_sum row rotation 2 + c.bit_shift_marker_3 row rotation
--     | 4 => c.bit_marker_sum row rotation 3 + c.bit_shift_marker_4 row rotation
--     | 5 => c.bit_marker_sum row rotation 4 + c.bit_shift_marker_5 row rotation
--     | 6 => c.bit_marker_sum row rotation 5 + c.bit_shift_marker_6 row rotation
--     | 7 => c.bit_marker_sum row rotation 6 + c.bit_shift_marker_7 row rotation

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.bit_marker_sum_def_1
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_shift_marker_0 row rotation + c.bit_shift_marker_1 row rotation =
--   c.bit_marker_sum row rotation 1
-- := by simp [Valid_MultiplicationCoreAir_4_8.bit_marker_sum.eq_def]


-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.bit_marker_sum_def_2
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_marker_sum row rotation 1 + c.bit_shift_marker_2 row rotation =
--   c.bit_marker_sum row rotation 2
-- := by simp [Valid_MultiplicationCoreAir_4_8.bit_marker_sum.eq_def]

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.bit_marker_sum_def_3
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_marker_sum row rotation 2 + c.bit_shift_marker_3 row rotation =
--   c.bit_marker_sum row rotation 3
-- := by simp [Valid_MultiplicationCoreAir_4_8.bit_marker_sum.eq_def]

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.bit_marker_sum_def_4
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_marker_sum row rotation 3 + c.bit_shift_marker_4 row rotation =
--   c.bit_marker_sum row rotation 4
-- := by simp [Valid_MultiplicationCoreAir_4_8.bit_marker_sum.eq_def]

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.bit_marker_sum_def_5
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_marker_sum row rotation 4 + c.bit_shift_marker_5 row rotation =
--   c.bit_marker_sum row rotation 5
-- := by simp [Valid_MultiplicationCoreAir_4_8.bit_marker_sum.eq_def]

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.bit_marker_sum_def_6
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_marker_sum row rotation 5 + c.bit_shift_marker_6 row rotation =
--   c.bit_marker_sum row rotation 6
-- := by simp [Valid_MultiplicationCoreAir_4_8.bit_marker_sum.eq_def]

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.bit_marker_sum_def_7
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_marker_sum row rotation 6 + c.bit_shift_marker_7 row rotation =
--   c.bit_marker_sum row rotation 7
-- := by simp [Valid_MultiplicationCoreAir_4_8.bit_marker_sum.eq_def]

-- def Valid_MultiplicationCoreAir_4_8.bit_shift
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- : F :=
--   0 +
--   0 * c.bit_shift_marker_0 row rotation +
--   1 * c.bit_shift_marker_1 row rotation +
--   2 * c.bit_shift_marker_2 row rotation +
--   3 * c.bit_shift_marker_3 row rotation +
--   4 * c.bit_shift_marker_4 row rotation +
--   5 * c.bit_shift_marker_5 row rotation +
--   6 * c.bit_shift_marker_6 row rotation +
--   7 * c.bit_shift_marker_7 row rotation

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.bit_shift_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- :
--   c.bit_shift_marker_1 row rotation +
--   2 * c.bit_shift_marker_2 row rotation +
--   3 * c.bit_shift_marker_3 row rotation +
--   4 * c.bit_shift_marker_4 row rotation +
--   5 * c.bit_shift_marker_5 row rotation +
--   6 * c.bit_shift_marker_6 row rotation +
--   7 * c.bit_shift_marker_7 row rotation =
--   c.bit_shift row rotation
-- := by simp [Valid_MultiplicationCoreAir_4_8.bit_shift.eq_def]

-- def Valid_MultiplicationCoreAir_4_8.limb_marker_sum
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- : F :=
--   0 +
--   c.limb_shift_marker_0 row rotation +
--   c.limb_shift_marker_1 row rotation +
--   c.limb_shift_marker_2 row rotation +
--   c.limb_shift_marker_3 row rotation

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.limb_marker_sum_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- :
--   0 +
--   c.limb_shift_marker_0 row rotation +
--   c.limb_shift_marker_1 row rotation +
--   c.limb_shift_marker_2 row rotation +
--   c.limb_shift_marker_3 row rotation =
--   c.limb_marker_sum row rotation
-- := rfl

-- def Valid_MultiplicationCoreAir_4_8.limb_shift
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- : Fin 4 → F :=
--   λ i => match i with
--     | 0 => 0 + 0 * c.limb_shift_marker_0 row rotation
--     | 1 => c.limb_shift row rotation 0 + 1 * c.limb_shift_marker_1 row rotation
--     | 2 => c.limb_shift row rotation 1 + 2 * c.limb_shift_marker_2 row rotation
--     | 3 => c.limb_shift row rotation 2 + 3 * c.limb_shift_marker_3 row rotation

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.limb_shift_2_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.limb_shift_marker_1 row rotation + 2 * c.limb_shift_marker_2 row rotation =
--   c.limb_shift row rotation 2
-- := by simp [Valid_MultiplicationCoreAir_4_8.limb_shift.eq_def]

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.limb_shift_3_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.limb_shift row rotation 2 + 3 * c.limb_shift_marker_3 row rotation =
--   c.limb_shift row rotation 3
-- := by simp [Valid_MultiplicationCoreAir_4_8.limb_shift.eq_def]

-- def Valid_MultiplicationCoreAir_4_8.expected_a_left
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- : Fin 4 → F :=
--   -- index is j - i in the rust
--   λ x => match x with
--     | 0 => 0 +                                                                 c.b_0 row rotation * c.bit_multiplier_left row rotation - 2^8 * c.bit_shift_carry_0 row rotation * c.opcode_sll_flag row rotation
--     | 1 => c.bit_shift_carry_0 row rotation * c.opcode_sll_flag row rotation + c.b_1 row rotation * c.bit_multiplier_left row rotation - 2^8 * c.bit_shift_carry_1 row rotation * c.opcode_sll_flag row rotation
--     | 2 => c.bit_shift_carry_1 row rotation * c.opcode_sll_flag row rotation + c.b_2 row rotation * c.bit_multiplier_left row rotation - 2^8 * c.bit_shift_carry_2 row rotation * c.opcode_sll_flag row rotation
--     | 3 => c.bit_shift_carry_2 row rotation * c.opcode_sll_flag row rotation + c.b_3 row rotation * c.bit_multiplier_left row rotation - 2^8 * c.bit_shift_carry_3 row rotation * c.opcode_sll_flag row rotation

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.expected_a_left_0_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.b_0 row rotation * c.bit_multiplier_left row rotation - 256 * c.bit_shift_carry_0 row rotation * c.opcode_sll_flag row rotation =
--   c.expected_a_left row rotation 0
-- := by simp [ Valid_MultiplicationCoreAir_4_8.expected_a_left.eq_def]; grind

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.expected_a_left_1_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_shift_carry_0 row rotation * c.opcode_sll_flag row rotation + c.b_1 row rotation * c.bit_multiplier_left row rotation - 256 * c.bit_shift_carry_1 row rotation * c.opcode_sll_flag row rotation =
--   c.expected_a_left row rotation 1
-- := by simp [ Valid_MultiplicationCoreAir_4_8.expected_a_left.eq_def]; grind

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.expected_a_left_2_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_shift_carry_1 row rotation * c.opcode_sll_flag row rotation + c.b_2 row rotation * c.bit_multiplier_left row rotation - 256 * c.bit_shift_carry_2 row rotation * c.opcode_sll_flag row rotation =
--   c.expected_a_left row rotation 2
-- := by simp [ Valid_MultiplicationCoreAir_4_8.expected_a_left.eq_def]; grind

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.expected_a_left_3_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_shift_carry_2 row rotation * c.opcode_sll_flag row rotation + c.b_3 row rotation * c.bit_multiplier_left row rotation - 256 * c.bit_shift_carry_3 row rotation * c.opcode_sll_flag row rotation =
--   c.expected_a_left row rotation 3
-- := by simp [ Valid_MultiplicationCoreAir_4_8.expected_a_left.eq_def]; grind

-- def Valid_MultiplicationCoreAir_4_8.expected_a_right
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- : Fin 4 → F :=
--   -- index is j + i in the rust
--   λ x => match x with
--     | 0 => c.bit_shift_carry_1 row rotation * c.right_shift row rotation * 2^8 + c.right_shift row rotation * (c.b_0 row rotation - c.bit_shift_carry_0 row rotation)
--     | 1 => c.bit_shift_carry_2 row rotation * c.right_shift row rotation * 2^8 + c.right_shift row rotation * (c.b_1 row rotation - c.bit_shift_carry_1 row rotation)
--     | 2 => c.bit_shift_carry_3 row rotation * c.right_shift row rotation * 2^8 + c.right_shift row rotation * (c.b_2 row rotation - c.bit_shift_carry_2 row rotation)
--     | 3 => c.b_sign row rotation * (c.bit_multiplier_right row rotation - 1) * 2^8 + c.right_shift row rotation * (c.b_3 row rotation - c.bit_shift_carry_3 row rotation)

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.expected_a_right_0_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_shift_carry_1 row rotation * c.right_shift row rotation * 256 + c.right_shift row rotation * (c.b_0 row rotation - c.bit_shift_carry_0 row rotation) =
--   c.expected_a_right row rotation 0
-- := by simp [ Valid_MultiplicationCoreAir_4_8.expected_a_right.eq_def]; grind

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.expected_a_right_1_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_shift_carry_2 row rotation * c.right_shift row rotation * 256 + c.right_shift row rotation * (c.b_1 row rotation - c.bit_shift_carry_1 row rotation) =
--   c.expected_a_right row rotation 1
-- := by simp [ Valid_MultiplicationCoreAir_4_8.expected_a_right.eq_def]; grind

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.expected_a_right_2_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.bit_shift_carry_3 row rotation * c.right_shift row rotation * 256 + c.right_shift row rotation * (c.b_2 row rotation - c.bit_shift_carry_2 row rotation) =
--   c.expected_a_right row rotation 2
-- := by simp [ Valid_MultiplicationCoreAir_4_8.expected_a_right.eq_def]; grind

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.expected_a_right_3_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : c.b_sign row rotation * (c.bit_multiplier_right row rotation - 1) * 256 + c.right_shift row rotation * (c.b_3 row rotation - c.bit_shift_carry_3 row rotation) =
--   c.expected_a_right row rotation 3
-- := by simp [ Valid_MultiplicationCoreAir_4_8.expected_a_right.eq_def]; grind

-- def Valid_MultiplicationCoreAir_4_8.b_sign_shifted
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- : F :=
--   c.b_sign row rotation * 255

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.b_sign_shifted_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F) (row rotation: ℕ)
-- :
--   c.b_sign row rotation * 255 =
--   c.b_sign_shifted row rotation
-- := rfl

-- def Valid_MultiplicationCoreAir_4_8.class_offset
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
-- : F :=
--   517

-- def Valid_MultiplicationCoreAir_4_8.ctx
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : AdapterAirContext F :=
--   AdapterAirContext.mk
--     .none --to_pc
--     λ x y => match x,y with -- reads
--       | 0, 0 => c.b_0 row rotation
--       | 0, 1 => c.b_1 row rotation
--       | 0, 2 => c.b_2 row rotation
--       | 0, 3 => c.b_3 row rotation
--       | 1, 0 => c.c_0 row rotation
--       | 1, 1 => c.c_1 row rotation
--       | 1, 2 => c.c_2 row rotation
--       | 1, 3 => c.c_3 row rotation
--     λ x => match x with --writes
--       | 0 => c.a_0 row rotation
--       | 1 => c.a_1 row rotation
--       | 2 => c.a_2 row rotation
--       | 3 => c.a_3 row rotation
--     (
--       MinimalInstruction.mk
--         (c.is_valid row rotation) --is_valid
--         (
--           c.class_offset + --opcode
--           (
--             c.opcode_sll_flag row rotation * 0 +
--             c.opcode_srl_flag row rotation * 1 +
--             c.opcode_sra_flag row rotation * 2
--           )
--         )
--     )

-- @[openvm_encapsulation]
-- lemma Valid_MultiplicationCoreAir_4_8.ctx.instruction.opcode_def
--   [Field F]
--   (c : Valid_MultiplicationCoreAir_4_8 F)
--   (row rotation: ℕ)
-- : 517 + (c.opcode_srl_flag row rotation + c.opcode_sra_flag row rotation * 2) =
--   (c.ctx row rotation).instruction.opcode
-- := by
--   unfold Valid_MultiplicationCoreAir_4_8.ctx Valid_MultiplicationCoreAir_4_8.class_offset
--   simp
