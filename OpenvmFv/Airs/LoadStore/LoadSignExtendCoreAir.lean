import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Fundamentals.BabyBear

set_option linter.unusedVariables false

#define_subair "LoadSignExtendCoreAir_4" using "openvm_encapsulation" where
  Column["opcode_loadb_flag0"]
  Column["opcode_loadb_flag1"]
  Column["opcode_loadh_flag"]
  Column["shift_most_sig_bit"]
  Column["data_most_sig_bit"]
  Column["shifted_read_data_0"]
  Column["shifted_read_data_1"]
  Column["shifted_read_data_2"]
  Column["shifted_read_data_3"]
  Column["prev_data_0"]
  Column["prev_data_1"]
  Column["prev_data_2"]
  Column["prev_data_3"]

-- def Valid_LoadStoreCoreAir_4.sum
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- : F :=
--   c.flags_0 row rotation +
--   c.flags_1 row rotation +
--   c.flags_2 row rotation +
--   c.flags_3 row rotation

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.sum
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_0 row rotation +
--   c.flags_1 row rotation +
--   c.flags_2 row rotation +
--   c.flags_3 row rotation =
--   c.sum row rotation
-- := rfl

-- def Valid_LoadStoreCoreAir_4.inv_2
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
-- : F :=
--   1006632961

-- def Valid_LoadStoreCoreAir_4.opcode_flags
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
-- : Fin 14 → F :=
--   λ idx => match idx with
--     | 0 => c.flags_0 row rotation * (c.flags_0 row rotation - 1) * c.inv_2
--     | 1 => c.flags_1 row rotation * (c.flags_1 row rotation - 1) * c.inv_2
--     | 2 => c.flags_2 row rotation * (c.flags_2 row rotation - 1) * c.inv_2
--     | 3 => c.flags_3 row rotation * (c.flags_3 row rotation - 1) * c.inv_2
--     | 4 => c.flags_0 row rotation * (c.sum row rotation - 2) * 2013265920
--     | 5 => c.flags_1 row rotation * (c.sum row rotation - 2) * 2013265920
--     | 6 => c.flags_2 row rotation * (c.sum row rotation - 2) * 2013265920
--     | 7 => c.flags_3 row rotation * (c.sum row rotation - 2) * 2013265920
--     | 8 => c.flags_0 row rotation * c.flags_1 row rotation
--     | 9 => c.flags_0 row rotation * c.flags_2 row rotation
--     | 10 => c.flags_0 row rotation * c.flags_3 row rotation
--     | 11 => c.flags_1 row rotation * c.flags_2 row rotation
--     | 12 => c.flags_1 row rotation * c.flags_3 row rotation
--     | 13 => c.flags_2 row rotation * c.flags_3 row rotation

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_0
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_0 row rotation *
--   (c.flags_0 row rotation - 1) *
--   1006632961 =
--   c.opcode_flags row rotation 0
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_1
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_1 row rotation *
--   (c.flags_1 row rotation - 1) *
--   1006632961 =
--   c.opcode_flags row rotation 1
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_2
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_2 row rotation *
--   (c.flags_2 row rotation - 1) *
--   1006632961 =
--   c.opcode_flags row rotation 2
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_3
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_3 row rotation *
--   (c.flags_3 row rotation - 1) *
--   1006632961 =
--   c.opcode_flags row rotation 3
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_4
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_0 row rotation *
--   (c.sum row rotation - 2) *
--   2013265920 =
--   c.opcode_flags row rotation 4
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_5
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_1 row rotation *
--   (c.sum row rotation - 2) *
--   2013265920 =
--   c.opcode_flags row rotation 5
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_6
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_2 row rotation *
--   (c.sum row rotation - 2) *
--   2013265920 =
--   c.opcode_flags row rotation 6
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_7
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_3 row rotation *
--   (c.sum row rotation - 2) *
--   2013265920 =
--   c.opcode_flags row rotation 7
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_8
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_0 row rotation *
--   c.flags_1 row rotation =
--   c.opcode_flags row rotation 8
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_9
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_0 row rotation *
--   c.flags_2 row rotation =
--   c.opcode_flags row rotation 9
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_10
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_0 row rotation *
--   c.flags_3 row rotation =
--   c.opcode_flags row rotation 10
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_11
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_1 row rotation *
--   c.flags_2 row rotation =
--   c.opcode_flags row rotation 11
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_12
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_1 row rotation *
--   c.flags_3 row rotation =
--   c.opcode_flags row rotation 12
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_flags_13
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.flags_2 row rotation *
--   c.flags_3 row rotation =
--   c.opcode_flags row rotation 13
-- := rfl

-- def Valid_LoadStoreCoreAir_4.opcode_when
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
--   (opcodes : List (Fin 14))
-- : F :=
--   match opcodes with
--     | [] => 0
--     | o::os => c.opcode_flags row rotation o + c.opcode_when row rotation os

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_when_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.opcode_flags row rotation x =
--   c.opcode_when row rotation [x]
-- := by
--   simp [Valid_LoadStoreCoreAir_4.opcode_when]

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.opcode_when_def'
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.opcode_when row rotation l +
--   c.opcode_when row rotation [x] =
--   c.opcode_when row rotation (l ++ [x])
-- := by
--   induction l with
--     | nil => simp [Valid_LoadStoreCoreAir_4.opcode_when]
--     | cons head tail h_tail =>
--       unfold Valid_LoadStoreCoreAir_4.opcode_when
--       simp [←h_tail, Valid_LoadStoreCoreAir_4.opcode_when]
--       grind

-- abbrev LS.LoadW0: Fin 14 := 0
-- abbrev LS.LoadHu0: Fin 14 := 1
-- abbrev LS.LoadHu2: Fin 14 := 2
-- abbrev LS.LoadBu0: Fin 14 := 3
-- abbrev LS.LoadBu1: Fin 14 := 4
-- abbrev LS.LoadBu2: Fin 14 := 5
-- abbrev LS.LoadBu3: Fin 14 := 6
-- abbrev LS.StoreW0: Fin 14 := 7
-- abbrev LS.StoreH0: Fin 14 := 8
-- abbrev LS.StoreH2: Fin 14 := 9
-- abbrev LS.StoreB0: Fin 14 := 10
-- abbrev LS.StoreB1: Fin 14 := 11
-- abbrev LS.StoreB2: Fin 14 := 12
-- abbrev LS.StoreB3: Fin 14 := 13

-- def Valid_LoadStoreCoreAir_4.expected_load_val
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
-- : Fin 4 →  F :=
--   λ idx => match idx with
--     | 0 =>
--       c.opcode_when row rotation [
--         LS.LoadW0, LS.LoadHu0, LS.LoadBu0
--       ] * c.read_data_0 row rotation +
--       c.opcode_when row rotation [
--         LS.LoadBu1
--       ] * c.read_data_1 row rotation +
--       c.opcode_when row rotation [
--         LS.LoadHu2, LS.LoadBu2
--       ] * c.read_data_2 row rotation +
--       c.opcode_when row rotation [
--         LS.LoadBu3
--       ] * c.read_data_3 row rotation
--     | 1 =>
--       c.opcode_when row rotation [
--         LS.LoadW0, LS.LoadHu0
--       ] * c.read_data_1 row rotation +
--       c.opcode_when row rotation [
--         LS.LoadHu2
--       ] * c.read_data_3 row rotation
--     | 2 =>
--       c.opcode_when row rotation [LS.LoadW0] *
--       c.read_data_2 row rotation
--     | 3 =>
--       c.opcode_when row rotation [LS.LoadW0] *
--       c.read_data_3 row rotation

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.expected_load_val_0_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.opcode_when row rotation [
--         LS.LoadW0, LS.LoadHu0, LS.LoadBu0
--       ] * c.read_data_0 row rotation +
--       c.opcode_when row rotation [
--         LS.LoadBu1
--       ] * c.read_data_1 row rotation +
--       c.opcode_when row rotation [
--         LS.LoadHu2, LS.LoadBu2
--       ] * c.read_data_2 row rotation +
--       c.opcode_when row rotation [
--         LS.LoadBu3
--       ] * c.read_data_3 row rotation =
--   c.expected_load_val row rotation 0
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.expected_load_val_1_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.opcode_when row rotation [
--         LS.LoadW0, LS.LoadHu0
--       ] * c.read_data_1 row rotation +
--       c.opcode_when row rotation [
--         LS.LoadHu2
--       ] * c.read_data_3 row rotation =
--   c.expected_load_val row rotation 1
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.expected_load_val_2_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.opcode_when row rotation [LS.LoadW0] *
--       c.read_data_2 row rotation =
--   c.expected_load_val row rotation 2
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.expected_load_val_3_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.opcode_when row rotation [LS.LoadW0] *
--       c.read_data_3 row rotation =
--   c.expected_load_val row rotation 3
-- := rfl

-- def Valid_LoadStoreCoreAir_4.expected_store_val
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
-- : Fin 4 →  F :=
--   λ idx => match idx with
--     | 0 =>
--       c.opcode_when row rotation [
--         LS.StoreW0, LS.StoreH0, LS.StoreB0
--       ] * c.read_data_0 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreH2, LS.StoreB1, LS.StoreB2, LS.StoreB3
--       ] * c.prev_data_0 row rotation
--     | 1 =>
--       c.opcode_when row rotation [
--         LS.StoreB1
--       ] * c.read_data_0 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreW0, LS.StoreH0
--       ] * c.read_data_1 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreH2, LS.StoreB0, LS.StoreB2, LS.StoreB3
--       ] * c.prev_data_1 row rotation
--     | 2 =>
--       c.opcode_when row rotation [
--         LS.StoreH2, LS.StoreB2
--       ] * c.read_data_0 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreW0
--       ] * c.read_data_2 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreH0, LS.StoreB0, LS.StoreB1, LS.StoreB3
--       ] * c.prev_data_2 row rotation
--     | 3 =>
--       c.opcode_when row rotation [
--         LS.StoreB3
--       ] * c.read_data_0 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreH2
--       ] * c.read_data_1 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreW0
--       ] * c.read_data_3 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreH0, LS.StoreB0, LS.StoreB1, LS.StoreB2
--       ] * c.prev_data_3 row rotation

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.expected_store_val_0_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.opcode_when row rotation [
--         LS.StoreW0, LS.StoreH0, LS.StoreB0
--       ] * c.read_data_0 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreH2, LS.StoreB1, LS.StoreB2, LS.StoreB3
--       ] * c.prev_data_0 row rotation =
--   c.expected_store_val row rotation 0
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.expected_store_val_1_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.opcode_when row rotation [
--         LS.StoreB1
--       ] * c.read_data_0 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreW0, LS.StoreH0
--       ] * c.read_data_1 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreH2, LS.StoreB0, LS.StoreB2, LS.StoreB3
--       ] * c.prev_data_1 row rotation =
--   c.expected_store_val row rotation 1
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.expected_store_val_2_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.opcode_when row rotation [
--         LS.StoreH2, LS.StoreB2
--       ] * c.read_data_0 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreW0
--       ] * c.read_data_2 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreH0, LS.StoreB0, LS.StoreB1, LS.StoreB3
--       ] * c.prev_data_2 row rotation =
--   c.expected_store_val row rotation 2
-- := rfl

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.expected_store_val_3_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F) (row rotation: ℕ)
-- :
--   c.opcode_when row rotation [
--         LS.StoreB3
--       ] * c.read_data_0 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreH2
--       ] * c.read_data_1 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreW0
--       ] * c.read_data_3 row rotation +
--       c.opcode_when row rotation [
--         LS.StoreH0, LS.StoreB0, LS.StoreB1, LS.StoreB2
--       ] * c.prev_data_3 row rotation =
--   c.expected_store_val row rotation 3
-- := rfl

-- def Valid_LoadStoreCoreAir_4.expected_val
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
-- : Fin 4 →  F :=
--   λ idx =>
--     c.expected_load_val row rotation idx +
--     c.expected_store_val row rotation idx

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.expected_val_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ) (idx : Fin 4)
-- :
--   c.expected_load_val row rotation idx +
--   c.expected_store_val row rotation idx =
--   c.expected_val row rotation idx
-- := rfl

-- def Valid_LoadStoreCoreAir_4.expected_opcode
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
-- : F :=
--   528 +
--     (c.opcode_when row rotation [1, 2] * 2 + c.opcode_when row rotation [3, 4, 5, 6] +
--           c.opcode_when row rotation [7] * 3 +
--         c.opcode_when row rotation [8, 9] * 4 +
--       c.opcode_when row rotation [10, 11, 12, 13] * 5)

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.expected_opcode_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
-- :
--   528 +
--     (c.opcode_when row rotation [1, 2] * 2 + c.opcode_when row rotation [3, 4, 5, 6] +
--           c.opcode_when row rotation [7] * 3 +
--         c.opcode_when row rotation [8, 9] * 4 +
--       c.opcode_when row rotation [10, 11, 12, 13] * 5) =
--   c.expected_opcode row rotation
-- := rfl

-- def Valid_LoadStoreCoreAir_4.load_shift_amount
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
-- : F :=
--   c.opcode_when row rotation [4] +
--   c.opcode_when row rotation [2, 5] * 2+
--   c.opcode_when row rotation [6] * 3

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.load_shift_amount_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
-- :
--   c.opcode_when row rotation [4] +
--   c.opcode_when row rotation [2, 5] * 2+
--   c.opcode_when row rotation [6] * 3 =
--   c.load_shift_amount row rotation
-- := rfl

-- def Valid_LoadStoreCoreAir_4.store_shift_amount
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
-- : F :=
--   c.opcode_when row rotation [11] +
--   c.opcode_when row rotation [9, 12] * 2+
--   c.opcode_when row rotation [13] * 3

-- @[openvm_encapsulation]
-- lemma LoadStoreCoreAir_4.store_shift_amount_def
--   [Field F]
--   (c : Valid_LoadStoreCoreAir_4 F)
--   (row rotation : ℕ)
-- :
--   c.opcode_when row rotation [11] +
--   c.opcode_when row rotation [9, 12] * 2+
--   c.opcode_when row rotation [13] * 3 =
--   c.store_shift_amount row rotation
-- := rfl
