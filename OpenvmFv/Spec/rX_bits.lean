import Mathlib

import LeanRV32D

def read_xreg (reg : Fin 32) : SailM (BitVec 32) :=
match reg.1 with
  | 0 => pure (0#32)
  | 1 => Sail.readReg Register.x1
  | 2 => Sail.readReg Register.x2
  | 3 => Sail.readReg Register.x3
  | 4 => Sail.readReg Register.x4
  | 5 => Sail.readReg Register.x5
  | 6 => Sail.readReg Register.x6
  | 7 => Sail.readReg Register.x7
  | 8 => Sail.readReg Register.x8
  | 9 => Sail.readReg Register.x9
  | 10 => Sail.readReg Register.x10
  | 11 => Sail.readReg Register.x11
  | 12 => Sail.readReg Register.x12
  | 13 => Sail.readReg Register.x13
  | 14 => Sail.readReg Register.x14
  | 15 => Sail.readReg Register.x15
  | 16 => Sail.readReg Register.x16
  | 17 => Sail.readReg Register.x17
  | 18 => Sail.readReg Register.x18
  | 19 => Sail.readReg Register.x19
  | 20 => Sail.readReg Register.x20
  | 21 => Sail.readReg Register.x21
  | 22 => Sail.readReg Register.x22
  | 23 => Sail.readReg Register.x23
  | 24 => Sail.readReg Register.x24
  | 25 => Sail.readReg Register.x25
  | 26 => Sail.readReg Register.x26
  | 27 => Sail.readReg Register.x27
  | 28 => Sail.readReg Register.x28
  | 29 => Sail.readReg Register.x29
  | 30 => Sail.readReg Register.x30
  | _ => Sail.readReg Register.x31

@[simp]
lemma read_xreg_of_0 : read_xreg 0 = pure 0#32 := rfl
@[simp]
lemma read_xreg_of_1 : read_xreg 1 = Sail.readReg Register.x1 := rfl
@[simp]
lemma read_xreg_of_2 : read_xreg 2 = Sail.readReg Register.x2 := rfl
@[simp]
lemma read_xreg_of_3 : read_xreg 3 = Sail.readReg Register.x3 := rfl
@[simp]
lemma read_xreg_of_4 : read_xreg 4 = Sail.readReg Register.x4 := rfl
@[simp]
lemma read_xreg_of_5 : read_xreg 5 = Sail.readReg Register.x5 := rfl
@[simp]
lemma read_xreg_of_6 : read_xreg 6 = Sail.readReg Register.x6 := rfl
@[simp]
lemma read_xreg_of_7 : read_xreg 7 = Sail.readReg Register.x7 := rfl
@[simp]
lemma read_xreg_of_8 : read_xreg 8 = Sail.readReg Register.x8 := rfl
@[simp]
lemma read_xreg_of_9 : read_xreg 9 = Sail.readReg Register.x9 := rfl
@[simp]
lemma read_xreg_of_10 : read_xreg 10 = Sail.readReg Register.x10 := rfl
@[simp]
lemma read_xreg_of_11 : read_xreg 11 = Sail.readReg Register.x11 := rfl
@[simp]
lemma read_xreg_of_12 : read_xreg 12 = Sail.readReg Register.x12 := rfl
@[simp]
lemma read_xreg_of_13 : read_xreg 13 = Sail.readReg Register.x13 := rfl
@[simp]
lemma read_xreg_of_14 : read_xreg 14 = Sail.readReg Register.x14 := rfl
@[simp]
lemma read_xreg_of_15 : read_xreg 15 = Sail.readReg Register.x15 := rfl
@[simp]
lemma read_xreg_of_16 : read_xreg 16 = Sail.readReg Register.x16 := rfl
@[simp]
lemma read_xreg_of_17 : read_xreg 17 = Sail.readReg Register.x17 := rfl
@[simp]
lemma read_xreg_of_18 : read_xreg 18 = Sail.readReg Register.x18 := rfl
@[simp]
lemma read_xreg_of_19 : read_xreg 19 = Sail.readReg Register.x19 := rfl
@[simp]
lemma read_xreg_of_20 : read_xreg 20 = Sail.readReg Register.x20 := rfl
@[simp]
lemma read_xreg_of_21 : read_xreg 21 = Sail.readReg Register.x21 := rfl
@[simp]
lemma read_xreg_of_22 : read_xreg 22 = Sail.readReg Register.x22 := rfl
@[simp]
lemma read_xreg_of_23 : read_xreg 23 = Sail.readReg Register.x23 := rfl
@[simp]
lemma read_xreg_of_24 : read_xreg 24 = Sail.readReg Register.x24 := rfl
@[simp]
lemma read_xreg_of_25 : read_xreg 25 = Sail.readReg Register.x25 := rfl
@[simp]
lemma read_xreg_of_26 : read_xreg 26 = Sail.readReg Register.x26 := rfl
@[simp]
lemma read_xreg_of_27 : read_xreg 27 = Sail.readReg Register.x27 := rfl
@[simp]
lemma read_xreg_of_28 : read_xreg 28 = Sail.readReg Register.x28 := rfl
@[simp]
lemma read_xreg_of_29 : read_xreg 29 = Sail.readReg Register.x29 := rfl
@[simp]
lemma read_xreg_of_30 : read_xreg 30 = Sail.readReg Register.x30 := rfl
@[simp]
lemma read_xreg_of_31 : read_xreg 31 = Sail.readReg Register.x31 := rfl

lemma rX_read_xreg_equiv
  (state)
  (rd_idx : regidx)
  (rd : Fin 32)
  (h_rd : rd_idx = regidx.Regidx (BitVec.ofNat 5 rd))
:
  LeanRV32D.Functions.rX_bits rd_idx state =
  read_xreg rd state
:= by
  unfold LeanRV32D.Functions.rX_bits
  simp [h_rd]
  unfold LeanRV32D.Functions.rX
  dsimp
  simp [LeanRV32D.Functions.regval_from_reg]
  unfold read_xreg
  simp [LeanRV32D.Functions.zero_reg, LeanRV32D.Functions.zeros]
  rfl
