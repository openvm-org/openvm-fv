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
