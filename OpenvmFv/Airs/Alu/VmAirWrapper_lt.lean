import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.Alu.LessThanCoreAir
import OpenvmFv.Airs.Alu.Rv32BaseAluAdapterAir

set_option linter.unusedVariables false

#define_air "VmAirWrapper_lt" using "openvm_encapsulation" where
  MainSubAir["adapter": "Rv32BaseAluAdapterAir" width := 19]
  MainSubAir["core": "LessThanCoreAir_4" width := 18]

def Valid_VmAirWrapper_lt.rs2_limbs
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_lt F ExtF)
  (row rotation : ℕ)
: Fin 4 → F :=
  (c.core.ctx row rotation).reads 1

def Valid_VmAirWrapper_lt.rs2_sign
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_lt F ExtF)
  (row rotation : ℕ)
: F :=
  c.rs2_limbs row rotation 2

def Valid_VmAirWrapper_lt.rs2_imm
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_lt F ExtF)
  (row rotation : ℕ)
: F :=
  c.rs2_limbs row rotation 0 +
  c.rs2_limbs row rotation 1 * 256 +
  c.rs2_sign row rotation * 65536

@[openvm_encapsulation]
lemma VmAirWrapper_lt.rs2_imm_def
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_lt F ExtF)
  (row rotation: ℕ)
: c.core.c_0 row rotation +
  c.core.c_1 row rotation * 256 +
  c.core.c_2 row rotation * 65536 =
  c.rs2_imm row rotation
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_lt.rs2_sign_limbs
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_lt F ExtF)
  (row rotation: ℕ)
: (c.core.c_2 row rotation = c.core.c_3 row rotation) =
  (c.rs2_sign row rotation = c.rs2_limbs row rotation 3)
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_lt.rs2_sign_check
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_lt F ExtF)
  (row rotation: ℕ)
: (1 = c.adapter.rs2_as row rotation ∨ c.core.c_2 row 0 = rotation ∨ 255 = c.core.c_2 row rotation) =
  (1 = c.adapter.rs2_as row rotation ∨ c.rs2_sign row 0 = rotation ∨ 255 = c.rs2_sign row rotation)
:= rfl
