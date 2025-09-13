import LeanZKCircuit.OpenVM.Circuit
import LeanZKCircuit.Command.Air.define_air

import OpenvmFv.Airs.Alu.MultiplicationCoreAir
import OpenvmFv.Airs.Alu.Rv32BaseAluAdapterAir

set_option linter.unusedVariables false

#define_air "VmAirWrapper_shift" using "openvm_encapsulation" where
  MainSubAir["adapter": "Rv32MultAdapterAir" width := 17]
  MainSubAir["core": "MultiplicationCoreAir_4_8" width := 13]

def Valid_VmAirWrapper_shift.rs2_limbs
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_shift F ExtF)
  (row rotation : ℕ)
: Fin 4 → F :=
  (c.core.ctx row rotation).reads 1

def Valid_VmAirWrapper_shift.rs2_sign
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_shift F ExtF)
  (row rotation : ℕ)
: F :=
  c.rs2_limbs row rotation 2

def Valid_VmAirWrapper_shift.rs2_imm
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_shift F ExtF)
  (row rotation : ℕ)
: F :=
  c.rs2_limbs row rotation 0 +
  c.rs2_limbs row rotation 1 * 256 +
  c.rs2_sign row rotation * 65536

@[openvm_encapsulation]
lemma VmAirWrapper_shift.rs2_imm_def
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_shift F ExtF)
  (row rotation: ℕ)
: c.core.c_0 row rotation +
  c.core.c_1 row rotation * 256 +
  c.core.c_2 row rotation * 65536 =
  c.rs2_imm row rotation
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_shift.rs2_sign_limbs
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_shift F ExtF)
  (row rotation: ℕ)
: (c.core.c_2 row rotation = c.core.c_3 row rotation) =
  (c.rs2_sign row rotation = c.rs2_limbs row rotation 3)
:= rfl

@[openvm_encapsulation]
lemma VmAirWrapper_shift.rs2_sign_check
  [Field F]
  [Field ExtF]
  (c : Valid_VmAirWrapper_shift F ExtF)
  (row rotation: ℕ)
: (1 = c.adapter.rs2_as row rotation ∨ c.core.c_2 row 0 = rotation ∨ 255 = c.core.c_2 row rotation) =
  (1 = c.adapter.rs2_as row rotation ∨ c.rs2_sign row 0 = rotation ∨ 255 = c.rs2_sign row rotation)
:= rfl
