import Mathlib

import OpenvmFv.Constraints.VmAirWrapper_loadstore

lemma inv_2
  (core: Valid_LoadStoreCoreAir_4 FBB)
:
  a * core.inv_2 = 1 ↔ a = 2
:= by
  simp [
    Valid_LoadStoreCoreAir_4.inv_2
  ]
  grind

lemma x_mul_x_sub_1_eq_2
  {x: FBB}
  (h_x: x = 0 ∨ x = 1 ∨ x = 2)
:
  x * (x-1) = 2 ↔ x = 2
:= by
  grind

lemma opcode_when_of_expected_opcode [Field ExtF]
  (air: Valid_VmAirWrapper_loadstore FBB ExtF)
  (row rotation: ℕ)
  (h_opcode: air.core.expected_opcode row 0 = 528)
  (h_row: row ≤ air.last_row)
  (h_constraints: VmAirWrapper_loadstore.constraints.allHold air row h_row)
  (h_is_valid: air.core.is_valid row 0 = 1)
:
  air.core.opcode_when row 0 [opcode] =
  if opcode = 0 then 1 else 0
:= by
  rewrite [VmAirWrapper_loadstore.constraints.allHold_simplified_of_allHold] at h_constraints
  simp [VmAirWrapper_loadstore_constraint_and_interaction_simplification] at h_constraints
  obtain ⟨
    h_interactions,
    h_is_valid_boolean,
    h_flag_0_le_2,
    h_flag_1_le_2,
    h_flag_2_le_2,
    h_flag_3_le_2,
    h_sum_le_2,
    h_sum_1_or_2_of_is_valid,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _,
    _
  ⟩ := h_constraints
  simp [h_is_valid] at *
  simp [Valid_LoadStoreCoreAir_4.sum] at h_sum_1_or_2_of_is_valid
  simp [
    Valid_LoadStoreCoreAir_4.opcode_when,
    Valid_LoadStoreCoreAir_4.opcode_flags,
    Valid_LoadStoreCoreAir_4.sum
  ]
  simp [
    Valid_LoadStoreCoreAir_4.expected_opcode,
    Valid_LoadStoreCoreAir_4.opcode_when
  ] at h_opcode
  fin_cases opcode
  . simp
    rewrite [inv_2 air.core, x_mul_x_sub_1_eq_2 h_flag_0_le_2]

    done
  done
