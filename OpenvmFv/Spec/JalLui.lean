import Mathlib

import OpenvmFv.Airs.Branch.VmAirWrapper_jallui
import OpenvmFv.Constraints.VmAirWrapper_jallui
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

namespace JalLui.NonValidRows

open VmAirWrapper_jallui.constraints

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_jallui FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_jallui.constraints.allHold air row row_in_range)

variable (row_not_valid : (executionBus_row air row)[0]!.1 = 0)

include
  row_not_valid
  constraints
in
/-- On non-valid rows, all interaction multiplicities
    on the execution, memory, and program buses
    equal zero -/
lemma non_valid_row_exec_mem_program_multiplicities_zero
:
  forall entry,
  entry ∈
    executionBus_row air row
     ++ memoryBus_row air row
     ++ programBus_row air row
    → entry.1 = 0
:= by
  rw [allHold_simplified_of_allHold] at constraints
  simp_all [VmAirWrapper_jallui_constraint_and_interaction_simplification]

end JalLui.NonValidRows

namespace JalLui.ValidRows

open VmAirWrapper_jallui.constraints

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_jallui FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_jallui.constraints.allHold air row row_in_range)
variable (axioms : axiomsPerRow air row)
variable (propertiesToAssume : wf_propertiesToAssumePerRow air row)

variable (row_valid : (executionBus_row air row)[0]!.1 = -1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2_000_000 in
include
  row_valid
  constraints
  axioms
  propertiesToAssume
in
/-- The properties that need to be proven actually hold -/
lemma wf_propertiesToAssert
:
  wf_propertiesToAssertPerRow air row
:= by
  simp [executionBus_row] at row_valid
  rw [allHold_simplified_of_allHold] at constraints

  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  clear pa_range pa_read
  simp [row_valid,
        VmAirWrapper_jallui_constraint_and_interaction_simplification,
        and_assoc,
        Interaction.ProgramBusEntry.operand_properties]
    at axioms pa_exec pa_mem pa_bit constraints ⊢
  grind

section General

include
  row_valid
  constraints
  axioms
  propertiesToAssume in
/-- The constraints entail correct implementation
    of the `lui` opcode
--/
theorem spec_lui
  (h_lui : air.core.expected_opcode row 0 = 561)
:
  U32.toBV #v[(air.core.rd_data_0 row 0).val,
              (air.core.rd_data_1 row 0).val,
              (air.core.rd_data_2 row 0).val,
              (air.core.rd_data_3 row 0).val]
    =
  (BitVec.ofNat 20 ((air.core.imm row 0).val) ++ 0#12)
  ∧
  BitVec.ofNat 32 (air.to_pc row 0) =
    BitVec.ofNat 32 ↑(air.adapter.inner.from_state.pc row 0) + 4#32
:= by
  simp [VmAirWrapper_jallui_constraint_and_interaction_simplification] at row_valid
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  rw [allHold_simplified_of_allHold] at constraints
  clear pa_mem pa_range
  simp [row_valid, VmAirWrapper_jallui_constraint_and_interaction_simplification]
    at pa_exec pa_read pa_bit axioms constraints
  simp [Interaction.ProgramBusEntry.operand_properties] at pa_read
  obtain ⟨ instruction, data, h_transpile,
           hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8 ⟩ := pa_read
  have h_alignment := Transpiler.pc_aligned_of_some h_transpile
  have h_bound := Transpiler.pc_bound_of_some h_transpile
  obtain ⟨ imm, rd, eq_instr, nz_rd ⟩ := Transpiler.transpiler_opcode_561 h_transpile (by grind)
  subst instruction; dsimp [Transpiler.transpile_op] at h_transpile
  rw [if_pos (by grind)] at h_transpile
  split_ifs at h_transpile with z_rd
  all_goals
    simp [-Vector.mk_eq] at h_transpile
    subst data; simp at *
  obtain ⟨ h_lui, h_jal ⟩ : air.core.is_jal row 0 = 0 ∧ air.core.is_lui row 0 = 1
  := by
    rw [← Rv32JalLuiCoreAir_4.is_valid_def] at row_valid
    rw [← Rv32JalLuiCoreAir_4.expected_opcode_def] at h_lui
    grind
  simp [h_lui, and_assoc] at pa_bit
  obtain ⟨ ub_rd0, ub_rd1, ub_rd2, ub_rd3 ⟩ := pa_bit
  simp [← BitVec.toNat_inj, U32.toNat]
  rw [BitVec.toNat_append]
  simp [Nat.shiftLeft_eq_mul_pow]
  repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
  have ub_imm : (air.core.imm row 0).val < 1048576
  := by
    simp [← hd4, Transpiler.utof]
    omega
  rw [Nat.mod_eq_of_lt ub_imm]
  simp_all
  split_ands
  . trans (air.core.imm row 0 * 16).val * 256
    . rw [← constraints.2.2.1,
          ← Rv32JalLuiCoreAir_4.intermed_val_def]
      grind
    . grind
  . simp [Valid_VmAirWrapper_jallui.to_pc, *]
    omega

include
  row_valid
  constraints
  axioms
  propertiesToAssume in
/-- The constraints entail correct implementation
    of the `jal` opcode
--/
theorem spec_jal
  (h_jal : air.core.expected_opcode row 0 = 560)
:
  U32.toBV #v[(air.core.rd_data_0 row 0).val,
              (air.core.rd_data_1 row 0).val,
              (air.core.rd_data_2 row 0).val,
              (air.core.rd_data_3 row 0).val]
    =
  BitVec.ofNat 32 (air.adapter.inner.from_state.pc row 0).val + 4#32
  ∧
  BitVec.ofNat 32 (air.to_pc row 0) =
    BitVec.ofNat 32 ↑(air.adapter.inner.from_state.pc row 0) +
    BitVec.signExtend 32 (BitVec.ofInt 21 (BabyBear.toInt (air.core.imm row 0)))
:= by
  simp [VmAirWrapper_jallui_constraint_and_interaction_simplification] at row_valid
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  rw [allHold_simplified_of_allHold] at constraints
  clear pa_mem pa_range
  simp [row_valid, VmAirWrapper_jallui_constraint_and_interaction_simplification]
    at pa_exec pa_read pa_bit axioms constraints
  simp [Interaction.ProgramBusEntry.operand_properties] at pa_read
  obtain ⟨ instruction, data, h_transpile,
           hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8 ⟩ := pa_read
  have h_alignment := Transpiler.pc_aligned_of_some h_transpile
  have h_bound := Transpiler.pc_bound_of_some h_transpile
  obtain ⟨ imm, rd, eq_instr, nz_rd ⟩ := Transpiler.transpiler_opcode_560 h_transpile (by grind)
  subst instruction; dsimp [Transpiler.transpile_op] at h_transpile
  rw [if_pos (by grind)] at h_transpile
  split_ifs at h_transpile with z_rd
  all_goals
    simp [-Vector.mk_eq] at h_transpile
    subst data; simp at *
  obtain ⟨ ci, bool_lui, bool_jal, lui_rd0, lui_imm, jal_imm, bool_nw, ts ⟩ := constraints
  clear ci ts
  obtain ⟨ h_jal, h_lui ⟩ : air.core.is_jal row 0 = 1 ∧ air.core.is_lui row 0 = 0
  := by
    rw [← Rv32JalLuiCoreAir_4.is_valid_def] at row_valid
    rw [← Rv32JalLuiCoreAir_4.expected_opcode_def] at h_jal
    grind
  simp [h_jal, and_assoc] at pa_bit
  obtain ⟨ ub_rd0, ub_rd1, ub_rd2, ub_rd3, h_rd ⟩ := pa_bit
  simp [← Rv32JalLuiCoreAir_4.intermed_val'_def,
        ← Rv32JalLuiCoreAir_4.intermed_val_def] at jal_imm
  ring_nf at jal_imm
  rw [Valid_VmAirWrapper_jallui.to_pc] at *
  simp_all

  split_ands
  . simp [add_comm (a := (4 : FBB)), Fin.ext_iff, Fin.val_add, Fin.val_mul] at jal_imm
    rw [Nat.mod_eq_of_lt] at jal_imm
    . rw [Nat.mod_eq_of_lt (by grind)] at jal_imm
      simp [← BitVec.toNat_inj, U32.toNat]
      repeat rw [Nat.mod_eq_of_lt (b := 256) (by assumption)]
      omega
    . suffices ub_rd3 : (air.core.rd_data_3 row 0).val < 64
      . omega
      . clear *- ub_rd3 h_rd
        simp [Fin.val_add] at h_rd
        rw [Nat.mod_eq_of_lt (by omega)] at h_rd
        obtain ⟨ x, eq_x ⟩ : ∃ (x : BitVec 9), (air.core.rd_data_3 row 0).val = BitVec.toNat x
        := by
          obtain ⟨ x, eq_x ⟩ : ∃ x, (air.core.rd_data_3 row 0).val = x := by simp
          exists (BitVec.ofNat 9 x)
          simp; omega
        rw [eq_x] at ub_rd3 h_rd ⊢
        clear eq_x air row
        rw [show 192 = (192#9).toNat by simp] at h_rd
        rw [show x.toNat + (192#9).toNat = (x.toNat + (192#9).toNat) % 2 ^ 9 by simp; omega] at h_rd
        rw [← BitVec.toNat_add, ← BitVec.toNat_xor] at h_rd
        rw [BitVec.toNat_inj] at h_rd
        rw [show 256 = (256#9).toNat by simp] at ub_rd3
        rw [← BitVec.lt_def] at ub_rd3
        rw [show 64 = (64#9).toNat by simp]
        rw [← BitVec.lt_def]
        bv_decide
  . have ⟨ lb_imm, ub_imm ⟩ : - 2^20 ≤ BabyBear.toInt (air.core.imm row 0) ∧ BabyBear.toInt (air.core.imm row 0) < 2^20
    := by
      clear *- hd4; symm at hd4
      simp_all [Transpiler.itof, BabyBear.toInt, BitVec.toInt]; clear hd4
      split_ifs with h_imm h_imm_toNat h_imm_toNat <;> simp_all
      . omega
      . omega
      . simp [Fin.sub_def] at *
        omega
      . simp [Fin.sub_def] at *
        omega
    unfold BabyBear.toInt at *
    split_ifs with sgn_imm
    . simp_all
      rw [Fin.val_add]
      rw [Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.signExtend_eq_setWidth_of_msb_false]
      . simp [← BitVec.toNat_inj]
        omega
      . simp [BitVec.msb_eq_decide]; omega
    . simp_all
      trans (BitVec.ofInt 32 ↑(air.adapter.inner.from_state.pc row 0 + air.core.imm row 0))
      . grind
      . have : BitVec.ofNat 32 ↑(air.adapter.inner.from_state.pc row 0) = BitVec.ofInt 32 ↑(air.adapter.inner.from_state.pc row 0) := by grind
        rw [this]; clear this
        have : (air.adapter.inner.from_state.pc row 0 + air.core.imm row 0).val = (air.adapter.inner.from_state.pc row 0).val + (air.core.imm row 0).val - 2013265921
          := by omega
        rw [this]; clear this
        rw [Int.natCast_sub (by omega), Int.natCast_add]
        rw [Nat.cast_ofNat, Int.add_sub_assoc]
        simp [BitVec.ofInt_add]

        obtain ⟨ x, eq_x ⟩ : exists x : ℤ, ↑↑(air.core.imm row 0) - 2013265921 = x := by simp
        replace lb_imm : -1048576 ≤ x := by grind
        simp_all; clear *- lb_imm ub_imm
        simp [← BitVec.toInt_inj, BitVec.signExtend]
        simp [Int.bmod_def]
        omega

include
  row_in_range
  constraints
  propertiesToAssume
in
lemma needs_write_eq_is_valid
:
  air.adapter.needs_write row 0 = air.core.is_valid row 0
:= by
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  rw [allHold_simplified_of_allHold] at constraints
  simp [VmAirWrapper_jallui_constraint_and_interaction_simplification] at constraints
  obtain ⟨ c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 ⟩ := constraints
  obtain row_valid | row_valid := c3
  . simp_all
  . clear pa_mem pa_range
    simp [row_valid, VmAirWrapper_jallui_constraint_and_interaction_simplification]
      at pa_exec pa_read pa_bit
    simp [Interaction.ProgramBusEntry.operand_properties] at pa_read
    obtain ⟨ instruction, data, h_transpile,
             hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8 ⟩ := pa_read
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    have h_bound := Transpiler.pc_bound_of_some h_transpile
    obtain is_lui | is_lui := c1
    . have h_jal : air.core.is_jal row 0 = 1
        := by simp [← Rv32JalLuiCoreAir_4.is_valid_def] at row_valid; grind
      simp_all [← Rv32JalLuiCoreAir_4.expected_opcode_def]
      obtain ⟨ imm, rd, eq_instr, nz_rd ⟩ := Transpiler.transpiler_opcode_560 h_transpile (by grind)
      subst instruction; dsimp [Transpiler.transpile_op] at h_transpile
      rw [if_pos (by grind)] at h_transpile
      split_ifs at h_transpile with z_rd
      all_goals
        simp [-Vector.mk_eq] at h_transpile
        subst data; simp at *
      simp_all
    . have h_jal : air.core.is_jal row 0 = 0
        := by simp [← Rv32JalLuiCoreAir_4.is_valid_def] at row_valid; grind
      simp_all [← Rv32JalLuiCoreAir_4.expected_opcode_def]
      obtain ⟨ imm, rd, eq_instr, nz_rd ⟩ := Transpiler.transpiler_opcode_561 h_transpile (by grind)
      subst instruction; dsimp [Transpiler.transpile_op] at h_transpile
      rw [if_pos (by grind)] at h_transpile
      split_ifs at h_transpile with z_rd
      all_goals
        simp [-Vector.mk_eq] at h_transpile
        subst data; simp at *
      simp_all

end General

end JalLui.ValidRows
