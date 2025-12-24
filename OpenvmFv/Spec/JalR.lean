import Mathlib

import OpenvmFv.Airs.Branch.VmAirWrapper_jalr
import OpenvmFv.Constraints.VmAirWrapper_jalr
import OpenvmFv.Fundamentals.Execution
import OpenvmFv.Fundamentals.Interaction

import LeanZKCircuit.Interactions

set_option maxHeartbeats 1_000_000_000

namespace JalLui.NonValidRows

open VmAirWrapper_jalr.constraints

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_jalr FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_jalr.constraints.allHold air row row_in_range)

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
  simp_all [VmAirWrapper_jalr_constraint_and_interaction_simplification]

end JalLui.NonValidRows

namespace JalLui.ValidRows

open VmAirWrapper_jalr.constraints

variable (ExtF : Type) [Field ExtF]
variable (air : Valid_VmAirWrapper_jalr FBB ExtF)
variable (row : ℕ)
variable (row_in_range : row ≤ air.last_row)
variable (constraints : VmAirWrapper_jalr.constraints.allHold air row row_in_range)
variable (axioms : axiomsPerRow air row)
variable (propertiesToAssume : wf_propertiesToAssumePerRow air row)

variable (row_valid : (executionBus_row air row)[0]!.1 = -1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2_000_000 in
include
  row_valid
  constraints
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
  simp [row_valid,
        VmAirWrapper_jalr_constraint_and_interaction_simplification,
        and_assoc,
        show (2013265920 : FBB) = -1 by decide,
        Interaction.ProgramBusEntry.operand_properties,
        Valid_Rv32JalrCoreAir_4.rd_data]
    at pa_exec pa_mem pa_range pa_read pa_bit constraints ⊢
  obtain nw | nw := constraints.2.2.2.2.2.1 <;> simp_all
  omega

section General

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
  simp [VmAirWrapper_jalr_constraint_and_interaction_simplification] at constraints
  obtain ⟨ c0, c1, c2, c3, c4, c5, c6, c7, c8, c9 ⟩ := constraints
  obtain row_valid | row_valid := c1
  . simp_all
  . clear pa_mem pa_range
    simp [row_valid, VmAirWrapper_jalr_constraint_and_interaction_simplification]
      at pa_exec pa_read pa_bit
    simp [Interaction.ProgramBusEntry.operand_properties] at pa_read
    obtain ⟨ instruction, multiplicity, data, h_transpile,
            hm, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8 ⟩ := pa_read
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    have h_bound := Transpiler.pc_bound_of_some h_transpile
    obtain ⟨ imm, rs1, rd, eq_instr, nz_rd ⟩ := Transpiler.transpiler_opcode_565 h_transpile (by simp_all)
    subst instruction; dsimp [Transpiler.transpile_op] at h_transpile
    rw [if_pos (by grind)] at h_transpile
    split_ifs at h_transpile with z_rd
    all_goals
      simp [-Vector.mk_eq] at h_transpile
      obtain ⟨ eq_mul, eq_data ⟩ := h_transpile
      symm at eq_data
      simp_all

include
  row_valid
  constraints
  axioms
  propertiesToAssume in
/-- The constraints entail correct implementation
    of the `jal` opcode
--/
theorem spec_jalr
:
  U32.toBV #v[(air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 0).val,
              (air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 1).val,
              (air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 2).val,
              (air.core.rd_data row 0 (air.adapter.from_state.pc row 0) 3).val]
    =
  BitVec.ofNat 32 (air.adapter.from_state.pc row 0).val + 4#32
  ∧
  BitVec.ofNat 32 (air.core.to_pc row 0) =
    (0xFFFFFFFE#32) &&&
      (U32.toBV #v[(air.core.rs1_data_0 row 0).val,
                   (air.core.rs1_data_1 row 0).val,
                   (air.core.rs1_data_2 row 0).val,
                   (air.core.rs1_data_3 row 0).val] +
       BitVec.signExtend 32 (BitVec.ofNat 12 (air.core.imm row 0)))
:= by
  simp [VmAirWrapper_jalr_constraint_and_interaction_simplification] at row_valid
  have needs_write_eq_is_valid := needs_write_eq_is_valid _ air row row_in_range constraints propertiesToAssume
  obtain ⟨ pa_exec, pa_mem, pa_range, pa_read, pa_bit ⟩ := propertiesToAssume
  rw [allHold_simplified_of_allHold] at constraints
  simp [and_assoc,
        row_valid,
        show (2013265920 : FBB) = -1 by decide,
        needs_write_eq_is_valid,
        VmAirWrapper_jalr_constraint_and_interaction_simplification]
    at pa_exec pa_mem pa_range pa_read pa_bit axioms constraints
  simp [Interaction.ProgramBusEntry.operand_properties] at pa_read
  obtain ⟨ instruction, multiplicity, data, h_transpile,
           hm, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8 ⟩ := pa_read
  have h_alignment := Transpiler.pc_aligned_of_some h_transpile
  have h_bound := Transpiler.pc_bound_of_some h_transpile
  obtain ⟨ imm, rs1, rd, eq_instr, nz_rd ⟩ := Transpiler.transpiler_opcode_565 h_transpile (by grind)
  subst instruction; dsimp [Transpiler.transpile_op] at h_transpile
  rw [if_pos (by grind)] at h_transpile
  split_ifs at h_transpile with z_rd
  all_goals
    simp [-Vector.mk_eq] at h_transpile
    obtain ⟨ hm, hdata ⟩ := h_transpile
    subst data; simp at *
  obtain ⟨ ub_rs1_ptr, ub_rs10, ub_rs11, ub_rs12, ub_rs13,
           ub_rd_ptr, ub_pd0, ub_pd1, ub_pd2, ub_pd3 ⟩ := pa_mem
  obtain ⟨ ub_rd1, ub_rd2, ub_tpc1, ub_tpc0, rest ⟩ := pa_range; clear rest
  obtain ⟨ ub_pc, al_pc, ub_tpc, al_tpc, rest ⟩ := axioms; clear rest
  obtain ⟨ ci, b_imm_sign, b_to_lsb, b_carry, b_carry', rest ⟩ := constraints; clear rest
  obtain ⟨ ub_rdl, ub_rd0 ⟩ := pa_bit
  simp_all [Valid_Rv32JalrCoreAir_4.rd_data,
            Valid_Rv32JalrCoreAir_4.least_sig_limb,
            Valid_Rv32JalrCoreAir_4.composed]
  split_ands
  . simp [← BitVec.toNat_inj, U32.toNat]
    rw [Fin.sub_val_of_le (by grind)]
    simp [Fin.val_add, Fin.val_mul]
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
    repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
    omega
  . clear ub_rdl ub_rd0 ub_rd1 ub_rd2
    have h_ext :
      BitVec.signExtend 32 (BitVec.ofNat 12 (air.core.imm row 0)) =
      BitVec.signExtend 32 (BitVec.ofNat 16 (air.core.imm row 0))
    := by
      rw [← hd4]; clear *-
      simp [Transpiler.utof, Transpiler.sign_extend_16]
      rw [Nat.mod_eq_of_lt (by omega)]
      grind
    rw [h_ext]
    have imm_sign_is_msb :
      air.core.imm_sign row 0 = (BitVec.ofNat 16 (air.core.imm row 0)).msb.toNat
    := by
      rw [← hd8, ← hd4]
      simp [Transpiler.sign_of, Transpiler.utof, Transpiler.sign_extend_16]
      rw [Nat.mod_eq_of_lt (by grind)]
      grind
    clear hd8
    obtain ⟨ i0, eq_i0 ⟩ : ∃ i0, i0 = (air.core.imm row 0).val % 256 := by simp
    obtain ⟨ i1, eq_i1 ⟩ : ∃ i1, i1 = (air.core.imm row 0).val / 256 := by simp
    obtain ⟨ i2, eq_i2 ⟩ : ∃ i2, i2 = (air.core.imm_extended_limb row 0).val % 256 := by simp
    obtain ⟨ i3, eq_i3 ⟩ : ∃ i3, i3 = (air.core.imm_extended_limb row 0).val / 256 := by simp
    have ub_i0 : i0 < 256 := by omega
    have ub_i1 : i1 < 256
    := by
      rw [eq_i1, ← hd4]
      simp [Transpiler.utof, Transpiler.sign_extend_16]
      rw [Nat.mod_eq_of_lt (by grind)]
      omega
    have ub_i2 : i2 < 256 := by omega
    have ub_i3 : i3 < 256
    := by
      simp [eq_i3, Valid_Rv32JalrCoreAir_4.imm_extended_limb, imm_sign_is_msb]
      cases (BitVec.ofNat 16 ↑(air.core.imm row 0)).msb <;> simp
    have eq_imm : (air.core.imm row 0).val = i0 + i1 * 256 := by omega
    have eq_imm_ext : (air.core.imm_extended_limb row 0).val = i2 + i3 * 256 := by omega
    have h_recast :
      U32.toBV #v[ i0, i1, i2, i3 ] =
      BitVec.signExtend 32 (BitVec.ofNat 16 ↑(air.core.imm row 0))
    := by
      rw [← h_ext]
      simp [← BitVec.toInt_inj]
      simp [BitVec.toInt_signExtend_of_le]
      simp [Valid_Rv32JalrCoreAir_4.imm_extended_limb, imm_sign_is_msb] at eq_i2 eq_i3
      subst i0 i1 i2 i3
      simp [U32.toInt, ← U32.msb_3_negative, U32.toNat]
      simp [← hd4, Transpiler.utof, Transpiler.sign_extend_16]
      rw [Nat.mod_eq_of_lt (by omega)]
      trans imm.toInt
      . simp [BitVec.msb_signExtend, BitVec.toInt]
        rw [Int.emod_eq_of_lt (b := 2013265921) (by omega) (by omega)]
        by_cases h_msb : ↑imm.msb
        . simp [BitVec.toNat_signExtend, h_msb]
          simp [BitVec.msb_eq_decide] at h_msb ⊢
          rw [if_neg (by omega)]
          rw [Int.emod_eq_of_lt (b := 65536) (by omega) (by omega)]
          ring_nf
          omega
        . simp [BitVec.toNat_signExtend, h_msb]
          simp [BitVec.msb_eq_decide] at h_msb ⊢
          rw [if_pos (by omega)]
          rw [Int.emod_eq_of_lt (b := 65536) (by omega) (by omega)]
          ring_nf
          omega
      . congr; simp; bv_decide
    rw [← h_recast]; clear h_recast
    have h_eq_and :
      ∀ (b : BitVec 32), 4294967294#32 &&& b = b - b[0].toNat
    := by
      clear *-; intro b
      by_cases b[0] <;> simp_all <;> bv_decide
    have eq_carry :
      (air.core.carry row 0) =
        ((air.core.rs1_data_0 row 0 + air.core.rs1_data_1 row 0 * 256) +
         (i0 + i1 * 256) - (air.core.to_pc_least_sig_bit row 0 + air.core.to_pc_limbs_0 row 0 * 2)) * 2013235201
    := by
      simp [Valid_Rv32JalrCoreAir_4.carry,
            Valid_Rv32JalrCoreAir_4.inv,
            Valid_Rv32JalrCoreAir_4.rs1_limbs_01]
      simp [eq_i0, eq_i1]
      rw [show 256 = (256 : FBB).val by simp]
      rw [← Fin.mod_val, ← Fin.div_val]
      simp [-Fin.mod_val, -Fin.div_val]
      clear *-
      ring_nf; simp [add_assoc]
      ring_nf; rw [add_comm]; simp [add_assoc]
      simp [Fin.ext_iff, Fin.val_add, Fin.val_mul]
      grind
    have eq_carry' :
      (air.core.carry' row 0) =
        ((air.core.rs1_data_2 row 0 + air.core.rs1_data_3 row 0 * 256) +
         (i2 + i3 * 256) + air.core.carry row 0 - (air.core.to_pc_limbs_1 row 0)) * 2013235201
    := by
      simp [Valid_Rv32JalrCoreAir_4.carry',
            Valid_Rv32JalrCoreAir_4.inv,
            Valid_Rv32JalrCoreAir_4.rs1_limbs_23]
      simp [Fin.ext_iff, eq_imm_ext, Fin.val_add, Fin.val_mul]
      omega
    have h_almost_there :
      U32.toBV #v[BitVec.ofNat 8 ↑(air.core.rs1_data_0 row 0),
                  BitVec.ofNat 8 ↑(air.core.rs1_data_1 row 0),
                  BitVec.ofNat 8 ↑(air.core.rs1_data_2 row 0),
                  BitVec.ofNat 8 ↑(air.core.rs1_data_3 row 0)] +
      U32.toBV #v[i0, i1, i2, i3] =
      BitVec.ofNat 32 (air.core.to_pc row 0) + BitVec.ofNat 32 (air.core.to_pc_least_sig_bit row 0)
    := by
      simp [Valid_Rv32JalrCoreAir_4.to_pc, -BitVec.toNat_add]
      trans BitVec.ofNat 32 (((air.core.to_pc_least_sig_bit row 0 + air.core.to_pc_limbs_0 row 0 * 2) + air.core.to_pc_limbs_1 row 0 * 65536) : FBB)
      . clear *- ub_rs10 ub_rs11 ub_rs12 ub_rs13 eq_carry eq_carry'
                 ub_tpc0 ub_tpc1 b_to_lsb b_carry b_carry'
                 ub_i0 ub_i1 ub_i2 ub_i3
        obtain ⟨ tpc0, eq_tpc0 ⟩ : ∃ tpc0, tpc0 = air.core.to_pc_least_sig_bit row 0 + air.core.to_pc_limbs_0 row 0 * 2 := by simp
        rw [← eq_tpc0] at eq_carry ⊢
        have ub_tpc_0 : tpc0.val < 65536 := by grind
        clear b_to_lsb eq_tpc0
        simp [← BitVec.toNat_inj, U32.toNat]
        repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
        simp [Fin.val_add, Fin.val_mul]
        rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
        rcases b_carry with eq_cry | eq_cry <;>
        rcases b_carry' with eq_cry' | eq_cry' <;>
        symm at eq_carry eq_carry'
        . simp_all
          rw [sub_eq_zero] at eq_carry eq_carry'
          symm at eq_carry eq_carry'
          simp_all [Fin.val_add, Fin.val_mul]
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          omega
        . simp_all
          rw [sub_eq_zero] at eq_carry
          symm at eq_carry
          have : air.core.to_pc_limbs_1 row 0 = air.core.rs1_data_2 row 0 + air.core.rs1_data_3 row 0 * 256 + (↑i2 + ↑i3 * 256) - 65536 := by omega
          simp_all
          rw [Fin.sub_val_of_le (by omega)]
          simp [Fin.val_add, Fin.val_mul]
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          have ub_cry'_fbb : (65536 : FBB) ≤ air.core.rs1_data_2 row 0 + (air.core.rs1_data_3 row 0) * 256 + (i2 + i3 * 256) := by omega
          have ub_cry'_nat : (65536 : ℕ) ≤ air.core.rs1_data_2 row 0 + (air.core.rs1_data_3 row 0) * 256 + (i2 + i3 * 256)
          := by
            simp [Fin.le_def, Fin.val_add, Fin.val_mul] at ub_cry'_fbb
            omega
          omega
        . simp_all
          have : tpc0 = air.core.rs1_data_0 row 0 + air.core.rs1_data_1 row 0 * 256 + (↑i0 + ↑i1 * 256) - 65536 := by omega
          rw [sub_eq_zero] at eq_carry'
          symm at eq_carry'
          simp_all [Fin.val_add, Fin.val_mul]
          rw [Fin.sub_val_of_le (by omega)]
          simp [Fin.val_add, Fin.val_mul]
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          have ub_cry_fbb : (65536 : FBB) ≤ air.core.rs1_data_0 row 0 + (air.core.rs1_data_1 row 0) * 256 + (i0 + i1 * 256) := by omega
          have ub_cry_nat : (65536 : ℕ) ≤ air.core.rs1_data_0 row 0 + (air.core.rs1_data_1 row 0) * 256 + (i0 + i1 * 256)
          := by
            simp [Fin.le_def, Fin.val_add, Fin.val_mul] at ub_cry_fbb
            omega
          omega
        . simp_all
          have eq_tpc0' : tpc0 = air.core.rs1_data_0 row 0 + air.core.rs1_data_1 row 0 * 256 + (↑i0 + ↑i1 * 256) - 65536 := by omega
          have eq_tpc1' : air.core.to_pc_limbs_1 row 0 = air.core.rs1_data_2 row 0 + air.core.rs1_data_3 row 0 * 256 + (↑i2 + ↑i3 * 256) + 1 - 65536 := by omega
          simp_all
          rw [Fin.sub_val_of_le (by omega)]
          rw [Fin.sub_val_of_le (by omega)]
          simp [Fin.val_add, Fin.val_mul]
          repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          have ub_cry_fbb : (65536 : FBB) ≤ air.core.rs1_data_0 row 0 + (air.core.rs1_data_1 row 0) * 256 + (i0 + i1 * 256) := by omega
          have ub_cry_nat : (65536 : ℕ) ≤ air.core.rs1_data_0 row 0 + (air.core.rs1_data_1 row 0) * 256 + (i0 + i1 * 256)
          := by
            simp [Fin.le_def, Fin.val_add, Fin.val_mul] at ub_cry_fbb
            omega
          have ub_cry'_fbb : (65536 : FBB) ≤ air.core.rs1_data_2 row 0 + (air.core.rs1_data_3 row 0) * 256 + (i2 + i3 * 256) + 1 := by omega
          have ub_cry'_nat : (65536 : ℕ) ≤ air.core.rs1_data_2 row 0 + (air.core.rs1_data_3 row 0) * 256 + (i2 + i3 * 256) + 1
          := by
            simp [Fin.le_def, Fin.val_add, Fin.val_mul] at ub_cry'_fbb
            omega
          rw [Nat.mul_sub_right_distrib]
          omega
      . simp [← BitVec.toNat_inj, -BitVec.toNat_add]
        repeat rw [BitVec.toNat_add]
        simp [Fin.val_add, Fin.val_mul]
        repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
        omega
    rw [h_almost_there]
    clear h_almost_there eq_carry eq_carry'
    simp [h_eq_and, add_sub_assoc]
    symm; simp [BitVec.eq_sub_iff_add_eq]
    simp [BitVec.getElem_add]
    have : (BitVec.ofNat 32 ↑(air.core.to_pc row 0))[0] = false
    := by
      clear *- ub_tpc al_tpc
      simp only [BitVec.ofNat, Nat.reducePow]
      rw [BitVec.getElem_ofFin]
      obtain ⟨ x, eq_x ⟩ : ∃ x, x = air.core.to_pc row 0 := by simp
      rw [← eq_x] at al_tpc ⊢
      grind
    simp [this]
    rcases b_to_lsb with h_lsb | h_lsb <;> simp [h_lsb]

end General

end JalLui.ValidRows
