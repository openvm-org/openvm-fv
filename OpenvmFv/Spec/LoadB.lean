import Mathlib

import OpenvmFv.Constraints.VmAirWrapper_load_sign_extend

namespace LoadB

  set_option maxHeartbeats 1_000_000_000
  set_option maxRecDepth 2_000_000

  lemma needs_write_of_rd_0 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_opcode: air.core.expected_opcode row 0 = 534)
  :
    air.adapter.rd_rs2_ptr row 0 = 0 ↔
    air.adapter.needs_write row 0 = 0
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2 -- get programBus properties specifically
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ProgramBusEntry.operand_properties
    ] at h_bus_wellformedness
    obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus_wellformedness
    have := Transpiler.transpiler_opcode_534 h_transpile
    simp [h_data.2.2.1, h_opcode] at this
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    have h_bound := Transpiler.pc_bound_of_some h_transpile
    obtain
      ⟨h_needs_write, imm, rs1, rd, h_instruction, h_rd⟩ |
      ⟨h_needs_write, imm, rs1, h_instruction⟩
       := this
    . rewrite [
        ←h_data.2.2.2.2.2.2.2.2.1,
        ←h_data.2.2.2.1,
        h_needs_write
      ]
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [if_pos (by constructor <;> assumption)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [
        ←h_transpile.2,
        Transpiler.ind,
        regidx_to_fin
      ]
      obtain ⟨⟨rd: Fin 32⟩⟩ := rd
      clear *- h_rd
      fin_cases rd <;> grind
    . rewrite [
        ←h_data.2.2.2.2.2.2.2.2.1,
        ←h_data.2.2.2.1,
        h_needs_write
      ]
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [if_pos (by constructor <;> assumption)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [
        ←h_transpile.2,
        Transpiler.ind,
        regidx_to_fin
      ]

  lemma needs_write_of_rd_neq_0 [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_opcode: air.core.expected_opcode row 0 = 534)
  :
    air.adapter.rd_rs2_ptr row 0 ≠ 0 ↔
    air.adapter.needs_write row 0 = 1
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2 -- get programBus properties specifically
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ProgramBusEntry.operand_properties
    ] at h_bus_wellformedness
    obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus_wellformedness
    have := Transpiler.transpiler_opcode_534 h_transpile
    simp [h_data.2.2.1, h_opcode] at this
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    have h_bound := Transpiler.pc_bound_of_some h_transpile
    obtain
      ⟨h_needs_write, imm, rs1, rd, h_instruction, h_rd⟩ |
      ⟨h_needs_write, imm, rs1, h_instruction⟩
       := this
    . rewrite [
        ←h_data.2.2.2.2.2.2.2.2.1,
        ←h_data.2.2.2.1,
        h_needs_write
      ]
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [if_pos (by constructor <;> assumption)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [
        ←h_transpile.2,
        Transpiler.ind,
        regidx_to_fin
      ]
      obtain ⟨⟨rd: Fin 32⟩⟩ := rd
      clear *- h_rd
      fin_cases rd <;> grind
    . rewrite [
        ←h_data.2.2.2.2.2.2.2.2.1,
        ←h_data.2.2.2.1,
        h_needs_write
      ]
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [if_pos (by constructor <;> assumption)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [
        ←h_transpile.2,
        Transpiler.ind,
        regidx_to_fin
      ]

  lemma imm_sign [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_opcode: air.core.expected_opcode row 0 = 534)
  : air.adapter.imm_sign row 0 =
    (BitVec.ofNat 16 (air.adapter.imm row 0)).msb.toNat
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2 -- get programBus properties specifically
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ProgramBusEntry.operand_properties
    ] at h_bus_wellformedness
    obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus_wellformedness
    have := Transpiler.transpiler_opcode_534 h_transpile
    simp [h_data.2.2.1, h_opcode] at this
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    have h_bound := Transpiler.pc_bound_of_some h_transpile
    rewrite [←h_data.2.2.2.2.2.2.2.2.2]
    obtain
      ⟨h_needs_write, imm, rs1, rd, h_instruction, h_rd⟩ |
      ⟨h_needs_write, imm, rs1, h_instruction⟩
       := this
    all_goals {
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [if_pos (by constructor <;> assumption)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      rewrite [←h_data.2.2.2.2.2.1]
      simp [
        ←h_transpile.2,
        Transpiler.sign_of,
        Transpiler.utof,
        Transpiler.sign_extend_16
      ]
      rewrite [Nat.mod_eq_of_lt]
      . have : imm.msb = (BitVec.signExtend 16 imm).msb := by bv_decide
        simp [this]
      . omega
    }

  lemma imm_sign_extend [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  : BitVec.signExtend 32 (BitVec.ofNat 16 (air.adapter.imm row 0)) =
    BitVec.ofNat 16 (air.adapter.imm_extended_limb row 0) ++
    BitVec.ofNat 16 (air.adapter.imm row 0)
  := by
    simp [
      Valid_Rv32LoadStoreAdapterAir.imm_extended_limb,
      imm_sign air row h_bus_wellformedness h_is_valid h_opcode,
      Fin.val_mul
    ]
    rewrite [Nat.mod_eq_of_lt]
    . simp [BitVec.ofNat_mul]
      by_cases h_msb: (BitVec.ofNat 16 ↑(air.adapter.imm row 0)).msb
      all_goals {
        simp [h_msb]
        bv_decide
      }
    . cases (BitVec.ofNat 16 ↑(air.adapter.imm row 0)).msb <;> simp


  lemma mem_as_eq_two [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_opcode: air.core.expected_opcode row 0 = 534)
  : air.adapter.mem_as row 0 = 2
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2 -- get programBus properties specifically
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ProgramBusEntry.operand_properties
    ] at h_bus_wellformedness
    obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus_wellformedness
    have := Transpiler.transpiler_opcode_534 h_transpile
    simp [h_data.2.2.1, h_opcode] at this
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    have h_bound := Transpiler.pc_bound_of_some h_transpile
    rewrite [←h_data.2.2.2.2.2.2.2.1]
    obtain
      ⟨h_needs_write, imm, rs1, rd, h_instruction, h_rd⟩ |
      ⟨h_needs_write, imm, rs1, h_instruction⟩
       := this
    all_goals {
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [if_pos (by constructor <;> assumption)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [←h_transpile.2]
    }

  lemma loadb0_loadb1_exclusive [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    (air.core.opcode_loadb_flag0 row 0 = 1 ∧ air.core.opcode_loadb_flag1 row 0 = 0) ∨
    (air.core.opcode_loadb_flag0 row 0 = 0 ∧ air.core.opcode_loadb_flag1 row 0 = 1)
  := by
    rewrite [VmAirWrapper_load_sign_extend.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_constraints
    obtain ⟨ t1, h0, h1, h2, t2 ⟩ := h_constraints
    clear *- h0 h1 h2 h_opcode
    simp [← LoadSignExtendCoreAir_4.expected_opcode_def] at h_opcode
    grind

  lemma loadb0_loadb1_sum [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.opcode_loadb_flag0 row 0 + air.core.opcode_loadb_flag1 row 0 = 1
  := by
    rewrite [VmAirWrapper_load_sign_extend.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_constraints
    obtain ⟨ t1, h0, h1, h2, t2 ⟩ := h_constraints
    clear *- h0 h1 h2 h_opcode
    simp [← LoadSignExtendCoreAir_4.expected_opcode_def] at h_opcode
    grind

  lemma loadh_eq_zero [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.opcode_loadh_flag row 0 = 0
  := by
    rewrite [VmAirWrapper_load_sign_extend.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_constraints
    obtain ⟨ t1, h0, h1, h2, t2 ⟩ := h_constraints
    clear *- h0 h1 h2 h_opcode
    simp [← LoadSignExtendCoreAir_4.expected_opcode_def] at h_opcode
    grind

  lemma shift_msb_is_bool [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.shift_most_sig_bit row 0 = 0 ∨ air.core.shift_most_sig_bit row 0 = 1
  := by
    rewrite [VmAirWrapper_load_sign_extend.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_constraints
    grind

  lemma is_load_eq_one [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.is_load row 0 = 1
  := by
    simpa [Valid_LoadSignExtendCoreAir_4.is_load]

  lemma carries_are_bool [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    (air.adapter.carry row 0 = 0 ∨ air.adapter.carry row 0 = 1) ∧
    (air.adapter.carry' row 0 = 0 ∨ air.adapter.carry' row 0 = 1)
  := by
    rewrite [VmAirWrapper_load_sign_extend.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_constraints
    grind

  lemma msl_eq_rd1 [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.most_sig_limb row 0 =
      if air.core.opcode_loadb_flag0 row 0 = 1
        then air.core.shifted_read_data_0 row 0
        else air.core.shifted_read_data_1 row 0
  := by
    have loadb0_loadb1_exclusive := loadb0_loadb1_exclusive air row h_opcode h_row h_constraints h_is_valid
    have loadh_eq_zero := loadh_eq_zero air row h_opcode h_row h_constraints h_is_valid
    rewrite [VmAirWrapper_load_sign_extend.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [← LoadSignExtendCoreAir_4.most_sig_limb_def]
    grind

  lemma shifted_read_data [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  :
    air.core.shifted_read_data_0 row 0 =
      (if (air.core.shift_most_sig_bit row 0 = 0)
         then air.core.read_data row 0 0
         else air.core.read_data row 0 2) ∧
    air.core.shifted_read_data_1 row 0 =
      (if (air.core.shift_most_sig_bit row 0 = 0)
         then air.core.read_data row 0 1
         else air.core.read_data row 0 3)
  := by
    rewrite [VmAirWrapper_load_sign_extend.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_constraints
    grind [← LoadSignExtendCoreAir_4.read_data_0_def,
           ← LoadSignExtendCoreAir_4.read_data_1_def,
           ← LoadSignExtendCoreAir_4.read_data_2_def,
           ← LoadSignExtendCoreAir_4.read_data_3_def]

  lemma data_msb_is_msb [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.core.data_most_sig_bit row 0 =
      if air.core.opcode_loadb_flag0 row 0 = 1
        then (BitVec.ofNat 8 (air.core.shifted_read_data_0 row 0)).msb.toNat
        else (BitVec.ofNat 8 (air.core.shifted_read_data_1 row 0)).msb.toNat
  := by
    have msl_eq_rd1 := msl_eq_rd1 air row h_opcode h_row h_constraints h_is_valid
    obtain ⟨ shifted_read_data_0, shifted_read_data_1 ⟩ := shifted_read_data air row h_opcode h_row h_constraints h_is_valid
    obtain ⟨ ub_rd0, ub_rd1 ⟩ : (air.core.read_data row 0 1).val < 256 ∧ (air.core.read_data row 0 3).val < 256
    := by
      simp [
        VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
        h_is_valid
      ] at h_bus_wellformedness
      grind
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.1
    rewrite [VmAirWrapper_load_sign_extend.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid
    ] at h_constraints h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.1
    simp [msl_eq_rd1, shifted_read_data_1] at h_bus_wellformedness ⊢
    obtain h_msb | h_msb := h_constraints.2.2.2.2.2.1 <;>
      simp [h_msb] at h_bus_wellformedness ⊢ <;>
      obtain h_msb | h_msb := h_constraints.2.2.2.2.1 <;>
      simp [h_msb] at h_bus_wellformedness ⊢ <;>
      simp [BitVec.msb_eq_decide]
    . split_ifs <;> simp_all <;> rw [decide_eq_false (by omega)] <;> simp
    . split_ifs <;> simp_all <;> rw [decide_eq_true (by omega)] <;> simp
    . split_ifs <;> simp_all <;> rw [decide_eq_false (by omega)] <;> simp
    . split_ifs <;> simp_all <;> rw [decide_eq_true (by omega)] <;> simp

  lemma limb_mask_is_msb_extend [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.core.limb_mask row 0 =
      if air.core.opcode_loadb_flag0 row 0 = 1
        then ((BitVec.ofNat 8 (air.core.shifted_read_data_0 row 0)).msb.toNat : FBB) * 255
        else ((BitVec.ofNat 8 (air.core.shifted_read_data_1 row 0)).msb.toNat : FBB) * 255
  := by
    simp [← LoadSignExtendCoreAir_4.limb_mask_def,
          data_msb_is_msb air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness]

  @[simp]
  def load_data
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
  :
    FBB
  :=
    if air.core.opcode_loadb_flag0 row 0 = 1 ∧ air.core.shift_most_sig_bit row 0 = 0 then air.core.read_data row 0 0 else
    if air.core.shift_most_sig_bit row 0 = 0 ∧ air.core.shift_most_sig_bit row 0 = 0 then air.core.read_data row 0 1 else
    if air.core.opcode_loadb_flag0 row 0 = 1 ∧ air.core.shift_most_sig_bit row 0 = 1 then air.core.read_data row 0 2 else
    air.core.read_data row 0 3

  lemma write_data_eq [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.core.write_data row 0 0 = load_data air row ∧
    air.core.write_data row 0 1 = ((BitVec.ofNat 8 (load_data air row)).msb.toNat : FBB) * 255 ∧
    air.core.write_data row 0 2 = ((BitVec.ofNat 8 (load_data air row)).msb.toNat : FBB) * 255 ∧
    air.core.write_data row 0 3 = ((BitVec.ofNat 8 (load_data air row)).msb.toNat : FBB) * 255
  := by
    have loadb0_loadb1_exclusive := loadb0_loadb1_exclusive air row h_opcode h_row h_constraints h_is_valid
    have loadh_eq_zero := loadh_eq_zero air row h_opcode h_row h_constraints h_is_valid
    have shift_msb_is_bool := shift_msb_is_bool air row h_opcode h_row h_constraints h_is_valid
    have ⟨ sd0, sd1 ⟩ := shifted_read_data air row h_opcode h_row h_constraints h_is_valid
    simp [Valid_LoadSignExtendCoreAir_4.write_data,
          limb_mask_is_msb_extend air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness]
    grind

  lemma write_data_correct [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    U32.toBV
        #v[
          air.core.write_data row 0 0,
          air.core.write_data row 0 1,
          air.core.write_data row 0 2,
          air.core.write_data row 0 3,
        ] =
      (BitVec.extend (BitVec.ofNat 8 (load_data air row)) 32 true)
  := by
    obtain ⟨ wd0, wd1, wd2, wd3 ⟩ := write_data_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    clear h_constraints h_bus_wellformedness
    simp [*, BitVec.extend, ← BitVec.toInt_inj]
    split_ifs with h0 h1 h2
    all_goals {
      rw [BitVec.toInt_signExtend_of_le (by simp)]
      simp [U32.toInt, ← U32.msb_3_negative, U32.toNat, BitVec.msb_eq_decide, BitVec.toInt]
      split_ifs with h_if_msb h_if h_if
      . rw [decide_eq_false (by omega)] at h_if_msb; simp at h_if_msb
      . rw [decide_eq_true (by omega)]; simp; omega
      . rw [decide_eq_false (by omega)]; simp
      . rw [decide_eq_true (by omega)] at h_if_msb; simp at h_if_msb
    }

  lemma shift_eqs [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.shift_amount row 0 =
      (if air.core.opcode_loadb_flag0 row 0 = 1 ∧ air.core.shift_most_sig_bit row 0 = 0 then 0 else
       if air.core.shift_most_sig_bit row 0 = 0 ∧ air.core.shift_most_sig_bit row 0 = 0 then 1 else
       if air.core.opcode_loadb_flag0 row 0 = 1 ∧ air.core.shift_most_sig_bit row 0 = 1 then 2 else 3) ∧
    air.core.load_shift_amount row 0 =
      (if air.core.opcode_loadb_flag0 row 0 = 1 ∧ air.core.shift_most_sig_bit row 0 = 0 then 0 else
       if air.core.shift_most_sig_bit row 0 = 0 ∧ air.core.shift_most_sig_bit row 0 = 0 then 1 else
       if air.core.opcode_loadb_flag0 row 0 = 1 ∧ air.core.shift_most_sig_bit row 0 = 1 then 2 else 3) ∧
    air.core.store_shift_amount = 0
  := by
    have shift_msb_is_bool := shift_msb_is_bool air row h_opcode h_row h_constraints h_is_valid
    have loadb0_loadb1_exclusive := loadb0_loadb1_exclusive air row h_opcode h_row h_constraints h_is_valid
    have loadh_eq_zero := loadh_eq_zero air row h_opcode h_row h_constraints h_is_valid
    rw [Valid_VmAirWrapper_load_sign_extend.shift_amount,
        Valid_LoadSignExtendCoreAir_4.load_shift_amount,
        Valid_LoadSignExtendCoreAir_4.store_shift_amount]
    split_ands <;> [ grind; grind; rfl ]

  lemma read_ptr_eq [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  :
    air.read_ptr row 0 = air.adapter.mem_ptr row 0 - air.shift_amount row 0
  := by
    obtain ⟨ sh, lsh, rsh ⟩ := shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    have is_load_eq_one := is_load_eq_one air row h_is_valid
    simp [Valid_VmAirWrapper_load_sign_extend.read_ptr, *]

  lemma read_as [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.read_as row 0 = air.adapter.mem_as row 0
  := by
    unfold Valid_VmAirWrapper_load_sign_extend.read_as
    simp_all [Valid_LoadSignExtendCoreAir_4.is_load]

  lemma write_as [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.write_as row 0 = 1
  := by
    unfold Valid_VmAirWrapper_load_sign_extend.write_as
    simp_all [Valid_LoadSignExtendCoreAir_4.is_load]

  lemma write_ptr [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.write_ptr row 0 = air.adapter.rd_rs2_ptr row 0
  := by
    unfold Valid_VmAirWrapper_load_sign_extend.write_ptr
    simp [*, Valid_LoadSignExtendCoreAir_4.is_load, Valid_LoadSignExtendCoreAir_4.store_shift_amount]

  lemma rangeCheckerBus_row [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : VmAirWrapper_load_sign_extend.constraints.rangeCheckerBus_row air row = [
    (1, [air.core.most_sig_limb row 0 - air.core.data_most_sig_bit row 0 * 128, 7]),
    (1, [air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (1, [air.adapter.rs1_aux_cols.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
    (1, [(air.adapter.mem_ptr_limbs_0 row 0 - air.shift_amount row 0) * 1509949441, 14]),
    (1, [air.adapter.mem_ptr_limbs_1 row 0, 13]),
    (1, [air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (1, [air.adapter.read_data_aux.base.timestamp_lt_aux.lower_decomp_1 row 0, 12]),
    (if air.adapter.rd_rs2_ptr row 0 = 0 then 0 else 1, [air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_0 row 0, 17]),
    (if air.adapter.rd_rs2_ptr row 0 = 0 then 0 else 1, [air.adapter.write_base_aux.timestamp_lt_aux.lower_decomp_1 row 0, 12])
  ] := by
    unfold VmAirWrapper_load_sign_extend.constraints.rangeCheckerBus_row
    simp [h_is_valid, Valid_VmAirWrapper_load_sign_extend.shift_amount, Valid_LoadSignExtendCoreAir_4.store_shift_amount]
    split_ifs with h_rd
    . simp [(needs_write_of_rd_0 air row h_bus_wellformedness h_is_valid h_opcode).mp h_rd]
    . simp [(needs_write_of_rd_neq_0 air row h_bus_wellformedness h_is_valid h_opcode).mp h_rd]

  lemma mem_ptr_limbs_0_range [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : (air.adapter.mem_ptr_limbs_0 row 0 - air.shift_amount row 0) < 2^16
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.1
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
    ] at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.1
    clear *- h_bus_wellformedness

    have : (1509949441: FBB) = 4⁻¹ := eq_inv_of_mul_eq_one_left rfl

    rewrite [this] at h_bus_wellformedness
    clear this
    simp [Valid_VmAirWrapper_load_sign_extend.shift_amount, Valid_LoadSignExtendCoreAir_4.store_shift_amount] at *

    rewrite [show 16384 = (16384: FBB).val by simp, ←Fin.lt_def] at h_bus_wellformedness
    rewrite [
      show (air.adapter.mem_ptr_limbs_0 row 0 - air.core.load_shift_amount row 0) = (air.adapter.mem_ptr_limbs_0 row 0 - air.core.load_shift_amount row 0) * 4⁻¹ * 4 by simp
    ]
    obtain ⟨ diff, eq_diff ⟩ : ∃ diff, diff = air.adapter.mem_ptr_limbs_0 row 0 - air.core.load_shift_amount row 0 := by simp
    rw [← eq_diff] at h_bus_wellformedness ⊢
    clear eq_diff
    grind

  lemma mem_ptr_limbs_1_range [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.adapter.mem_ptr_limbs_1 row 0 < 2^13
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.1
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
    ] at h_bus_wellformedness
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2.2.1
    grind

  lemma mem_ptr_range [Field ExtF]
    (air : Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row : ℕ)
    (h_opcode : air.core.expected_opcode row 0 = 534)
    (h_row : row ≤ air.last_row)
    (h_constraints : VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid : air.core.is_valid row 0 = 1)
  : air.adapter.mem_ptr row 0 - air.shift_amount row 0 < 2^29
  := by
    unfold Valid_Rv32LoadStoreAdapterAir.mem_ptr
    have hm0 := mem_ptr_limbs_0_range air row h_bus_wellformedness h_is_valid
    have hm1 := mem_ptr_limbs_1_range air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
    rw [add_sub_assoc, ← add_comm_sub]
    obtain ⟨ diff, eq_diff ⟩ : ∃ diff, diff = air.adapter.mem_ptr_limbs_0 row 0 - air.shift_amount row 0 := by simp
    rw [← eq_diff] at hm0 ⊢
    clear eq_diff
    grind

  lemma rs1_data_0_range [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rs1_data_0 row 0 < 256
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920: FBB) = -1 by decide
    ] at h_bus_wellformedness
    rewrite [
      show 256 = (256:FBB).val by decide,
    ] at h_bus_wellformedness
    exact Fin.lt_def.mpr h_bus_wellformedness.1.2.1

  lemma rs1_data_1_range [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rs1_data_1 row 0 < 256
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920: FBB) = -1 by decide
    ] at h_bus_wellformedness
    rewrite [
      show 256 = (256:FBB).val by decide,
    ] at h_bus_wellformedness
    exact Fin.lt_def.mpr h_bus_wellformedness.1.2.2.1

  lemma rs1_data_2_range [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rs1_data_2 row 0 < 256
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920: FBB) = -1 by decide
    ] at h_bus_wellformedness
    rewrite [
      show 256 = (256:FBB).val by decide,
    ] at h_bus_wellformedness
    exact Fin.lt_def.mpr h_bus_wellformedness.1.2.2.2.1

  lemma rs1_data_3_range [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rs1_data_3 row 0 < 256
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920: FBB) = -1 by decide
    ] at h_bus_wellformedness
    rewrite [
      show 256 = (256:FBB).val by decide,
    ] at h_bus_wellformedness
    exact Fin.lt_def.mpr h_bus_wellformedness.1.2.2.2.2

  lemma rs1_lower_half_range [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.rs1_data_0 row 0 + air.adapter.rs1_data_1 row 0 * 256 < 65536
  := by
    have h_data_0 := rs1_data_0_range air row h_is_valid h_bus_wellformedness
    have h_data_1 := rs1_data_1_range air row h_is_valid h_bus_wellformedness
    clear *- h_data_0 h_data_1
    grind

  lemma imm_range [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode : air.core.expected_opcode row 0 = 534)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  : air.adapter.imm row 0 < 65536
  := by
    replace h_bus_wellformedness := h_bus_wellformedness.2.2.2 -- get programBus properties specifically
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ProgramBusEntry.operand_properties
    ] at h_bus_wellformedness
    obtain ⟨instruction, multiplicity, data, h_transpile, h_data⟩ := h_bus_wellformedness
    have := Transpiler.transpiler_opcode_534 h_transpile
    simp [h_data.2.2.1, h_opcode] at this
    have h_alignment := Transpiler.pc_aligned_of_some h_transpile
    have h_bound := Transpiler.pc_bound_of_some h_transpile
    obtain
      ⟨h_needs_write, imm, rs1, rd, h_instruction, h_rd⟩ |
      ⟨h_needs_write, imm, rs1, h_instruction⟩
      := this
    all_goals {
      rewrite [←h_data.2.2.2.2.2.1]
      rewrite [h_instruction] at h_transpile
      unfold Transpiler.transpile_op at h_transpile
      rewrite [if_pos (by constructor <;> assumption)] at h_transpile
      dsimp at h_transpile
      simp [-Vector.mk_eq] at h_transpile
      simp [
        ←h_transpile.2,
        Transpiler.sign_extend_16,
        Transpiler.utof,
        Fin.lt_def
      ]
      rewrite [Nat.mod_eq_of_lt (by omega)]
      omega
    }

lemma imm_extend_range [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : air.adapter.imm_extended_limb row 0 < 65536
  := by
    rewrite [VmAirWrapper_load_sign_extend.constraints.allHold_simplified_of_allHold] at h_constraints
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
    ] at h_constraints
    rw [← Rv32LoadStoreAdapterAir.imm_extended_limb_def]
    omega

  set_option maxHeartbeats 1_000_000_000 in
  lemma mem_ptr_eq_imm_plus_rs1 [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_is_valid: air.core.is_valid row 0 = 1)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
  : BitVec.ofNat 32 (air.adapter.mem_ptr row 0) =
    BitVec.signExtend 32 (BitVec.ofNat 16 (air.adapter.imm row 0)) +
    U32.toBV #v[
      (air.adapter.rs1_data_0 row 0).val,
      (air.adapter.rs1_data_1 row 0).val,
      (air.adapter.rs1_data_2 row 0).val,
      (air.adapter.rs1_data_3 row 0).val
    ]
  := by
    have h_carry_def := Rv32LoadStoreAdapterAir.carry_def air.adapter row 0
    have h_carry'_def := Rv32LoadStoreAdapterAir.carry'_def air.adapter row 0
    have h_rs1_data_0 := rs1_data_0_range air row h_is_valid h_bus_wellformedness
    have h_rs1_data_1 := rs1_data_1_range air row h_is_valid h_bus_wellformedness
    have h_rs1_data_2 := rs1_data_2_range air row h_is_valid h_bus_wellformedness
    have h_rs1_data_3 := rs1_data_3_range air row h_is_valid h_bus_wellformedness
    have h_imm_range := imm_range air row h_opcode h_is_valid h_bus_wellformedness
    have h_imm_ext_range := imm_extend_range air row h_row h_constraints h_is_valid
    have h_mem_ptr_0_range := mem_ptr_limbs_0_range air row h_bus_wellformedness h_is_valid
    have h_mem_ptr_1_range := mem_ptr_limbs_1_range air row h_opcode h_row h_constraints h_bus_wellformedness h_is_valid
    simp at h_mem_ptr_0_range h_mem_ptr_1_range
    have ⟨ b_carry, b_carry' ⟩ := carries_are_bool air row h_opcode h_row h_constraints h_is_valid
    obtain ⟨ sh, lsh, rsh ⟩ := shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
    rw [← Rv32LoadStoreAdapterAir.mem_ptr_def, imm_sign_extend air row h_opcode h_is_valid h_bus_wellformedness]
    simp [U32.toBV]
    rw [← BitVec.toNat_inj]
    repeat rw [BitVec.toNat_add]
    simp
    rw [Nat.mod_eq_of_lt (by omega)]
    repeat (rw [BitVec.toNat_append]; simp; rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)])
    repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
    repeat rw [Nat.mod_eq_of_lt (b := 65536) (by omega)]
    repeat rw [Nat.shiftLeft_eq_mul_pow]
    ring_nf
    trans
      (((air.adapter.limbs_01 row 0 + air.adapter.imm row 0).val) +
       ((air.adapter.limbs_23 row 0 + air.adapter.imm_extended_limb row 0).val) * 65536) % 4294967296
    . have ub_l01 : air.adapter.limbs_01 row 0 < 65536
        := by rw [← Rv32LoadStoreAdapterAir.limbs_01_def]; clear *- h_rs1_data_0 h_rs1_data_1; grind
      have ub_l23 : air.adapter.limbs_23 row 0 < 65536
        := by rw [← Rv32LoadStoreAdapterAir.limbs_23_def]; clear *- h_rs1_data_2 h_rs1_data_3; grind
      simp [Valid_VmAirWrapper_load_sign_extend.shift_amount, Valid_LoadSignExtendCoreAir_4.store_shift_amount] at *
      clear h_rs1_data_0 h_rs1_data_1 h_rs1_data_2 h_rs1_data_3
            h_constraints h_bus_wellformedness h_is_valid h_row h_opcode
      rw [← h_carry_def] at h_carry'_def
      rcases b_carry with hc | hc <;> rcases b_carry' with hc' | hc' <;> simp_all
      . rw [sub_eq_zero] at h_carry_def h_carry'_def
        symm at h_carry_def h_carry'_def
        simp [h_carry_def, h_carry'_def] at *
        simp [Fin.val_add, Fin.val_mul]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      . rw [sub_eq_zero] at h_carry_def
        replace h_carry'_def := eq_add_of_sub_eq h_carry'_def
        rw [← h_carry_def, h_carry'_def]
        simp [Fin.val_add, Fin.val_mul]
        repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
        ring_nf
        rw [Nat.mod_eq_sub_mod (by omega)]
        omega
      . rw [sub_eq_zero] at h_carry'_def
        replace h_carry_def := eq_add_of_sub_eq h_carry_def
        rw [h_carry_def, ← h_carry'_def]
        ring_nf
        simp [Fin.val_add, Fin.val_mul]
        split_ifs at h_mem_ptr_0_range <;>
        repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] <;>
        omega
      . replace h_carry_def := eq_add_of_sub_eq h_carry_def
        replace h_carry'_def := eq_add_of_sub_eq h_carry'_def
        replace h_carry'_def := eq_sub_of_add_eq h_carry'_def
        rw [h_carry_def, h_carry'_def]
        simp [Fin.val_add, Fin.val_mul]
        rw [Fin.sub_val_of_le (by omega)]
        simp [Fin.val_add]
        split_ifs at h_mem_ptr_0_range <;>
        repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)] <;>
        omega
    . rw [← Rv32LoadStoreAdapterAir.limbs_01_def, ← Rv32LoadStoreAdapterAir.limbs_23_def]
      simp [Fin.val_add, Fin.val_mul]
      repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
      ring_nf

  def program_of_instruction
    (pc : FBB)
    (imm : BitVec 12) (rs1 rd:  regidx)
  : List (FBB × List FBB) := [
    (
      1, [
        pc,
        534,
        Transpiler.ind rd,
        Transpiler.ind rs1,
        Transpiler.utof (Transpiler.sign_extend_16 imm),
        1,
        2,
        if rd == regidx.Regidx 0 then 0 else 1,
        Transpiler.sign_of imm
      ]
    )
  ]

  def memory_of_instruction
    (imm : BitVec 12) (rs1 rd :  regidx)
    (rs1_data read_data : U32)
    (prev_data : Vector FBB 4)
    (rs1_prev_timestamp : FBB)
    (read_prev_timestamp : FBB)
    (write_prev_timestamp : FBB)
    (timestamp : FBB)
    (shift : FBB)
  : List (FBB × List FBB) := [
      (-1,
        [
          1,
          4 * rs1.1.toNat,
          rs1_data[0].toNat,
          rs1_data[1].toNat,
          rs1_data[2].toNat,
          rs1_data[3].toNat,
          rs1_prev_timestamp
        ]
      ),
      (1,
        [
          1,
          4 *rs1.1.toNat,
          rs1_data[0].toNat,
          rs1_data[1].toNat,
          rs1_data[2].toNat,
          rs1_data[3].toNat,
          timestamp
        ]
      ),
      (-1,
        [
          2,
          (BitVec.signExtend 32 imm + rs1_data.toBV).toNat - shift.val,
          read_data[0].toNat,
          read_data[1].toNat,
          read_data[2].toNat,
          read_data[3].toNat,
          read_prev_timestamp
        ]
      ),
      (1,
        [
          2,
          (BitVec.signExtend 32 imm + rs1_data.toBV).toNat - shift.val,
          read_data[0].toNat,
          read_data[1].toNat,
          read_data[2].toNat,
          read_data[3].toNat,
          timestamp + 1
        ]
      ),
      (if rd.1 = 0 then 0 else -1,
        [
          1,
          4 * rd.1.toNat,
          prev_data[0].toNat,
          prev_data[1].toNat,
          prev_data[2].toNat,
          prev_data[3].toNat,
          write_prev_timestamp
        ]
      ),
      (if rd.1 = 0 then 0 else 1,
        [
          1,
          4 * rd.1.toNat,
          if (shift = 0) then read_data[0].toNat else if (shift = 1) then read_data[1].toNat else if (shift = 2) then read_data[2].toNat else read_data[3].toNat,
          if (shift = 0) then (BitVec.ofNat 8 read_data[0].toNat).msb.toNat * 255 else if (shift = 1) then (BitVec.ofNat 8 read_data[1].toNat).msb.toNat * 255 else if (shift = 2) then (BitVec.ofNat 8 read_data[2].toNat).msb.toNat * 255 else (BitVec.ofNat 8 read_data[3].toNat).msb.toNat * 255,
          if (shift = 0) then (BitVec.ofNat 8 read_data[0].toNat).msb.toNat * 255 else if (shift = 1) then (BitVec.ofNat 8 read_data[1].toNat).msb.toNat * 255 else if (shift = 2) then (BitVec.ofNat 8 read_data[2].toNat).msb.toNat * 255 else (BitVec.ofNat 8 read_data[3].toNat).msb.toNat * 255,
          if (shift = 0) then (BitVec.ofNat 8 read_data[0].toNat).msb.toNat * 255 else if (shift = 1) then (BitVec.ofNat 8 read_data[1].toNat).msb.toNat * 255 else if (shift = 2) then (BitVec.ofNat 8 read_data[2].toNat).msb.toNat * 255 else (BitVec.ofNat 8 read_data[3].toNat).msb.toNat * 255,
          timestamp + 2
        ]
      )
    ]

  lemma executionBus_row [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : VmAirWrapper_load_sign_extend.constraints.executionBus_row air row = [
      (-1, [air.adapter.from_state.pc row 0, air.adapter.from_state.timestamp row 0]),
      (1, [air.adapter.from_state.pc row 0 + 4, air.adapter.from_state.timestamp row 0 + 3])
    ]
  := by
    unfold VmAirWrapper_load_sign_extend.constraints.executionBus_row
    simp [h_is_valid, Valid_VmAirWrapper_load_sign_extend.to_pc]

  attribute [-simp]
    Fin.natCast_eq_zero

  set_option maxHeartbeats 2_000_000 in
  set_option synthInstance.maxHeartbeats 2_000_000 in
  lemma bus_interface [Field ExtF]
    (air: Valid_VmAirWrapper_load_sign_extend FBB ExtF)
    (row: ℕ)
    (h_opcode: air.core.expected_opcode row 0 = 534)
    (h_row: row ≤ air.last_row)
    (h_constraints: VmAirWrapper_load_sign_extend.constraints.allHold air row h_row)
    (h_axioms : VmAirWrapper_load_sign_extend.constraints.axiomsPerRow air row)
    (h_bus_wellformedness : VmAirWrapper_load_sign_extend.constraints.wf_propertiesToAssumePerRow air row)
    (h_is_valid: air.core.is_valid row 0 = 1)
  : ∃ pc imm rs1 rd rs1_data read_data prev_data rs1_prev_timestamp read_prev_timestamp write_prev_timestamp timestamp shift,
    VmAirWrapper_load_sign_extend.constraints.programBus_row air row =
    program_of_instruction pc imm rs1 rd ∧
    VmAirWrapper_load_sign_extend.constraints.memoryBus_row air row =
    memory_of_instruction
      imm
      rs1
      rd
      rs1_data
      read_data
      prev_data
      rs1_prev_timestamp
      read_prev_timestamp
      write_prev_timestamp
      timestamp
      shift ∧
    (rd.1 ≠ 0 →
      prev_data[0].val < 256 ∧
      prev_data[1].val < 256 ∧
      prev_data[2].val < 256 ∧
      prev_data[3].val < 256)
    -- we may want to add extra constraints about the timestamps in here too
  := by
    have h_bus_wellformedness' := h_bus_wellformedness.2.2.2
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      Interaction.ProgramBusEntry.operand_properties
    ] at h_bus_wellformedness'
    obtain ⟨ inst, a, b, h_transpile, h_a, h_b0, h_b1, h_b2, h_b3, h_b4, h_b5, h_b6, h_b7, h_b8 ⟩ := h_bus_wellformedness'
    have := Transpiler.transpiler_opcode_534 h_transpile (by simp; grind)
    simp [*] at this
    have h_eq_b : b = #v[b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], b[8]]
      := by clear *-; ext i h_i; interval_cases i <;> simp
    simp [h_b0, h_b1, h_b2, h_b3, h_b4, h_b5, h_b6, h_b7, h_b8] at h_eq_b

    have h_imm_range := imm_range air row h_opcode h_is_valid h_bus_wellformedness
    have h_imm_ext_range := imm_extend_range air row h_row h_constraints h_is_valid
    have h_imm_sign := imm_sign air row h_bus_wellformedness h_is_valid h_opcode
    have h_mem_as := mem_as_eq_two air row h_bus_wellformedness h_is_valid h_opcode
    have h_write_ptr := write_ptr air row h_is_valid
    have h_read_as := read_as air row h_is_valid
    have h_write_as := write_as air row h_is_valid

    have h_bus_wellformedness' := h_bus_wellformedness.2.1
    simp [
      VmAirWrapper_load_sign_extend_constraint_and_interaction_simplification,
      h_is_valid,
      show (2013265920: FBB) = -1 by decide
    ] at h_bus_wellformedness'

    have h_eq_ind : forall reg, Transpiler.ind reg = 4 * ↑reg.1.toNat
    := by
      intro reg
      simp [Transpiler.ind, regidx_to_fin]
      have : reg.1.toNat < 2^5
        := by apply BitVec.toNat_lt_twoPow_of_le; simp
      simp [Fin.ext_iff, Fin.val_mul]
      omega

    obtain real | phantom := this
    . obtain ⟨ h_needs_write, ⟨ imm, rs1, rd, h_inst, h_nz⟩  ⟩ := real
      -- Transpilation
      subst inst; unfold Transpiler.transpile_op at h_transpile
      simp at h_transpile; obtain ⟨ h_pc, h_a', h_eq_b' ⟩ := h_transpile
      symm at h_eq_b'; simp [h_eq_b] at h_eq_b'
      obtain ⟨ h_opcode', h_rs2_ptr, h_rs1_ptr, h_imm, h_mem_as, h_needs_write, h_imm_sgn ⟩ := h_eq_b'
      -- Rest
      unfold VmAirWrapper_load_sign_extend.constraints.programBus_row
             program_of_instruction
             VmAirWrapper_load_sign_extend.constraints.memoryBus_row
             memory_of_instruction
      exists air.adapter.from_state.pc row 0, imm, rs1, rd,
             #v[(air.adapter.rs1_data_0 row 0).val, (air.adapter.rs1_data_1 row 0).val, (air.adapter.rs1_data_2 row 0).val, (air.adapter.rs1_data_3 row 0).val],
             #v[(air.core.read_data row 0 0).val, (air.core.read_data row 0 1).val, (air.core.read_data row 0 2).val, (air.core.read_data row 0 3).val],
             #v[(air.core.prev_data_0 row 0).val, (air.core.prev_data_1 row 0).val, (air.core.prev_data_2 row 0).val, (air.core.prev_data_3 row 0).val]
      simp [show (2013265920 :FBB) = -1 by native_decide,
            *]
      repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
      simp
      clear h_bus_wellformedness'
      split_ands
      . grind
      . simp [Transpiler.utof, Transpiler.sign_extend_16, Transpiler.sign_of]
        rw [Nat.mod_eq_of_lt (by omega)]
        simp [Fin.ext_iff]; congr 2
        simp [BitVec.msb_signExtend]
      . exists air.adapter.read_data_aux.base.prev_timestamp row 0
        exists air.adapter.write_base_aux.prev_timestamp row 0
        exists air.shift_amount row 0
        have h_eq := mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
        simp [← BitVec.toNat_inj] at h_eq
        rw [Nat.mod_eq_of_lt (a := (air.adapter.mem_ptr row 0).val) (by omega)] at h_eq
        have : (BitVec.signExtend 32 (BitVec.ofNat 16 ↑(air.adapter.imm row 0))).toNat = (BitVec.signExtend 32 imm).toNat
        := by
          congr 1
          rw [h_imm]
          simp [Transpiler.utof, Transpiler.sign_extend_16]
          rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          clear *-
          grind
        rw [this] at h_eq
        obtain ⟨ srd0, srd1 ⟩ := shifted_read_data air row h_opcode h_row h_constraints h_is_valid
        obtain ⟨ sh, lsh, rsh ⟩ := shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
        obtain ⟨ wd0, wd1, wd2, wd3 ⟩ := write_data_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
        split_ands <;> try rfl
        rotate_left; rotate_left
        . simp [wd0, sh]; grind
        . simp [wd1, sh]; grind
        . simp [wd2, sh]; grind
        . simp [wd3, sh]; grind
        all_goals
          simp [read_ptr_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness]
          have mem_ptr_eq_imm_plus_rs1 := mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
          simp [← BitVec.toNat_inj] at mem_ptr_eq_imm_plus_rs1
          rw [Nat.mod_eq_of_lt (by omega)] at mem_ptr_eq_imm_plus_rs1
          simp [Fin.ext_iff, mem_ptr_eq_imm_plus_rs1, this]
          omega
    . obtain ⟨ h_needs_write, ⟨ imm, rs1, h_inst ⟩  ⟩ := phantom
      -- Transpilation
      subst inst; unfold Transpiler.transpile_op at h_transpile
      simp at h_transpile; obtain ⟨ h_pc, h_a', h_eq_b' ⟩ := h_transpile
      symm at h_eq_b'; simp [h_eq_b] at h_eq_b'
      obtain ⟨ h_opcode', h_rs2_ptr, h_rs1_ptr, h_imm, h_mem_as, h_needs_write, h_imm_sgn ⟩ := h_eq_b'
      rw [if_pos (by grind)] at h_needs_write
      unfold VmAirWrapper_load_sign_extend.constraints.programBus_row
             program_of_instruction
             VmAirWrapper_load_sign_extend.constraints.memoryBus_row
             memory_of_instruction
      exists air.adapter.from_state.pc row 0, imm, rs1, (regidx.Regidx 0),
             #v[(air.adapter.rs1_data_0 row 0).val, (air.adapter.rs1_data_1 row 0).val, (air.adapter.rs1_data_2 row 0).val, (air.adapter.rs1_data_3 row 0).val],
             #v[(air.core.read_data row 0 0).val, (air.core.read_data row 0 1).val, (air.core.read_data row 0 2).val, (air.core.read_data row 0 3).val],
             #v[(air.core.prev_data_0 row 0).val, (air.core.prev_data_1 row 0).val, (air.core.prev_data_2 row 0).val, (air.core.prev_data_3 row 0).val]
      have h_eq_ind : forall reg, Transpiler.ind reg = 4 * ↑reg.1.toNat
      := by
        intro reg
        simp [Transpiler.ind, regidx_to_fin]
        have : reg.1.toNat < 2^5
          := by apply BitVec.toNat_lt_twoPow_of_le; simp
        simp [Fin.ext_iff, Fin.val_mul]
        omega
      simp [show (2013265920 :FBB) = -1 by native_decide,
            *]
      repeat rw [Nat.mod_eq_of_lt (b := 256) (by omega)]
      simp
      split_ands
      . rfl
      . simp [Transpiler.utof, Transpiler.sign_extend_16, Transpiler.sign_of]
        rw [Nat.mod_eq_of_lt (by omega)]
        simp [Fin.ext_iff]; congr 2
        simp [BitVec.msb_signExtend]
      . exists air.adapter.read_data_aux.base.prev_timestamp row 0
        exists air.adapter.write_base_aux.prev_timestamp row 0
        exists air.shift_amount row 0
        have h_eq := mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
        simp [← BitVec.toNat_inj] at h_eq
        rw [Nat.mod_eq_of_lt (a := (air.adapter.mem_ptr row 0).val) (by omega)] at h_eq
        have : (BitVec.signExtend 32 (BitVec.ofNat 16 ↑(air.adapter.imm row 0))).toNat = (BitVec.signExtend 32 imm).toNat
        := by
          congr 1
          rw [h_imm]
          simp [Transpiler.utof, Transpiler.sign_extend_16]
          rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
          grind
        rw [this] at h_eq
        obtain ⟨ srd0, srd1 ⟩ := shifted_read_data air row h_opcode h_row h_constraints h_is_valid
        obtain ⟨ sh, lsh, rsh ⟩ := shift_eqs air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
        obtain ⟨ wd0, wd1, wd2, wd3 ⟩ := write_data_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
        split_ands <;> try rfl
        rotate_left; rotate_left
        . simp [wd0, sh]; grind
        . simp [wd1, sh]; grind
        . simp [wd2, sh]; grind
        . simp [wd3, sh]; grind
        all_goals
          simp [read_ptr_eq air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness]
          have mem_ptr_eq_imm_plus_rs1 := mem_ptr_eq_imm_plus_rs1 air row h_opcode h_row h_constraints h_is_valid h_bus_wellformedness
          simp [← BitVec.toNat_inj] at mem_ptr_eq_imm_plus_rs1
          rw [Nat.mod_eq_of_lt (by omega)] at mem_ptr_eq_imm_plus_rs1
          simp [Fin.ext_iff, mem_ptr_eq_imm_plus_rs1, this]
          omega

end LoadB
