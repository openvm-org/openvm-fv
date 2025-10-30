import LeanRV32D
import Mathlib

import OpenvmFv.Fundamentals.BabyBear

def regidx_to_fin (r: regidx): Fin 32 :=
  match r with
    | regidx.Regidx r => ⟨
        r.toNat,
        by {
          have : (if false = true then 4 else 5) ≤ 5 := by decide
          convert BitVec.toNat_lt_twoPow_of_le this
        }
      ⟩

namespace Transpiler

  def ind (rd : regidx) : FBB :=
    ⟨4 * (regidx_to_fin rd).val, by omega⟩

  lemma ind_range : ind rd < 128 := by
    unfold ind regidx_to_fin
    simp
    have : rd.1.toNat < 2^5 := by
      apply BitVec.toNat_lt_twoPow_of_le
      simp
    apply Fin.lt_def.mpr
    simp
    omega

  def itof (bv : BitVec n) : FBB :=
    bv.toInt

  def sign_extend_24 (bv : BitVec 12) : BitVec 24 :=
    bv.signExtend 24

  def sign_extend_16 (bv : BitVec 12) : BitVec 16 :=
    bv.signExtend 16

  def zero_extend_24 (bv : BitVec n) : BitVec 24 :=
    bv.setWidth 24

  def utof (bv : BitVec n) : FBB :=
    bv.toNat

  def transpile_op (inst : instruction) (multiplicity : FBB) (pc : FBB): Option (FBB × Vector FBB 9) :=
    match inst with
      | .RTYPE (rs2, rs1, rd, rop.ADD)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 512, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]))
      | .RTYPE (rs2, rs1, rd, rop.SUB)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 513, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]))
      | .RTYPE (rs2, rs1, rd, rop.XOR)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 514, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]))
      | .RTYPE (rs2, rs1, rd, rop.OR)   =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 515, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]))
      | .RTYPE (rs2, rs1, rd, rop.AND)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 516, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]))
      | .RTYPE (rs2, rs1, rd, rop.SLL)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 517, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]))
      | .RTYPE (rs2, rs1, rd, rop.SRL)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 518, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]))
      | .RTYPE (rs2, rs1, rd, rop.SRA)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 519, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]))
      | .RTYPE (rs2, rs1, rd, rop.SLT)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 520, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]))
      | .RTYPE (rs2, rs1, rd, rop.SLTU) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 521, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]))
      | .ITYPE (imm, rs1, rd, iop.ADDI)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 512, ind rd, ind rs1, utof (sign_extend_24 imm), 1, 0, 0, 0]))
      | .ITYPE (imm, rs1, rd, iop.XORI)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 514, ind rd, ind rs1, utof (sign_extend_24 imm), 1, 0, 0, 0]))
      | .ITYPE (imm, rs1, rd, iop.ORI)   =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 515, ind rd, ind rs1, utof (sign_extend_24 imm), 1, 0, 0, 0]))
      | .ITYPE (imm, rs1, rd, iop.ANDI)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 516, ind rd, ind rs1, utof (sign_extend_24 imm), 1, 0, 0, 0]))
      | .SHIFTIOP (shamt, rs1, rd, sop.SLLI)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 517, ind rd, ind rs1, utof (zero_extend_24 (BitVec.extractLsb 4 0 shamt)), 1, 0, 0, 0]))
      | .SHIFTIOP (shamt, rs1, rd, sop.SRLI)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 518, ind rd, ind rs1, utof (zero_extend_24 (BitVec.extractLsb 4 0 shamt)), 1, 0, 0, 0]))
      | .SHIFTIOP (shamt, rs1, rd, sop.SRAI)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 519, ind rd, ind rs1, utof (zero_extend_24 (BitVec.extractLsb 4 0 shamt)), 1, 0, 0, 0]))
      | .ITYPE (imm, rs1, rd, iop.SLTI)  =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 520, ind rd, ind rs1, utof (sign_extend_24 imm), 1, 0, 0, 0]))
      | .ITYPE (imm, rs1, rd, iop.SLTIU) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 521, ind rd, ind rs1, utof (sign_extend_24 imm), 1, 0, 0, 0]))
      | .BTYPE (imm, rs2, rs1, bop.BEQ) =>
        if (imm % 4 = 0)
        then .some (multiplicity, #v[pc, 544, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
        else .none
      | .BTYPE (imm, rs2, rs1, bop.BNE) =>
        if (imm % 4 = 0)
        then .some (multiplicity, #v[pc, 545, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
        else .none
      | .BTYPE (imm, rs2, rs1, bop.BLT) =>
        if (imm % 4 = 0)
        then .some (multiplicity, #v[pc, 549, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
        else .none
      | .BTYPE (imm, rs2, rs1, bop.BGE) =>
        if (imm % 4 = 0)
        then .some (multiplicity, #v[pc, 550, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
        else .none
      | .BTYPE (imm, rs2, rs1, bop.BLTU) =>
        if (imm % 4 = 0)
        then .some (multiplicity, #v[pc, 551, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
        else .none
      | .BTYPE (imm, rs2, rs1, bop.BGEU) =>
        if (imm % 4 = 0)
        then .some (multiplicity, #v[pc, 552, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
        else .none
      | .UTYPE (imm, rd, uop.AUIPC) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 576, ind rd, 0, utof ((zero_extend_24 imm) <<< 4), 1, 0, 0, 0]))
      | .MUL (rs2, rs1, rd, { high := false, signed_rs1 := _, signed_rs2 := _ : mul_op}) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 592, ind rd, ind rs1, ind rs2, 1, 0, 0, 0]))
      | .MUL (rs2, rs1, rd, { high := true, signed_rs1 := true, signed_rs2 := true : mul_op}) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 593, ind rd, ind rs1, ind rs2, 1, 0, 0, 0]))
      | .MUL (rs2, rs1, rd, { high := true, signed_rs1 := true, signed_rs2 := false : mul_op}) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 594, ind rd, ind rs1, ind rs2, 1, 0, 0, 0]))
      | .MUL (rs2, rs1, rd, { high := true, signed_rs1 := false, signed_rs2 := false : mul_op}) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 595, ind rd, ind rs1, ind rs2, 1, 0, 0, 0]))
      | .DIV (rs2, rs1, rd, false) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 596, ind rd, ind rs1, ind rs2, 1, 0, 0, 0]))
      | .DIV (rs2, rs1, rd, true) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 597, ind rd, ind rs1, ind rs2, 1, 0, 0, 0]))
      | .REM (rs2, rs1, rd, false) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 598, ind rd, ind rs1, ind rs2, 1, 0, 0, 0]))
      | .REM (rs2, rs1, rd, true) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 599, ind rd, ind rs1, ind rs2, 1, 0, 0, 0]))
      | _ => .none

    lemma transpiler_supported_opcode_types
      (h_some : transpile_op inst mult pc = .some result)
    :
      (∃ data, inst = .RTYPE data) ∨
      (∃ data, inst = .ITYPE data) ∨
      (∃ data, inst = .SHIFTIOP data) ∨
      (∃ data, inst = .BTYPE data) ∨
      (∃ data, inst = .UTYPE data) ∨
      (∃ data, inst = .MUL data) ∨
      (∃ data, inst = .DIV data) ∨
      (∃ data, inst = .REM data)
    := by
      cases h: inst
      case RTYPE data => left; use data
      case ITYPE data => right; left; use data
      case SHIFTIOP data => right; right; left; use data
      case BTYPE data => right; right; right; left; use data
      case UTYPE data => right; right; right; right; left; use data
      case MUL data => right; right; right; right; right; left; use data
      case DIV data => right; right; right; right; right; right; left; use data
      case REM data => right; right; right; right; right; right; right; use data
      all_goals {
        exfalso
        rewrite [h] at h_some
        reduce at h_some
        simp at h_some
      }

    lemma non_phantom_rd
      (h: ¬(rd == regidx.Regidx 0#5) = true)
    : ¬rd.1 = 0#5 := by
      by_cases h_contr : rd = regidx.Regidx 0#5
      . simp [h_contr] at h
        exfalso
        have : (regidx.Regidx 0#5 == regidx.Regidx 0#5) = true := rfl
        contradiction
      . obtain ⟨rd⟩ := rd
        by_cases h_contr' : (regidx.Regidx rd).1 = 0#5
        . aesop
        . aesop

    lemma extract_opcode
      (h: some (mult, #v[x1, x2, x3, x4, x5, x6, x7, x8, x9]) = some result)
    : result.2[1] = x2 := by
      aesop

    lemma extract_rs2_as
      (h: some (mult, #v[x1, x2, x3, x4, x5, x6, x7, x8, x9]) = some result)
    : result.2[6] = x7 := by
      aesop

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_512
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 512)
    :
      (result.2[6] = 0 ∧ ∃ imm rs1 rd, inst = .ITYPE (imm, rs1, rd, iop.ADDI) ∧ rd.1 ≠ 0) ∨
      (result.2[6] = 1 ∧ ∃ rs2 rs1 rd, inst = .RTYPE (rs2, rs1, rd, rop.ADD) ∧ rd.1 ≠ 0)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case ADD =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use rs2, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        case ADDI =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use imm, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_513
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 513)
    :
      result.2[6] = 1 ∧ ∃ rs2 rs1 rd, inst = .RTYPE (rs2, rs1, rd, rop.SUB) ∧ rd.1 ≠ 0
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case SUB =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use rs2, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_514
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 514)
    :
      (result.2[6] = 0 ∧ ∃ imm rs1 rd, inst = .ITYPE (imm, rs1, rd, iop.XORI) ∧ rd.1 ≠ 0) ∨
      (result.2[6] = 1 ∧ ∃ rs2 rs1 rd, inst = .RTYPE (rs2, rs1, rd, rop.XOR) ∧ rd.1 ≠ 0)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case XOR =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use rs2, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        case XORI =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use imm, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_515
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 515)
    :
      (result.2[6] = 0 ∧ ∃ imm rs1 rd, inst = .ITYPE (imm, rs1, rd, iop.ORI) ∧ rd.1 ≠ 0) ∨
      (result.2[6] = 1 ∧ ∃ rs2 rs1 rd, inst = .RTYPE (rs2, rs1, rd, rop.OR) ∧ rd.1 ≠ 0)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case OR =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use rs2, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        case ORI =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use imm, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_516
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 516)
    :
      (result.2[6] = 0 ∧ ∃ imm rs1 rd, inst = .ITYPE (imm, rs1, rd, iop.ANDI) ∧ rd.1 ≠ 0) ∨
      (result.2[6] = 1 ∧ ∃ rs2 rs1 rd, inst = .RTYPE (rs2, rs1, rd, rop.AND) ∧ rd.1 ≠ 0)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case AND =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use rs2, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        case ANDI =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use imm, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_517
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 517)
    :
      (result.2[6] = 0 ∧ ∃ shamt rs1 rd, inst = .SHIFTIOP (shamt, rs1, rd, sop.SLLI) ∧ rd.1 ≠ 0) ∨
      (result.2[6] = 1 ∧ ∃ rs2 rs1 rd, inst = .RTYPE (rs2, rs1, rd, rop.SLL) ∧ rd.1 ≠ 0)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case SLL =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use rs2, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case SLLI =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use shamt, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_518
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 518)
    :
      (result.2[6] = 0 ∧ ∃ shamt rs1 rd, inst = .SHIFTIOP (shamt, rs1, rd, sop.SRLI) ∧ rd.1 ≠ 0) ∨
      (result.2[6] = 1 ∧ ∃ rs2 rs1 rd, inst = .RTYPE (rs2, rs1, rd, rop.SRL) ∧ rd.1 ≠ 0)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case SRL =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use rs2, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case SRLI =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use shamt, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_519
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 519)
    :
      (result.2[6] = 0 ∧ ∃ shamt rs1 rd, inst = .SHIFTIOP (shamt, rs1, rd, sop.SRAI) ∧ rd.1 ≠ 0) ∨
      (result.2[6] = 1 ∧ ∃ rs2 rs1 rd, inst = .RTYPE (rs2, rs1, rd, rop.SRA) ∧ rd.1 ≠ 0)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case SRA =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use rs2, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case SRAI =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use shamt, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_520
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 520)
    :
      (result.2[6] = 0 ∧ ∃ imm rs1 rd, inst = .ITYPE (imm, rs1, rd, iop.SLTI) ∧ rd.1 ≠ 0) ∨
      (result.2[6] = 1 ∧ ∃ rs2 rs1 rd, inst = .RTYPE (rs2, rs1, rd, rop.SLT) ∧ rd.1 ≠ 0)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case SLT =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use rs2, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        case SLTI =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use imm, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_521
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 521)
    :
      (result.2[6] = 0 ∧ ∃ imm rs1 rd, inst = .ITYPE (imm, rs1, rd, iop.SLTIU) ∧ rd.1 ≠ 0) ∨
      (result.2[6] = 1 ∧ ∃ rs2 rs1 rd, inst = .RTYPE (rs2, rs1, rd, rop.SLTU) ∧ rd.1 ≠ 0)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        case SLTU =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use rs2, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        case SLTIU =>
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            exfalso
            omega
          . have h_rs2_as := extract_rs2_as h_transpile
            simp [h_rs2_as]
            have h_rd := non_phantom_rd h_if
            use imm, rs1, rd
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_544
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 544)
    :
      ∃ imm rs2 rs1, imm % 4 = 0 ∧ inst = .BTYPE (imm, rs2, rs1, bop.BEQ)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        case BEQ =>
          use imm, rs2, rs1
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          exact ⟨h_if, h_op_data⟩
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_545
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 545)
    :
      ∃ imm rs2 rs1, imm % 4 = 0 ∧ inst = .BTYPE (imm, rs2, rs1, bop.BNE)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        case BNE =>
          use imm, rs2, rs1
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          exact ⟨h_if, h_op_data⟩
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_549
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 549)
    :
      ∃ imm rs2 rs1, imm % 4 = 0 ∧ inst = .BTYPE (imm, rs2, rs1, bop.BLT)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        case BLT =>
          use imm, rs2, rs1
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          exact ⟨h_if, h_op_data⟩
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_550
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 550)
    :
      ∃ imm rs2 rs1, imm % 4 = 0 ∧ inst = .BTYPE (imm, rs2, rs1, bop.BGE)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        case BGE =>
          use imm, rs2, rs1
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          exact ⟨h_if, h_op_data⟩
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_551
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 551)
    :
      ∃ imm rs2 rs1, imm % 4 = 0 ∧ inst = .BTYPE (imm, rs2, rs1, bop.BLTU)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        case BLTU =>
          use imm, rs2, rs1
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          exact ⟨h_if, h_op_data⟩
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_552
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 552)
    :
      ∃ imm rs2 rs1, imm % 4 = 0 ∧ inst = .BTYPE (imm, rs2, rs1, bop.BGEU)
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        case BGEU =>
          use imm, rs2, rs1
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          exact ⟨h_if, h_op_data⟩
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_576
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 576)
    :
      ∃ imm rd, inst = .UTYPE (imm, rd, uop.AUIPC) ∧ rd.1 ≠ 0
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if
          . symm at h_transpile; simp_all
          . have h_rd := non_phantom_rd h_if
            simp_all
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    -- DIV/REM

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_596
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 596)
    :
      ∃ rs2 rs1 rd, inst = .DIV (rs2, rs1, rd, false) ∧ rd.1 ≠ 0
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨rs2, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed

        all_goals
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if

        . have := extract_opcode h_transpile
          omega
        . have h_rd := non_phantom_rd h_if
          use rs2, rs1, rd
          simp_all
        . have := extract_opcode h_transpile
          omega
        . have := extract_opcode h_transpile
          omega
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_597
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 597)
    :
      ∃ rs2 rs1 rd, inst = .DIV (rs2, rs1, rd, true) ∧ rd.1 ≠ 0
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨rs2, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed

        all_goals
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if

        . have := extract_opcode h_transpile
          omega
        . have := extract_opcode h_transpile
          omega
        . have := extract_opcode h_transpile
          omega
        . have h_rd := non_phantom_rd h_if
          use rs2, rs1, rd
          simp_all
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_598
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 598)
    :
      ∃ rs2 rs1 rd, inst = .REM (rs2, rs1, rd, false) ∧ rd.1 ≠ 0
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨rs2, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed

        all_goals
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if

        . have := extract_opcode h_transpile
          omega
        . have h_rd := non_phantom_rd h_if
          use rs2, rs1, rd
          simp_all
        . have := extract_opcode h_transpile
          omega
        . have := extract_opcode h_transpile
          omega

    set_option maxHeartbeats 0 in
    lemma transpiler_opcode_599
      (h_transpile : transpile_op inst mult pc = .some result)
      (h_opcode: result.2[1] = 599)
    :
      ∃ rs2 rs1 rd, inst = .REM (rs2, rs1, rd, true) ∧ rd.1 ≠ 0
    := by
      have h_opcodes := transpiler_supported_opcode_types h_transpile
      rcases h_opcodes with h_type | h_type | h_type | h_type | h_type | h_type | h_type | h_type
      case inl => -- RTYPE
        obtain ⟨⟨rs2, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
          . have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      case inr.inr.inl => --SHIFTIOP
        obtain ⟨⟨shamt, rs1, rd, op⟩, h_op_data⟩ := h_type
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, op⟩, h_op_data⟩ := h_type -- ITYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs2, rs1, op⟩, h_op_data⟩ := h_type -- BTYPE
        cases op
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile
          have := extract_opcode h_transpile
          clear * - h_opcode this
          omega
        }
      . obtain ⟨⟨imm, rd, op⟩, h_op_data⟩ := h_type -- UTYPE
        cases op
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          simp at h_transpile
        . exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
      . obtain ⟨⟨imm, rs1, rd, ⟨high, signed_rs1, signed_rs2⟩⟩, h_op_data⟩ := h_type -- MUL
        cases high <;> cases signed_rs1 <;> cases signed_rs2
        case true.false.true =>
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          simp at h_transpile
        all_goals {
          rewrite [h_op_data] at h_transpile
          unfold Transpiler.transpile_op at h_transpile
          exfalso
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨imm, rs1, rd, signed⟩, h_op_data⟩ := h_type -- DIV
        cases signed
        all_goals {
          exfalso
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if <;> {
            have := extract_opcode h_transpile
            clear * - h_opcode this
            omega
          }
        }
      . obtain ⟨⟨rs2, rs1, rd, signed⟩, h_op_data⟩ := h_type -- REM
        cases signed

        all_goals
          rewrite [h_op_data] at h_transpile
          unfold transpile_op at h_transpile
          dsimp at h_transpile
          split_ifs at h_transpile with h_if

        . have := extract_opcode h_transpile
          omega
        . have := extract_opcode h_transpile
          omega
        . have := extract_opcode h_transpile
          omega
        . have h_rd := non_phantom_rd h_if
          use rs2, rs1, rd
          simp_all

end Transpiler
