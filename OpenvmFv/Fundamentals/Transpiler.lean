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
        .some (multiplicity, #v[pc, 544, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
      | .BTYPE (imm, rs2, rs1, bop.BNE) =>
        .some (multiplicity, #v[pc, 545, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
      | .BTYPE (imm, rs2, rs1, bop.BLT) =>
        .some (multiplicity, #v[pc, 549, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
      | .BTYPE (imm, rs2, rs1, bop.BGE) =>
        .some (multiplicity, #v[pc, 550, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
      | .BTYPE (imm, rs2, rs1, bop.BLTU) =>
        .some (multiplicity, #v[pc, 551, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
      | .BTYPE (imm, rs2, rs1, bop.BGEU) =>
        .some (multiplicity, #v[pc, 552, ind rs1, ind rs2, itof imm, 1, 1, 0, 0])
      | .UTYPE (imm, rd, uop.AUIPC) =>
        .some (if rd == regidx.Regidx 0
        then (multiplicity, #v[pc, 1, 0, 0, 0, 0, 0, 0, 0])
        else (multiplicity, #v[pc, 576, ind rd, 0, utof ((zero_extend_24 (BitVec.extractLsb 31 12 imm)) <<< 4), 1, 0, 0, 0]))
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


    -- def transpile_opcode_512
    --   (h_transpile : transpile_op inst mult pc = some (mult, data))
    --   (h_opcode : data[1] = 512)
    -- :
    --   (∃ rs2 rs1 rd, data = #v[pc, 512, ind rd, ind rs1, ind rs2, 1, 1, 0, 0]) ∨
    --   (∃ imm rs1 rd, data = #v[pc, 512, ind rd, ind rs1, utof (sign_extend_24 imm), 1, 0, 0, 0])
    -- := by
    --   set result := transpile_op inst mult pc
    --   simp only [transpile_op] at *
    --   -- cases h: (transpile_op inst mult pc) with
    --   --   | none => simp [h] at h_transpile
    --   --   | some result =>
    --   --     simp [h] at h_transpile
    --   done



end Transpiler
