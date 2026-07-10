/-
  Layer A: Per-Row Facts (Workvar Bit Booleanness)

  Packages all workvar-bit booleanness facts, from the slot-0 base cases
  through the slot-general assembly used by schedule, round-step, and digest
  proofs.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha256.PerRow.BaseFacts

set_option autoImplicit false


namespace Sha2BlockHasherVmAir_sha256.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha256.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ## Slot-0 Workvar Bit Booleanness (constraints 16–79)

Each constraint is `col * (col - 1) = 0`. -/

/-- a-bits for slot 0 are boolean (constraints 16–78). -/
theorem workvar_a0_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 32 → work_vars_a air 0 bit row = 0 ∨ work_vars_a air 0 bit row = 1 := by
  rcases hb with ⟨h0_49, h50_99, _, _, _, _⟩
  rcases h0_49 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h16, _, h18, _, h20, _, h22, _,
      h24, _, h26, _, h28, _, h30, _, h32, _, h34, _, h36, _, h38, _, h40, _, h42, _,
      h44, _, h46, _, h48, _⟩
  rcases h50_99 with
    ⟨h50, _, h52, _, h54, _, h56, _, h58, _, h60, _, h62, _, h64, _, h66, _, h68, _,
      h70, _, h72, _, h74, _, h76, _, h78, _, _⟩
  intro bit hbit
  interval_cases bit
  · simpa [constraint_16] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 0 row) h16
  · simpa [constraint_18] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 1 row) h18
  · simpa [constraint_20] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 2 row) h20
  · simpa [constraint_22] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 3 row) h22
  · simpa [constraint_24] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 4 row) h24
  · simpa [constraint_26] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 5 row) h26
  · simpa [constraint_28] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 6 row) h28
  · simpa [constraint_30] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 7 row) h30
  · simpa [constraint_32] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 8 row) h32
  · simpa [constraint_34] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 9 row) h34
  · simpa [constraint_36] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 10 row) h36
  · simpa [constraint_38] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 11 row) h38
  · simpa [constraint_40] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 12 row) h40
  · simpa [constraint_42] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 13 row) h42
  · simpa [constraint_44] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 14 row) h44
  · simpa [constraint_46] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 15 row) h46
  · simpa [constraint_48] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 16 row) h48
  · simpa [constraint_50] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 17 row) h50
  · simpa [constraint_52] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 18 row) h52
  · simpa [constraint_54] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 19 row) h54
  · simpa [constraint_56] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 20 row) h56
  · simpa [constraint_58] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 21 row) h58
  · simpa [constraint_60] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 22 row) h60
  · simpa [constraint_62] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 23 row) h62
  · simpa [constraint_64] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 24 row) h64
  · simpa [constraint_66] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 25 row) h66
  · simpa [constraint_68] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 26 row) h68
  · simpa [constraint_70] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 27 row) h70
  · simpa [constraint_72] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 28 row) h72
  · simpa [constraint_74] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 29 row) h74
  · simpa [constraint_76] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 30 row) h76
  · simpa [constraint_78] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 31 row) h78

/-- e-bits for slot 0 are boolean (constraints 17–79). -/
theorem workvar_e0_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 32 → work_vars_e air 0 bit row = 0 ∨ work_vars_e air 0 bit row = 1 := by
  rcases hb with ⟨h0_49, h50_99, _, _, _, _⟩
  rcases h0_49 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h17, _, h19, _, h21, _, h23, _,
      h25, _, h27, _, h29, _, h31, _, h33, _, h35, _, h37, _, h39, _, h41, _, h43, _,
      h45, _, h47, _, h49⟩
  rcases h50_99 with
    ⟨_, h51, _, h53, _, h55, _, h57, _, h59, _, h61, _, h63, _, h65, _, h67, _, h69, _,
      h71, _, h73, _, h75, _, h77, _, h79, _⟩
  intro bit hbit
  interval_cases bit
  · simpa [constraint_17] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 0 row) h17
  · simpa [constraint_19] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 1 row) h19
  · simpa [constraint_21] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 2 row) h21
  · simpa [constraint_23] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 3 row) h23
  · simpa [constraint_25] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 4 row) h25
  · simpa [constraint_27] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 5 row) h27
  · simpa [constraint_29] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 6 row) h29
  · simpa [constraint_31] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 7 row) h31
  · simpa [constraint_33] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 8 row) h33
  · simpa [constraint_35] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 9 row) h35
  · simpa [constraint_37] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 10 row) h37
  · simpa [constraint_39] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 11 row) h39
  · simpa [constraint_41] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 12 row) h41
  · simpa [constraint_43] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 13 row) h43
  · simpa [constraint_45] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 14 row) h45
  · simpa [constraint_47] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 15 row) h47
  · simpa [constraint_49] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 16 row) h49
  · simpa [constraint_51] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 17 row) h51
  · simpa [constraint_53] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 18 row) h53
  · simpa [constraint_55] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 19 row) h55
  · simpa [constraint_57] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 20 row) h57
  · simpa [constraint_59] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 21 row) h59
  · simpa [constraint_61] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 22 row) h61
  · simpa [constraint_63] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 23 row) h63
  · simpa [constraint_65] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 24 row) h65
  · simpa [constraint_67] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 25 row) h67
  · simpa [constraint_69] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 26 row) h69
  · simpa [constraint_71] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 27 row) h71
  · simpa [constraint_73] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 28 row) h73
  · simpa [constraint_75] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 29 row) h75
  · simpa [constraint_77] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 30 row) h77
  · simpa [constraint_79] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 31 row) h79

/-! ## Slots 1–3 Workvar Bit Booleanness (constraints 80–271) -/

private theorem workvar_a1_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 32 → work_vars_a air 1 bit row = 0 ∨ work_vars_a air 1 bit row = 1 := by
  rcases hb with ⟨_, h50_99, h100_149, _, _, _⟩
  rcases h50_99 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      h80_99⟩
  rcases h80_99 with
    ⟨h80, _, h82, _, h84, _, h86, _, h88, _, h90, _, h92, _, h94, _, h96, _, h98, _⟩
  rcases h100_149 with
    ⟨h100, _, h102, _, h104, _, h106, _, h108, _, h110, _, h112, _, h114, _, h116, _, h118, _,
      h120, _, h122, _, h124, _, h126, _, h128, _, h130, _, h132, _, h134, _, h136, _, h138, _,
      h140, _, h142, _⟩
  intro bit hbit
  interval_cases bit
  · simpa [constraint_80] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 0 row) h80
  · simpa [constraint_82] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 1 row) h82
  · simpa [constraint_84] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 2 row) h84
  · simpa [constraint_86] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 3 row) h86
  · simpa [constraint_88] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 4 row) h88
  · simpa [constraint_90] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 5 row) h90
  · simpa [constraint_92] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 6 row) h92
  · simpa [constraint_94] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 7 row) h94
  · simpa [constraint_96] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 8 row) h96
  · simpa [constraint_98] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 9 row) h98
  · simpa [constraint_100] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 10 row) h100
  · simpa [constraint_102] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 11 row) h102
  · simpa [constraint_104] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 12 row) h104
  · simpa [constraint_106] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 13 row) h106
  · simpa [constraint_108] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 14 row) h108
  · simpa [constraint_110] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 15 row) h110
  · simpa [constraint_112] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 16 row) h112
  · simpa [constraint_114] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 17 row) h114
  · simpa [constraint_116] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 18 row) h116
  · simpa [constraint_118] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 19 row) h118
  · simpa [constraint_120] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 20 row) h120
  · simpa [constraint_122] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 21 row) h122
  · simpa [constraint_124] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 22 row) h124
  · simpa [constraint_126] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 23 row) h126
  · simpa [constraint_128] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 24 row) h128
  · simpa [constraint_130] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 25 row) h130
  · simpa [constraint_132] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 26 row) h132
  · simpa [constraint_134] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 27 row) h134
  · simpa [constraint_136] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 28 row) h136
  · simpa [constraint_138] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 29 row) h138
  · simpa [constraint_140] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 30 row) h140
  · simpa [constraint_142] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 31 row) h142

private theorem workvar_e1_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 32 → work_vars_e air 1 bit row = 0 ∨ work_vars_e air 1 bit row = 1 := by
  rcases hb with ⟨_, h50_99, h100_149, _, _, _⟩
  rcases h50_99 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      h80_99⟩
  rcases h80_99 with
    ⟨_, h81, _, h83, _, h85, _, h87, _, h89, _, h91, _, h93, _, h95, _, h97, _, h99⟩
  rcases h100_149 with
    ⟨_, h101, _, h103, _, h105, _, h107, _, h109, _, h111, _, h113, _, h115, _, h117, _, h119,
      _, h121, _, h123, _, h125, _, h127, _, h129, _, h131, _, h133, _, h135, _, h137, _, h139,
      _, h141, _, h143, _⟩
  intro bit hbit
  interval_cases bit
  · simpa [constraint_81] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 0 row) h81
  · simpa [constraint_83] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 1 row) h83
  · simpa [constraint_85] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 2 row) h85
  · simpa [constraint_87] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 3 row) h87
  · simpa [constraint_89] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 4 row) h89
  · simpa [constraint_91] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 5 row) h91
  · simpa [constraint_93] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 6 row) h93
  · simpa [constraint_95] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 7 row) h95
  · simpa [constraint_97] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 8 row) h97
  · simpa [constraint_99] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 9 row) h99
  · simpa [constraint_101] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 10 row) h101
  · simpa [constraint_103] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 11 row) h103
  · simpa [constraint_105] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 12 row) h105
  · simpa [constraint_107] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 13 row) h107
  · simpa [constraint_109] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 14 row) h109
  · simpa [constraint_111] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 15 row) h111
  · simpa [constraint_113] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 16 row) h113
  · simpa [constraint_115] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 17 row) h115
  · simpa [constraint_117] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 18 row) h117
  · simpa [constraint_119] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 19 row) h119
  · simpa [constraint_121] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 20 row) h121
  · simpa [constraint_123] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 21 row) h123
  · simpa [constraint_125] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 22 row) h125
  · simpa [constraint_127] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 23 row) h127
  · simpa [constraint_129] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 24 row) h129
  · simpa [constraint_131] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 25 row) h131
  · simpa [constraint_133] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 26 row) h133
  · simpa [constraint_135] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 27 row) h135
  · simpa [constraint_137] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 28 row) h137
  · simpa [constraint_139] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 29 row) h139
  · simpa [constraint_141] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 30 row) h141
  · simpa [constraint_143] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 31 row) h143

private theorem workvar_a2_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 32 → work_vars_a air 2 bit row = 0 ∨ work_vars_a air 2 bit row = 1 := by
  rcases hb with ⟨_, _, h100_149, h150_199, h200_249, _⟩
  rcases h100_149 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, h144_149⟩
  rcases h144_149 with ⟨h144, _, h146, _, h148, _⟩
  rcases h150_199 with
    ⟨h150, _, h152, _, h154, _, h156, _, h158, _, h160, _, h162, _, h164, _, h166, _, h168, _,
      h170, _, h172, _, h174, _, h176, _, h178, _, h180, _, h182, _, h184, _, h186, _, h188, _,
      h190, _, h192, _, h194, _, h196, _, h198, _⟩
  rcases h200_249 with ⟨h200, _, h202, _, h204, _, h206, _⟩
  intro bit hbit
  interval_cases bit
  · simpa [constraint_144] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 0 row) h144
  · simpa [constraint_146] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 1 row) h146
  · simpa [constraint_148] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 2 row) h148
  · simpa [constraint_150] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 3 row) h150
  · simpa [constraint_152] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 4 row) h152
  · simpa [constraint_154] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 5 row) h154
  · simpa [constraint_156] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 6 row) h156
  · simpa [constraint_158] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 7 row) h158
  · simpa [constraint_160] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 8 row) h160
  · simpa [constraint_162] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 9 row) h162
  · simpa [constraint_164] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 10 row) h164
  · simpa [constraint_166] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 11 row) h166
  · simpa [constraint_168] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 12 row) h168
  · simpa [constraint_170] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 13 row) h170
  · simpa [constraint_172] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 14 row) h172
  · simpa [constraint_174] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 15 row) h174
  · simpa [constraint_176] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 16 row) h176
  · simpa [constraint_178] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 17 row) h178
  · simpa [constraint_180] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 18 row) h180
  · simpa [constraint_182] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 19 row) h182
  · simpa [constraint_184] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 20 row) h184
  · simpa [constraint_186] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 21 row) h186
  · simpa [constraint_188] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 22 row) h188
  · simpa [constraint_190] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 23 row) h190
  · simpa [constraint_192] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 24 row) h192
  · simpa [constraint_194] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 25 row) h194
  · simpa [constraint_196] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 26 row) h196
  · simpa [constraint_198] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 27 row) h198
  · simpa [constraint_200] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 28 row) h200
  · simpa [constraint_202] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 29 row) h202
  · simpa [constraint_204] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 30 row) h204
  · simpa [constraint_206] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 31 row) h206

private theorem workvar_e2_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 32 → work_vars_e air 2 bit row = 0 ∨ work_vars_e air 2 bit row = 1 := by
  rcases hb with ⟨_, _, h100_149, h150_199, h200_249, _⟩
  rcases h100_149 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, h144_149⟩
  rcases h144_149 with ⟨_, h145, _, h147, _, h149⟩
  rcases h150_199 with
    ⟨_, h151, _, h153, _, h155, _, h157, _, h159, _, h161, _, h163, _, h165, _, h167, _, h169,
      _, h171, _, h173, _, h175, _, h177, _, h179, _, h181, _, h183, _, h185, _, h187, _, h189,
      _, h191, _, h193, _, h195, _, h197, _, h199⟩
  rcases h200_249 with ⟨_, h201, _, h203, _, h205, _, h207, _⟩
  intro bit hbit
  interval_cases bit
  · simpa [constraint_145] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 0 row) h145
  · simpa [constraint_147] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 1 row) h147
  · simpa [constraint_149] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 2 row) h149
  · simpa [constraint_151] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 3 row) h151
  · simpa [constraint_153] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 4 row) h153
  · simpa [constraint_155] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 5 row) h155
  · simpa [constraint_157] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 6 row) h157
  · simpa [constraint_159] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 7 row) h159
  · simpa [constraint_161] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 8 row) h161
  · simpa [constraint_163] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 9 row) h163
  · simpa [constraint_165] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 10 row) h165
  · simpa [constraint_167] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 11 row) h167
  · simpa [constraint_169] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 12 row) h169
  · simpa [constraint_171] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 13 row) h171
  · simpa [constraint_173] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 14 row) h173
  · simpa [constraint_175] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 15 row) h175
  · simpa [constraint_177] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 16 row) h177
  · simpa [constraint_179] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 17 row) h179
  · simpa [constraint_181] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 18 row) h181
  · simpa [constraint_183] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 19 row) h183
  · simpa [constraint_185] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 20 row) h185
  · simpa [constraint_187] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 21 row) h187
  · simpa [constraint_189] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 22 row) h189
  · simpa [constraint_191] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 23 row) h191
  · simpa [constraint_193] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 24 row) h193
  · simpa [constraint_195] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 25 row) h195
  · simpa [constraint_197] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 26 row) h197
  · simpa [constraint_199] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 27 row) h199
  · simpa [constraint_201] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 28 row) h201
  · simpa [constraint_203] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 29 row) h203
  · simpa [constraint_205] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 30 row) h205
  · simpa [constraint_207] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 31 row) h207

private theorem workvar_a3_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 32 → work_vars_a air 3 bit row = 0 ∨ work_vars_a air 3 bit row = 1 := by
  rcases hb with ⟨_, _, _, _, h200_249, h250_299⟩
  rcases h200_249 with ⟨_, _, _, _, _, _, _, _, h208_249⟩
  rcases h208_249 with
    ⟨h208, _, h210, _, h212, _, h214, _, h216, _, h218, _, h220, _, h222, _, h224, _, h226, _,
      h228, _, h230, _, h232, _, h234, _, h236, _, h238, _, h240, _, h242, _, h244, _, h246, _,
      h248, _⟩
  rcases h250_299 with
    ⟨h250, _, h252, _, h254, _, h256, _, h258, _, h260, _, h262, _, h264, _, h266, _, h268, _,
      h270, _⟩
  intro bit hbit
  interval_cases bit
  · simpa [constraint_208] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 0 row) h208
  · simpa [constraint_210] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 1 row) h210
  · simpa [constraint_212] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 2 row) h212
  · simpa [constraint_214] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 3 row) h214
  · simpa [constraint_216] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 4 row) h216
  · simpa [constraint_218] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 5 row) h218
  · simpa [constraint_220] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 6 row) h220
  · simpa [constraint_222] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 7 row) h222
  · simpa [constraint_224] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 8 row) h224
  · simpa [constraint_226] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 9 row) h226
  · simpa [constraint_228] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 10 row) h228
  · simpa [constraint_230] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 11 row) h230
  · simpa [constraint_232] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 12 row) h232
  · simpa [constraint_234] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 13 row) h234
  · simpa [constraint_236] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 14 row) h236
  · simpa [constraint_238] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 15 row) h238
  · simpa [constraint_240] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 16 row) h240
  · simpa [constraint_242] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 17 row) h242
  · simpa [constraint_244] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 18 row) h244
  · simpa [constraint_246] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 19 row) h246
  · simpa [constraint_248] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 20 row) h248
  · simpa [constraint_250] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 21 row) h250
  · simpa [constraint_252] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 22 row) h252
  · simpa [constraint_254] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 23 row) h254
  · simpa [constraint_256] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 24 row) h256
  · simpa [constraint_258] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 25 row) h258
  · simpa [constraint_260] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 26 row) h260
  · simpa [constraint_262] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 27 row) h262
  · simpa [constraint_264] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 28 row) h264
  · simpa [constraint_266] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 29 row) h266
  · simpa [constraint_268] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 30 row) h268
  · simpa [constraint_270] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 31 row) h270

private theorem workvar_e3_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 32 → work_vars_e air 3 bit row = 0 ∨ work_vars_e air 3 bit row = 1 := by
  rcases hb with ⟨_, _, _, _, h200_249, h250_299⟩
  rcases h200_249 with ⟨_, _, _, _, _, _, _, _, h208_249⟩
  rcases h208_249 with
    ⟨_, h209, _, h211, _, h213, _, h215, _, h217, _, h219, _, h221, _, h223, _, h225, _, h227,
      _, h229, _, h231, _, h233, _, h235, _, h237, _, h239, _, h241, _, h243, _, h245, _, h247,
      _, h249⟩
  rcases h250_299 with
    ⟨_, h251, _, h253, _, h255, _, h257, _, h259, _, h261, _, h263, _, h265, _, h267, _, h269,
      _, h271, _⟩
  intro bit hbit
  interval_cases bit
  · simpa [constraint_209] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 0 row) h209
  · simpa [constraint_211] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 1 row) h211
  · simpa [constraint_213] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 2 row) h213
  · simpa [constraint_215] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 3 row) h215
  · simpa [constraint_217] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 4 row) h217
  · simpa [constraint_219] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 5 row) h219
  · simpa [constraint_221] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 6 row) h221
  · simpa [constraint_223] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 7 row) h223
  · simpa [constraint_225] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 8 row) h225
  · simpa [constraint_227] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 9 row) h227
  · simpa [constraint_229] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 10 row) h229
  · simpa [constraint_231] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 11 row) h231
  · simpa [constraint_233] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 12 row) h233
  · simpa [constraint_235] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 13 row) h235
  · simpa [constraint_237] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 14 row) h237
  · simpa [constraint_239] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 15 row) h239
  · simpa [constraint_241] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 16 row) h241
  · simpa [constraint_243] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 17 row) h243
  · simpa [constraint_245] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 18 row) h245
  · simpa [constraint_247] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 19 row) h247
  · simpa [constraint_249] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 20 row) h249
  · simpa [constraint_251] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 21 row) h251
  · simpa [constraint_253] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 22 row) h253
  · simpa [constraint_255] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 23 row) h255
  · simpa [constraint_257] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 24 row) h257
  · simpa [constraint_259] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 25 row) h259
  · simpa [constraint_261] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 26 row) h261
  · simpa [constraint_263] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 27 row) h263
  · simpa [constraint_265] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 28 row) h265
  · simpa [constraint_267] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 29 row) h267
  · simpa [constraint_269] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 30 row) h269
  · simpa [constraint_271] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 31 row) h271

/-- a-bits for slot s are boolean (all 4 slots, constraints 16–271). -/
theorem workvar_a_bits_boolean (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 32 → work_vars_a air slot bit row = 0 ∨ work_vars_a air slot bit row = 1 := by
  interval_cases slot
  · simpa using workvar_a0_bits_boolean air row hb
  · simpa using workvar_a1_bits_boolean air row hb
  · simpa using workvar_a2_bits_boolean air row hb
  · simpa using workvar_a3_bits_boolean air row hb

/-- e-bits for slot s are boolean (all 4 slots). -/
theorem workvar_e_bits_boolean (air : C FBB ExtF) (row : ℕ) (slot : ℕ)
    (hslot : slot < 4)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 32 → work_vars_e air slot bit row = 0 ∨ work_vars_e air slot bit row = 1 := by
  interval_cases slot
  · simpa using workvar_e0_bits_boolean air row hb
  · simpa using workvar_e1_bits_boolean air row hb
  · simpa using workvar_e2_bits_boolean air row hb
  · simpa using workvar_e3_bits_boolean air row hb

/-- workvar_bit_boolean_constraints → allWorkVarBitsBoolean.
    Assembly: split into a-bits and e-bits, use parametric per-slot lemmas. -/
theorem allWorkVarBitsBoolean_of_constraints (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    allWorkVarBitsBoolean air row :=
  ⟨fun slot bit hs hb' => workvar_a_bits_boolean air row slot hs hb bit hb',
   fun slot bit hs hb' => workvar_e_bits_boolean air row slot hs hb bit hb'⟩

end MatrixProjection

end Sha2BlockHasherVmAir_sha256.BlockSpec
