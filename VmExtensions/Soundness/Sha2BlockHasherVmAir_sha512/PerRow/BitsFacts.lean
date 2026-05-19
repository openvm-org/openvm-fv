/-
  Layer A: Per-Row Facts (Workvar Bit Booleanness)

  Packages all SHA-512 workvar-bit booleanness facts directly from the grouped
  raw row bundles, following the SHA-256 proof shape.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.PerRow.BaseFacts

set_option autoImplicit false

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

private theorem workvar_slot0_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 64 →
      (work_vars_a air 0 bit row = 0 ∨ work_vars_a air 0 bit row = 1) ∧
      (work_vars_e air 0 bit row = 0 ∨ work_vars_e air 0 bit row = 1) := by
  rcases hb with ⟨h0_49, h50_99, h100_149, _, _, _, _, _, _, _, _⟩
  rcases h0_49 with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49⟩
  rcases h50_99 with
    ⟨h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99⟩
  rcases h100_149 with
    ⟨h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132, h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨by simpa [constraint_17] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 0 row) h17,
      by simpa [constraint_18] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 0 row) h18⟩
  · exact ⟨by simpa [constraint_19] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 1 row) h19,
      by simpa [constraint_20] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 1 row) h20⟩
  · exact ⟨by simpa [constraint_21] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 2 row) h21,
      by simpa [constraint_22] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 2 row) h22⟩
  · exact ⟨by simpa [constraint_23] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 3 row) h23,
      by simpa [constraint_24] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 3 row) h24⟩
  · exact ⟨by simpa [constraint_25] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 4 row) h25,
      by simpa [constraint_26] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 4 row) h26⟩
  · exact ⟨by simpa [constraint_27] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 5 row) h27,
      by simpa [constraint_28] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 5 row) h28⟩
  · exact ⟨by simpa [constraint_29] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 6 row) h29,
      by simpa [constraint_30] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 6 row) h30⟩
  · exact ⟨by simpa [constraint_31] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 7 row) h31,
      by simpa [constraint_32] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 7 row) h32⟩
  · exact ⟨by simpa [constraint_33] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 8 row) h33,
      by simpa [constraint_34] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 8 row) h34⟩
  · exact ⟨by simpa [constraint_35] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 9 row) h35,
      by simpa [constraint_36] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 9 row) h36⟩
  · exact ⟨by simpa [constraint_37] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 10 row) h37,
      by simpa [constraint_38] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 10 row) h38⟩
  · exact ⟨by simpa [constraint_39] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 11 row) h39,
      by simpa [constraint_40] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 11 row) h40⟩
  · exact ⟨by simpa [constraint_41] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 12 row) h41,
      by simpa [constraint_42] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 12 row) h42⟩
  · exact ⟨by simpa [constraint_43] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 13 row) h43,
      by simpa [constraint_44] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 13 row) h44⟩
  · exact ⟨by simpa [constraint_45] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 14 row) h45,
      by simpa [constraint_46] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 14 row) h46⟩
  · exact ⟨by simpa [constraint_47] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 15 row) h47,
      by simpa [constraint_48] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 15 row) h48⟩
  · exact ⟨by simpa [constraint_49] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 16 row) h49,
      by simpa [constraint_50] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 16 row) h50⟩
  · exact ⟨by simpa [constraint_51] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 17 row) h51,
      by simpa [constraint_52] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 17 row) h52⟩
  · exact ⟨by simpa [constraint_53] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 18 row) h53,
      by simpa [constraint_54] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 18 row) h54⟩
  · exact ⟨by simpa [constraint_55] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 19 row) h55,
      by simpa [constraint_56] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 19 row) h56⟩
  · exact ⟨by simpa [constraint_57] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 20 row) h57,
      by simpa [constraint_58] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 20 row) h58⟩
  · exact ⟨by simpa [constraint_59] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 21 row) h59,
      by simpa [constraint_60] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 21 row) h60⟩
  · exact ⟨by simpa [constraint_61] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 22 row) h61,
      by simpa [constraint_62] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 22 row) h62⟩
  · exact ⟨by simpa [constraint_63] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 23 row) h63,
      by simpa [constraint_64] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 23 row) h64⟩
  · exact ⟨by simpa [constraint_65] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 24 row) h65,
      by simpa [constraint_66] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 24 row) h66⟩
  · exact ⟨by simpa [constraint_67] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 25 row) h67,
      by simpa [constraint_68] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 25 row) h68⟩
  · exact ⟨by simpa [constraint_69] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 26 row) h69,
      by simpa [constraint_70] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 26 row) h70⟩
  · exact ⟨by simpa [constraint_71] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 27 row) h71,
      by simpa [constraint_72] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 27 row) h72⟩
  · exact ⟨by simpa [constraint_73] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 28 row) h73,
      by simpa [constraint_74] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 28 row) h74⟩
  · exact ⟨by simpa [constraint_75] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 29 row) h75,
      by simpa [constraint_76] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 29 row) h76⟩
  · exact ⟨by simpa [constraint_77] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 30 row) h77,
      by simpa [constraint_78] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 30 row) h78⟩
  · exact ⟨by simpa [constraint_79] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 31 row) h79,
      by simpa [constraint_80] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 31 row) h80⟩
  · exact ⟨by simpa [constraint_81] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 32 row) h81,
      by simpa [constraint_82] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 32 row) h82⟩
  · exact ⟨by simpa [constraint_83] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 33 row) h83,
      by simpa [constraint_84] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 33 row) h84⟩
  · exact ⟨by simpa [constraint_85] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 34 row) h85,
      by simpa [constraint_86] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 34 row) h86⟩
  · exact ⟨by simpa [constraint_87] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 35 row) h87,
      by simpa [constraint_88] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 35 row) h88⟩
  · exact ⟨by simpa [constraint_89] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 36 row) h89,
      by simpa [constraint_90] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 36 row) h90⟩
  · exact ⟨by simpa [constraint_91] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 37 row) h91,
      by simpa [constraint_92] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 37 row) h92⟩
  · exact ⟨by simpa [constraint_93] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 38 row) h93,
      by simpa [constraint_94] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 38 row) h94⟩
  · exact ⟨by simpa [constraint_95] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 39 row) h95,
      by simpa [constraint_96] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 39 row) h96⟩
  · exact ⟨by simpa [constraint_97] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 40 row) h97,
      by simpa [constraint_98] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 40 row) h98⟩
  · exact ⟨by simpa [constraint_99] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 41 row) h99,
      by simpa [constraint_100] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 41 row) h100⟩
  · exact ⟨by simpa [constraint_101] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 42 row) h101,
      by simpa [constraint_102] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 42 row) h102⟩
  · exact ⟨by simpa [constraint_103] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 43 row) h103,
      by simpa [constraint_104] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 43 row) h104⟩
  · exact ⟨by simpa [constraint_105] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 44 row) h105,
      by simpa [constraint_106] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 44 row) h106⟩
  · exact ⟨by simpa [constraint_107] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 45 row) h107,
      by simpa [constraint_108] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 45 row) h108⟩
  · exact ⟨by simpa [constraint_109] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 46 row) h109,
      by simpa [constraint_110] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 46 row) h110⟩
  · exact ⟨by simpa [constraint_111] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 47 row) h111,
      by simpa [constraint_112] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 47 row) h112⟩
  · exact ⟨by simpa [constraint_113] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 48 row) h113,
      by simpa [constraint_114] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 48 row) h114⟩
  · exact ⟨by simpa [constraint_115] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 49 row) h115,
      by simpa [constraint_116] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 49 row) h116⟩
  · exact ⟨by simpa [constraint_117] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 50 row) h117,
      by simpa [constraint_118] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 50 row) h118⟩
  · exact ⟨by simpa [constraint_119] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 51 row) h119,
      by simpa [constraint_120] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 51 row) h120⟩
  · exact ⟨by simpa [constraint_121] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 52 row) h121,
      by simpa [constraint_122] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 52 row) h122⟩
  · exact ⟨by simpa [constraint_123] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 53 row) h123,
      by simpa [constraint_124] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 53 row) h124⟩
  · exact ⟨by simpa [constraint_125] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 54 row) h125,
      by simpa [constraint_126] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 54 row) h126⟩
  · exact ⟨by simpa [constraint_127] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 55 row) h127,
      by simpa [constraint_128] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 55 row) h128⟩
  · exact ⟨by simpa [constraint_129] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 56 row) h129,
      by simpa [constraint_130] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 56 row) h130⟩
  · exact ⟨by simpa [constraint_131] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 57 row) h131,
      by simpa [constraint_132] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 57 row) h132⟩
  · exact ⟨by simpa [constraint_133] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 58 row) h133,
      by simpa [constraint_134] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 58 row) h134⟩
  · exact ⟨by simpa [constraint_135] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 59 row) h135,
      by simpa [constraint_136] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 59 row) h136⟩
  · exact ⟨by simpa [constraint_137] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 60 row) h137,
      by simpa [constraint_138] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 60 row) h138⟩
  · exact ⟨by simpa [constraint_139] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 61 row) h139,
      by simpa [constraint_140] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 61 row) h140⟩
  · exact ⟨by simpa [constraint_141] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 62 row) h141,
      by simpa [constraint_142] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 62 row) h142⟩
  · exact ⟨by simpa [constraint_143] using bit_boolean_of_sq_eq_zero (work_vars_a air 0 63 row) h143,
      by simpa [constraint_144] using bit_boolean_of_sq_eq_zero (work_vars_e air 0 63 row) h144⟩

private theorem workvar_slot1_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 64 →
      (work_vars_a air 1 bit row = 0 ∨ work_vars_a air 1 bit row = 1) ∧
      (work_vars_e air 1 bit row = 0 ∨ work_vars_e air 1 bit row = 1) := by
  rcases hb with ⟨_, _, h100_149, h150_199, h200_249, h250_299, _, _, _, _, _⟩
  rcases h100_149 with
    ⟨h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127, h128, h129, h130, h131, h132, h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149⟩
  rcases h150_199 with
    ⟨h150, h151, h152, h153, h154, h155, h156, h157, h158, h159, h160, h161, h162, h163, h164, h165, h166, h167, h168, h169, h170, h171, h172, h173, h174, h175, h176, h177, h178, h179, h180, h181, h182, h183, h184, h185, h186, h187, h188, h189, h190, h191, h192, h193, h194, h195, h196, h197, h198, h199⟩
  rcases h200_249 with
    ⟨h200, h201, h202, h203, h204, h205, h206, h207, h208, h209, h210, h211, h212, h213, h214, h215, h216, h217, h218, h219, h220, h221, h222, h223, h224, h225, h226, h227, h228, h229, h230, h231, h232, h233, h234, h235, h236, h237, h238, h239, h240, h241, h242, h243, h244, h245, h246, h247, h248, h249⟩
  rcases h250_299 with
    ⟨h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, h261, h262, h263, h264, h265, h266, h267, h268, h269, h270, h271, h272, h273, h274, h275, h276, h277, h278, h279, h280, h281, h282, h283, h284, h285, h286, h287, h288, h289, h290, h291, h292, h293, h294, h295, h296, h297, h298, h299⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨by simpa [constraint_145] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 0 row) h145,
      by simpa [constraint_146] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 0 row) h146⟩
  · exact ⟨by simpa [constraint_147] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 1 row) h147,
      by simpa [constraint_148] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 1 row) h148⟩
  · exact ⟨by simpa [constraint_149] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 2 row) h149,
      by simpa [constraint_150] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 2 row) h150⟩
  · exact ⟨by simpa [constraint_151] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 3 row) h151,
      by simpa [constraint_152] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 3 row) h152⟩
  · exact ⟨by simpa [constraint_153] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 4 row) h153,
      by simpa [constraint_154] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 4 row) h154⟩
  · exact ⟨by simpa [constraint_155] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 5 row) h155,
      by simpa [constraint_156] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 5 row) h156⟩
  · exact ⟨by simpa [constraint_157] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 6 row) h157,
      by simpa [constraint_158] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 6 row) h158⟩
  · exact ⟨by simpa [constraint_159] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 7 row) h159,
      by simpa [constraint_160] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 7 row) h160⟩
  · exact ⟨by simpa [constraint_161] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 8 row) h161,
      by simpa [constraint_162] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 8 row) h162⟩
  · exact ⟨by simpa [constraint_163] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 9 row) h163,
      by simpa [constraint_164] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 9 row) h164⟩
  · exact ⟨by simpa [constraint_165] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 10 row) h165,
      by simpa [constraint_166] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 10 row) h166⟩
  · exact ⟨by simpa [constraint_167] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 11 row) h167,
      by simpa [constraint_168] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 11 row) h168⟩
  · exact ⟨by simpa [constraint_169] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 12 row) h169,
      by simpa [constraint_170] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 12 row) h170⟩
  · exact ⟨by simpa [constraint_171] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 13 row) h171,
      by simpa [constraint_172] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 13 row) h172⟩
  · exact ⟨by simpa [constraint_173] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 14 row) h173,
      by simpa [constraint_174] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 14 row) h174⟩
  · exact ⟨by simpa [constraint_175] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 15 row) h175,
      by simpa [constraint_176] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 15 row) h176⟩
  · exact ⟨by simpa [constraint_177] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 16 row) h177,
      by simpa [constraint_178] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 16 row) h178⟩
  · exact ⟨by simpa [constraint_179] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 17 row) h179,
      by simpa [constraint_180] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 17 row) h180⟩
  · exact ⟨by simpa [constraint_181] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 18 row) h181,
      by simpa [constraint_182] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 18 row) h182⟩
  · exact ⟨by simpa [constraint_183] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 19 row) h183,
      by simpa [constraint_184] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 19 row) h184⟩
  · exact ⟨by simpa [constraint_185] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 20 row) h185,
      by simpa [constraint_186] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 20 row) h186⟩
  · exact ⟨by simpa [constraint_187] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 21 row) h187,
      by simpa [constraint_188] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 21 row) h188⟩
  · exact ⟨by simpa [constraint_189] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 22 row) h189,
      by simpa [constraint_190] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 22 row) h190⟩
  · exact ⟨by simpa [constraint_191] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 23 row) h191,
      by simpa [constraint_192] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 23 row) h192⟩
  · exact ⟨by simpa [constraint_193] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 24 row) h193,
      by simpa [constraint_194] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 24 row) h194⟩
  · exact ⟨by simpa [constraint_195] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 25 row) h195,
      by simpa [constraint_196] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 25 row) h196⟩
  · exact ⟨by simpa [constraint_197] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 26 row) h197,
      by simpa [constraint_198] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 26 row) h198⟩
  · exact ⟨by simpa [constraint_199] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 27 row) h199,
      by simpa [constraint_200] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 27 row) h200⟩
  · exact ⟨by simpa [constraint_201] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 28 row) h201,
      by simpa [constraint_202] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 28 row) h202⟩
  · exact ⟨by simpa [constraint_203] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 29 row) h203,
      by simpa [constraint_204] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 29 row) h204⟩
  · exact ⟨by simpa [constraint_205] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 30 row) h205,
      by simpa [constraint_206] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 30 row) h206⟩
  · exact ⟨by simpa [constraint_207] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 31 row) h207,
      by simpa [constraint_208] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 31 row) h208⟩
  · exact ⟨by simpa [constraint_209] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 32 row) h209,
      by simpa [constraint_210] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 32 row) h210⟩
  · exact ⟨by simpa [constraint_211] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 33 row) h211,
      by simpa [constraint_212] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 33 row) h212⟩
  · exact ⟨by simpa [constraint_213] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 34 row) h213,
      by simpa [constraint_214] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 34 row) h214⟩
  · exact ⟨by simpa [constraint_215] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 35 row) h215,
      by simpa [constraint_216] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 35 row) h216⟩
  · exact ⟨by simpa [constraint_217] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 36 row) h217,
      by simpa [constraint_218] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 36 row) h218⟩
  · exact ⟨by simpa [constraint_219] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 37 row) h219,
      by simpa [constraint_220] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 37 row) h220⟩
  · exact ⟨by simpa [constraint_221] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 38 row) h221,
      by simpa [constraint_222] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 38 row) h222⟩
  · exact ⟨by simpa [constraint_223] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 39 row) h223,
      by simpa [constraint_224] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 39 row) h224⟩
  · exact ⟨by simpa [constraint_225] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 40 row) h225,
      by simpa [constraint_226] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 40 row) h226⟩
  · exact ⟨by simpa [constraint_227] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 41 row) h227,
      by simpa [constraint_228] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 41 row) h228⟩
  · exact ⟨by simpa [constraint_229] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 42 row) h229,
      by simpa [constraint_230] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 42 row) h230⟩
  · exact ⟨by simpa [constraint_231] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 43 row) h231,
      by simpa [constraint_232] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 43 row) h232⟩
  · exact ⟨by simpa [constraint_233] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 44 row) h233,
      by simpa [constraint_234] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 44 row) h234⟩
  · exact ⟨by simpa [constraint_235] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 45 row) h235,
      by simpa [constraint_236] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 45 row) h236⟩
  · exact ⟨by simpa [constraint_237] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 46 row) h237,
      by simpa [constraint_238] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 46 row) h238⟩
  · exact ⟨by simpa [constraint_239] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 47 row) h239,
      by simpa [constraint_240] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 47 row) h240⟩
  · exact ⟨by simpa [constraint_241] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 48 row) h241,
      by simpa [constraint_242] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 48 row) h242⟩
  · exact ⟨by simpa [constraint_243] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 49 row) h243,
      by simpa [constraint_244] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 49 row) h244⟩
  · exact ⟨by simpa [constraint_245] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 50 row) h245,
      by simpa [constraint_246] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 50 row) h246⟩
  · exact ⟨by simpa [constraint_247] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 51 row) h247,
      by simpa [constraint_248] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 51 row) h248⟩
  · exact ⟨by simpa [constraint_249] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 52 row) h249,
      by simpa [constraint_250] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 52 row) h250⟩
  · exact ⟨by simpa [constraint_251] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 53 row) h251,
      by simpa [constraint_252] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 53 row) h252⟩
  · exact ⟨by simpa [constraint_253] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 54 row) h253,
      by simpa [constraint_254] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 54 row) h254⟩
  · exact ⟨by simpa [constraint_255] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 55 row) h255,
      by simpa [constraint_256] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 55 row) h256⟩
  · exact ⟨by simpa [constraint_257] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 56 row) h257,
      by simpa [constraint_258] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 56 row) h258⟩
  · exact ⟨by simpa [constraint_259] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 57 row) h259,
      by simpa [constraint_260] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 57 row) h260⟩
  · exact ⟨by simpa [constraint_261] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 58 row) h261,
      by simpa [constraint_262] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 58 row) h262⟩
  · exact ⟨by simpa [constraint_263] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 59 row) h263,
      by simpa [constraint_264] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 59 row) h264⟩
  · exact ⟨by simpa [constraint_265] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 60 row) h265,
      by simpa [constraint_266] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 60 row) h266⟩
  · exact ⟨by simpa [constraint_267] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 61 row) h267,
      by simpa [constraint_268] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 61 row) h268⟩
  · exact ⟨by simpa [constraint_269] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 62 row) h269,
      by simpa [constraint_270] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 62 row) h270⟩
  · exact ⟨by simpa [constraint_271] using bit_boolean_of_sq_eq_zero (work_vars_a air 1 63 row) h271,
      by simpa [constraint_272] using bit_boolean_of_sq_eq_zero (work_vars_e air 1 63 row) h272⟩

private theorem workvar_slot2_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 64 →
      (work_vars_a air 2 bit row = 0 ∨ work_vars_a air 2 bit row = 1) ∧
      (work_vars_e air 2 bit row = 0 ∨ work_vars_e air 2 bit row = 1) := by
  rcases hb with ⟨_, _, _, _, _, h250_299, h300_349, h350_399, h400_449, _, _, _⟩
  rcases h250_299 with
    ⟨h250, h251, h252, h253, h254, h255, h256, h257, h258, h259, h260, h261, h262, h263, h264, h265, h266, h267, h268, h269, h270, h271, h272, h273, h274, h275, h276, h277, h278, h279, h280, h281, h282, h283, h284, h285, h286, h287, h288, h289, h290, h291, h292, h293, h294, h295, h296, h297, h298, h299⟩
  rcases h300_349 with
    ⟨h300, h301, h302, h303, h304, h305, h306, h307, h308, h309, h310, h311, h312, h313, h314, h315, h316, h317, h318, h319, h320, h321, h322, h323, h324, h325, h326, h327, h328, h329, h330, h331, h332, h333, h334, h335, h336, h337, h338, h339, h340, h341, h342, h343, h344, h345, h346, h347, h348, h349⟩
  rcases h350_399 with
    ⟨h350, h351, h352, h353, h354, h355, h356, h357, h358, h359, h360, h361, h362, h363, h364, h365, h366, h367, h368, h369, h370, h371, h372, h373, h374, h375, h376, h377, h378, h379, h380, h381, h382, h383, h384, h385, h386, h387, h388, h389, h390, h391, h392, h393, h394, h395, h396, h397, h398, h399⟩
  rcases h400_449 with
    ⟨h400, h401, h402, h403, h404, h405, h406, h407, h408, h409, h410, h411, h412, h413, h414, h415, h416, h417, h418, h419, h420, h421, h422, h423, h424, h425, h426, h427, h428, h429, h430, h431, h432, h433, h434, h435, h436, h437, h438, h439, h440, h441, h442, h443, h444, h445, h446, h447, h448, h449⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨by simpa [constraint_273] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 0 row) h273,
      by simpa [constraint_274] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 0 row) h274⟩
  · exact ⟨by simpa [constraint_275] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 1 row) h275,
      by simpa [constraint_276] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 1 row) h276⟩
  · exact ⟨by simpa [constraint_277] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 2 row) h277,
      by simpa [constraint_278] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 2 row) h278⟩
  · exact ⟨by simpa [constraint_279] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 3 row) h279,
      by simpa [constraint_280] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 3 row) h280⟩
  · exact ⟨by simpa [constraint_281] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 4 row) h281,
      by simpa [constraint_282] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 4 row) h282⟩
  · exact ⟨by simpa [constraint_283] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 5 row) h283,
      by simpa [constraint_284] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 5 row) h284⟩
  · exact ⟨by simpa [constraint_285] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 6 row) h285,
      by simpa [constraint_286] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 6 row) h286⟩
  · exact ⟨by simpa [constraint_287] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 7 row) h287,
      by simpa [constraint_288] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 7 row) h288⟩
  · exact ⟨by simpa [constraint_289] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 8 row) h289,
      by simpa [constraint_290] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 8 row) h290⟩
  · exact ⟨by simpa [constraint_291] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 9 row) h291,
      by simpa [constraint_292] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 9 row) h292⟩
  · exact ⟨by simpa [constraint_293] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 10 row) h293,
      by simpa [constraint_294] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 10 row) h294⟩
  · exact ⟨by simpa [constraint_295] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 11 row) h295,
      by simpa [constraint_296] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 11 row) h296⟩
  · exact ⟨by simpa [constraint_297] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 12 row) h297,
      by simpa [constraint_298] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 12 row) h298⟩
  · exact ⟨by simpa [constraint_299] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 13 row) h299,
      by simpa [constraint_300] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 13 row) h300⟩
  · exact ⟨by simpa [constraint_301] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 14 row) h301,
      by simpa [constraint_302] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 14 row) h302⟩
  · exact ⟨by simpa [constraint_303] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 15 row) h303,
      by simpa [constraint_304] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 15 row) h304⟩
  · exact ⟨by simpa [constraint_305] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 16 row) h305,
      by simpa [constraint_306] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 16 row) h306⟩
  · exact ⟨by simpa [constraint_307] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 17 row) h307,
      by simpa [constraint_308] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 17 row) h308⟩
  · exact ⟨by simpa [constraint_309] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 18 row) h309,
      by simpa [constraint_310] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 18 row) h310⟩
  · exact ⟨by simpa [constraint_311] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 19 row) h311,
      by simpa [constraint_312] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 19 row) h312⟩
  · exact ⟨by simpa [constraint_313] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 20 row) h313,
      by simpa [constraint_314] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 20 row) h314⟩
  · exact ⟨by simpa [constraint_315] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 21 row) h315,
      by simpa [constraint_316] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 21 row) h316⟩
  · exact ⟨by simpa [constraint_317] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 22 row) h317,
      by simpa [constraint_318] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 22 row) h318⟩
  · exact ⟨by simpa [constraint_319] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 23 row) h319,
      by simpa [constraint_320] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 23 row) h320⟩
  · exact ⟨by simpa [constraint_321] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 24 row) h321,
      by simpa [constraint_322] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 24 row) h322⟩
  · exact ⟨by simpa [constraint_323] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 25 row) h323,
      by simpa [constraint_324] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 25 row) h324⟩
  · exact ⟨by simpa [constraint_325] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 26 row) h325,
      by simpa [constraint_326] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 26 row) h326⟩
  · exact ⟨by simpa [constraint_327] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 27 row) h327,
      by simpa [constraint_328] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 27 row) h328⟩
  · exact ⟨by simpa [constraint_329] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 28 row) h329,
      by simpa [constraint_330] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 28 row) h330⟩
  · exact ⟨by simpa [constraint_331] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 29 row) h331,
      by simpa [constraint_332] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 29 row) h332⟩
  · exact ⟨by simpa [constraint_333] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 30 row) h333,
      by simpa [constraint_334] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 30 row) h334⟩
  · exact ⟨by simpa [constraint_335] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 31 row) h335,
      by simpa [constraint_336] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 31 row) h336⟩
  · exact ⟨by simpa [constraint_337] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 32 row) h337,
      by simpa [constraint_338] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 32 row) h338⟩
  · exact ⟨by simpa [constraint_339] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 33 row) h339,
      by simpa [constraint_340] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 33 row) h340⟩
  · exact ⟨by simpa [constraint_341] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 34 row) h341,
      by simpa [constraint_342] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 34 row) h342⟩
  · exact ⟨by simpa [constraint_343] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 35 row) h343,
      by simpa [constraint_344] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 35 row) h344⟩
  · exact ⟨by simpa [constraint_345] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 36 row) h345,
      by simpa [constraint_346] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 36 row) h346⟩
  · exact ⟨by simpa [constraint_347] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 37 row) h347,
      by simpa [constraint_348] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 37 row) h348⟩
  · exact ⟨by simpa [constraint_349] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 38 row) h349,
      by simpa [constraint_350] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 38 row) h350⟩
  · exact ⟨by simpa [constraint_351] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 39 row) h351,
      by simpa [constraint_352] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 39 row) h352⟩
  · exact ⟨by simpa [constraint_353] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 40 row) h353,
      by simpa [constraint_354] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 40 row) h354⟩
  · exact ⟨by simpa [constraint_355] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 41 row) h355,
      by simpa [constraint_356] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 41 row) h356⟩
  · exact ⟨by simpa [constraint_357] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 42 row) h357,
      by simpa [constraint_358] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 42 row) h358⟩
  · exact ⟨by simpa [constraint_359] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 43 row) h359,
      by simpa [constraint_360] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 43 row) h360⟩
  · exact ⟨by simpa [constraint_361] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 44 row) h361,
      by simpa [constraint_362] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 44 row) h362⟩
  · exact ⟨by simpa [constraint_363] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 45 row) h363,
      by simpa [constraint_364] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 45 row) h364⟩
  · exact ⟨by simpa [constraint_365] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 46 row) h365,
      by simpa [constraint_366] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 46 row) h366⟩
  · exact ⟨by simpa [constraint_367] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 47 row) h367,
      by simpa [constraint_368] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 47 row) h368⟩
  · exact ⟨by simpa [constraint_369] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 48 row) h369,
      by simpa [constraint_370] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 48 row) h370⟩
  · exact ⟨by simpa [constraint_371] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 49 row) h371,
      by simpa [constraint_372] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 49 row) h372⟩
  · exact ⟨by simpa [constraint_373] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 50 row) h373,
      by simpa [constraint_374] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 50 row) h374⟩
  · exact ⟨by simpa [constraint_375] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 51 row) h375,
      by simpa [constraint_376] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 51 row) h376⟩
  · exact ⟨by simpa [constraint_377] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 52 row) h377,
      by simpa [constraint_378] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 52 row) h378⟩
  · exact ⟨by simpa [constraint_379] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 53 row) h379,
      by simpa [constraint_380] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 53 row) h380⟩
  · exact ⟨by simpa [constraint_381] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 54 row) h381,
      by simpa [constraint_382] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 54 row) h382⟩
  · exact ⟨by simpa [constraint_383] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 55 row) h383,
      by simpa [constraint_384] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 55 row) h384⟩
  · exact ⟨by simpa [constraint_385] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 56 row) h385,
      by simpa [constraint_386] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 56 row) h386⟩
  · exact ⟨by simpa [constraint_387] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 57 row) h387,
      by simpa [constraint_388] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 57 row) h388⟩
  · exact ⟨by simpa [constraint_389] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 58 row) h389,
      by simpa [constraint_390] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 58 row) h390⟩
  · exact ⟨by simpa [constraint_391] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 59 row) h391,
      by simpa [constraint_392] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 59 row) h392⟩
  · exact ⟨by simpa [constraint_393] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 60 row) h393,
      by simpa [constraint_394] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 60 row) h394⟩
  · exact ⟨by simpa [constraint_395] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 61 row) h395,
      by simpa [constraint_396] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 61 row) h396⟩
  · exact ⟨by simpa [constraint_397] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 62 row) h397,
      by simpa [constraint_398] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 62 row) h398⟩
  · exact ⟨by simpa [constraint_399] using bit_boolean_of_sq_eq_zero (work_vars_a air 2 63 row) h399,
      by simpa [constraint_400] using bit_boolean_of_sq_eq_zero (work_vars_e air 2 63 row) h400⟩

private theorem workvar_slot3_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 64 →
      (work_vars_a air 3 bit row = 0 ∨ work_vars_a air 3 bit row = 1) ∧
      (work_vars_e air 3 bit row = 0 ∨ work_vars_e air 3 bit row = 1) := by
  rcases hb with ⟨_, _, _, _, _, _, _, _, h400_449, h450_499, h500_549⟩
  rcases h400_449 with
    ⟨h400, h401, h402, h403, h404, h405, h406, h407, h408, h409, h410, h411, h412, h413, h414, h415, h416, h417, h418, h419, h420, h421, h422, h423, h424, h425, h426, h427, h428, h429, h430, h431, h432, h433, h434, h435, h436, h437, h438, h439, h440, h441, h442, h443, h444, h445, h446, h447, h448, h449⟩
  rcases h450_499 with
    ⟨h450, h451, h452, h453, h454, h455, h456, h457, h458, h459, h460, h461, h462, h463, h464, h465, h466, h467, h468, h469, h470, h471, h472, h473, h474, h475, h476, h477, h478, h479, h480, h481, h482, h483, h484, h485, h486, h487, h488, h489, h490, h491, h492, h493, h494, h495, h496, h497, h498, h499⟩
  rcases h500_549 with
    ⟨h500, h501, h502, h503, h504, h505, h506, h507, h508, h509, h510, h511, h512, h513, h514, h515, h516, h517, h518, h519, h520, h521, h522, h523, h524, h525, h526, h527, h528, h529, h530, h531, h532, h533, h534, h535, h536, h537, h538, h539, h540, h541, h542, h543, h544, h545, h546, h547, h548, h549⟩
  intro bit hbit
  interval_cases bit
  · exact ⟨by simpa [constraint_401] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 0 row) h401,
      by simpa [constraint_402] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 0 row) h402⟩
  · exact ⟨by simpa [constraint_403] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 1 row) h403,
      by simpa [constraint_404] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 1 row) h404⟩
  · exact ⟨by simpa [constraint_405] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 2 row) h405,
      by simpa [constraint_406] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 2 row) h406⟩
  · exact ⟨by simpa [constraint_407] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 3 row) h407,
      by simpa [constraint_408] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 3 row) h408⟩
  · exact ⟨by simpa [constraint_409] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 4 row) h409,
      by simpa [constraint_410] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 4 row) h410⟩
  · exact ⟨by simpa [constraint_411] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 5 row) h411,
      by simpa [constraint_412] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 5 row) h412⟩
  · exact ⟨by simpa [constraint_413] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 6 row) h413,
      by simpa [constraint_414] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 6 row) h414⟩
  · exact ⟨by simpa [constraint_415] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 7 row) h415,
      by simpa [constraint_416] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 7 row) h416⟩
  · exact ⟨by simpa [constraint_417] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 8 row) h417,
      by simpa [constraint_418] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 8 row) h418⟩
  · exact ⟨by simpa [constraint_419] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 9 row) h419,
      by simpa [constraint_420] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 9 row) h420⟩
  · exact ⟨by simpa [constraint_421] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 10 row) h421,
      by simpa [constraint_422] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 10 row) h422⟩
  · exact ⟨by simpa [constraint_423] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 11 row) h423,
      by simpa [constraint_424] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 11 row) h424⟩
  · exact ⟨by simpa [constraint_425] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 12 row) h425,
      by simpa [constraint_426] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 12 row) h426⟩
  · exact ⟨by simpa [constraint_427] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 13 row) h427,
      by simpa [constraint_428] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 13 row) h428⟩
  · exact ⟨by simpa [constraint_429] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 14 row) h429,
      by simpa [constraint_430] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 14 row) h430⟩
  · exact ⟨by simpa [constraint_431] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 15 row) h431,
      by simpa [constraint_432] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 15 row) h432⟩
  · exact ⟨by simpa [constraint_433] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 16 row) h433,
      by simpa [constraint_434] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 16 row) h434⟩
  · exact ⟨by simpa [constraint_435] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 17 row) h435,
      by simpa [constraint_436] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 17 row) h436⟩
  · exact ⟨by simpa [constraint_437] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 18 row) h437,
      by simpa [constraint_438] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 18 row) h438⟩
  · exact ⟨by simpa [constraint_439] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 19 row) h439,
      by simpa [constraint_440] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 19 row) h440⟩
  · exact ⟨by simpa [constraint_441] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 20 row) h441,
      by simpa [constraint_442] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 20 row) h442⟩
  · exact ⟨by simpa [constraint_443] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 21 row) h443,
      by simpa [constraint_444] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 21 row) h444⟩
  · exact ⟨by simpa [constraint_445] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 22 row) h445,
      by simpa [constraint_446] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 22 row) h446⟩
  · exact ⟨by simpa [constraint_447] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 23 row) h447,
      by simpa [constraint_448] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 23 row) h448⟩
  · exact ⟨by simpa [constraint_449] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 24 row) h449,
      by simpa [constraint_450] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 24 row) h450⟩
  · exact ⟨by simpa [constraint_451] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 25 row) h451,
      by simpa [constraint_452] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 25 row) h452⟩
  · exact ⟨by simpa [constraint_453] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 26 row) h453,
      by simpa [constraint_454] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 26 row) h454⟩
  · exact ⟨by simpa [constraint_455] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 27 row) h455,
      by simpa [constraint_456] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 27 row) h456⟩
  · exact ⟨by simpa [constraint_457] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 28 row) h457,
      by simpa [constraint_458] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 28 row) h458⟩
  · exact ⟨by simpa [constraint_459] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 29 row) h459,
      by simpa [constraint_460] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 29 row) h460⟩
  · exact ⟨by simpa [constraint_461] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 30 row) h461,
      by simpa [constraint_462] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 30 row) h462⟩
  · exact ⟨by simpa [constraint_463] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 31 row) h463,
      by simpa [constraint_464] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 31 row) h464⟩
  · exact ⟨by simpa [constraint_465] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 32 row) h465,
      by simpa [constraint_466] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 32 row) h466⟩
  · exact ⟨by simpa [constraint_467] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 33 row) h467,
      by simpa [constraint_468] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 33 row) h468⟩
  · exact ⟨by simpa [constraint_469] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 34 row) h469,
      by simpa [constraint_470] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 34 row) h470⟩
  · exact ⟨by simpa [constraint_471] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 35 row) h471,
      by simpa [constraint_472] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 35 row) h472⟩
  · exact ⟨by simpa [constraint_473] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 36 row) h473,
      by simpa [constraint_474] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 36 row) h474⟩
  · exact ⟨by simpa [constraint_475] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 37 row) h475,
      by simpa [constraint_476] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 37 row) h476⟩
  · exact ⟨by simpa [constraint_477] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 38 row) h477,
      by simpa [constraint_478] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 38 row) h478⟩
  · exact ⟨by simpa [constraint_479] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 39 row) h479,
      by simpa [constraint_480] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 39 row) h480⟩
  · exact ⟨by simpa [constraint_481] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 40 row) h481,
      by simpa [constraint_482] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 40 row) h482⟩
  · exact ⟨by simpa [constraint_483] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 41 row) h483,
      by simpa [constraint_484] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 41 row) h484⟩
  · exact ⟨by simpa [constraint_485] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 42 row) h485,
      by simpa [constraint_486] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 42 row) h486⟩
  · exact ⟨by simpa [constraint_487] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 43 row) h487,
      by simpa [constraint_488] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 43 row) h488⟩
  · exact ⟨by simpa [constraint_489] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 44 row) h489,
      by simpa [constraint_490] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 44 row) h490⟩
  · exact ⟨by simpa [constraint_491] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 45 row) h491,
      by simpa [constraint_492] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 45 row) h492⟩
  · exact ⟨by simpa [constraint_493] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 46 row) h493,
      by simpa [constraint_494] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 46 row) h494⟩
  · exact ⟨by simpa [constraint_495] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 47 row) h495,
      by simpa [constraint_496] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 47 row) h496⟩
  · exact ⟨by simpa [constraint_497] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 48 row) h497,
      by simpa [constraint_498] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 48 row) h498⟩
  · exact ⟨by simpa [constraint_499] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 49 row) h499,
      by simpa [constraint_500] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 49 row) h500⟩
  · exact ⟨by simpa [constraint_501] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 50 row) h501,
      by simpa [constraint_502] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 50 row) h502⟩
  · exact ⟨by simpa [constraint_503] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 51 row) h503,
      by simpa [constraint_504] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 51 row) h504⟩
  · exact ⟨by simpa [constraint_505] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 52 row) h505,
      by simpa [constraint_506] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 52 row) h506⟩
  · exact ⟨by simpa [constraint_507] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 53 row) h507,
      by simpa [constraint_508] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 53 row) h508⟩
  · exact ⟨by simpa [constraint_509] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 54 row) h509,
      by simpa [constraint_510] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 54 row) h510⟩
  · exact ⟨by simpa [constraint_511] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 55 row) h511,
      by simpa [constraint_512] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 55 row) h512⟩
  · exact ⟨by simpa [constraint_513] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 56 row) h513,
      by simpa [constraint_514] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 56 row) h514⟩
  · exact ⟨by simpa [constraint_515] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 57 row) h515,
      by simpa [constraint_516] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 57 row) h516⟩
  · exact ⟨by simpa [constraint_517] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 58 row) h517,
      by simpa [constraint_518] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 58 row) h518⟩
  · exact ⟨by simpa [constraint_519] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 59 row) h519,
      by simpa [constraint_520] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 59 row) h520⟩
  · exact ⟨by simpa [constraint_521] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 60 row) h521,
      by simpa [constraint_522] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 60 row) h522⟩
  · exact ⟨by simpa [constraint_523] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 61 row) h523,
      by simpa [constraint_524] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 61 row) h524⟩
  · exact ⟨by simpa [constraint_525] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 62 row) h525,
      by simpa [constraint_526] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 62 row) h526⟩
  · exact ⟨by simpa [constraint_527] using bit_boolean_of_sq_eq_zero (work_vars_a air 3 63 row) h527,
      by simpa [constraint_528] using bit_boolean_of_sq_eq_zero (work_vars_e air 3 63 row) h528⟩

/-- a-bits for slot `s` are boolean. -/
theorem workvar_a_bits_boolean (air : C FBB ExtF) (row slot : ℕ)
    (hslot : slot < 4)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 64 → work_vars_a air slot bit row = 0 ∨ work_vars_a air slot bit row = 1 := by
  intro bit hbit
  interval_cases slot
  · exact (workvar_slot0_bits_boolean air row hb bit hbit).1
  · exact (workvar_slot1_bits_boolean air row hb bit hbit).1
  · exact (workvar_slot2_bits_boolean air row hb bit hbit).1
  · exact (workvar_slot3_bits_boolean air row hb bit hbit).1

/-- e-bits for slot `s` are boolean. -/
theorem workvar_e_bits_boolean (air : C FBB ExtF) (row slot : ℕ)
    (hslot : slot < 4)
    (hb : workvar_bit_boolean_constraints air row) :
    ∀ bit, bit < 64 → work_vars_e air slot bit row = 0 ∨ work_vars_e air slot bit row = 1 := by
  intro bit hbit
  interval_cases slot
  · exact (workvar_slot0_bits_boolean air row hb bit hbit).2
  · exact (workvar_slot1_bits_boolean air row hb bit hbit).2
  · exact (workvar_slot2_bits_boolean air row hb bit hbit).2
  · exact (workvar_slot3_bits_boolean air row hb bit hbit).2

/-- workvar_bit_boolean_constraints -> allWorkVarBitsBoolean. -/
theorem allWorkVarBitsBoolean_of_constraints (air : C FBB ExtF) (row : ℕ)
    (hb : workvar_bit_boolean_constraints air row) :
    allWorkVarBitsBoolean air row :=
  ⟨fun slot bit hs hb' => workvar_a_bits_boolean air row slot hs hb bit hb',
   fun slot bit hs hb' => workvar_e_bits_boolean air row slot hs hb bit hb'⟩

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
