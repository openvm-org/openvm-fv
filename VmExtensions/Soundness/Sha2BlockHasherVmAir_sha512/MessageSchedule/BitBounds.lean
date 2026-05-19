/-
  Layer B: Message Schedule Correctness (Bit Bounds)

  Combined module: proves that all SHA-512 schedule word bits are boolean
  on round rows, dispatching across 4 slots × 64 bits each.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.TraceSpec
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.SpecFacts
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.Core.FieldArithmetic

set_option autoImplicit false
set_option maxHeartbeats 40000000

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

private theorem bit_boolean_of_round_constraint
    {air : C FBB ExtF} {row : ℕ} {x : FBB}
    (hround_next : next_is_round_row air row = 1)
    (hpoly : next_is_round_row air row * (x * (x - 1)) = 0) :
    x = 0 ∨ x = 1 := by
  exact bit_boolean_of_sq_eq_zero x (by simpa [hround_next] using hpoly)

-- Slot 0

set_option maxHeartbeats 40000000 in
theorem schedule_bit_boolean_raw_slot0
    {air : C FBB ExtF} {row slot bit : ℕ}
    (hslot0 : slot = 0)
    (hbit : bit < 64)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    next_msg_schedule_w air slot bit row = 0 ∨
      next_msg_schedule_w air slot bit row = 1 := by
  subst hslot0
  rcases hs with ⟨_, h1100_1149, h1150_1199, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1100_1149 at h1100_1149
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1150_1199 at h1150_1199
  interval_cases bit
  · have h1124 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1124 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1124] using h1124)
  · have h1125 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1125 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1125] using h1125)
  · have h1126 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1126 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1126] using h1126)
  · have h1127 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1127 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1127] using h1127)
  · have h1128 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1128 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1128] using h1128)
  · have h1129 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1129 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1129] using h1129)
  · have h1130 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1130 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1130] using h1130)
  · have h1131 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1131 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1131] using h1131)
  · have h1132 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1132 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1132] using h1132)
  · have h1133 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1133 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1133] using h1133)
  · have h1134 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1134 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1134] using h1134)
  · have h1135 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1135 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1135] using h1135)
  · have h1136 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1136 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1136] using h1136)
  · have h1137 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1137 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1137] using h1137)
  · have h1138 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1138 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1138] using h1138)
  · have h1139 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1139 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1139] using h1139)
  · have h1140 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1140 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1140] using h1140)
  · have h1141 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1141 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1141] using h1141)
  · have h1142 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1142 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1142] using h1142)
  · have h1143 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1143 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1143] using h1143)
  · have h1144 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1144 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1144] using h1144)
  · have h1145 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1145 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1145] using h1145)
  · have h1146 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1146 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1146] using h1146)
  · have h1147 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1147 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1147] using h1147)
  · have h1148 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1148 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1148] using h1148)
  · have h1149 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1149 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1149] using h1149)
  · have h1150 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1150 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1150] using h1150)
  · have h1151 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1151 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1151] using h1151)
  · have h1152 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1152 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1152] using h1152)
  · have h1153 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1153 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1153] using h1153)
  · have h1154 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1154 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1154] using h1154)
  · have h1155 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1155 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1155] using h1155)
  · have h1156 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1156 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1156] using h1156)
  · have h1157 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1157 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1157] using h1157)
  · have h1158 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1158 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1158] using h1158)
  · have h1159 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1159 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1159] using h1159)
  · have h1160 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1160 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1160] using h1160)
  · have h1161 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1161 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1161] using h1161)
  · have h1162 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1162 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1162] using h1162)
  · have h1163 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1163 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1163] using h1163)
  · have h1164 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1164 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1164] using h1164)
  · have h1165 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1165 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1165] using h1165)
  · have h1166 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1166 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1166] using h1166)
  · have h1167 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1167 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1167] using h1167)
  · have h1168 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1168 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1168] using h1168)
  · have h1169 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1169 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1169] using h1169)
  · have h1170 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1170 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1170] using h1170)
  · have h1171 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1171 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1171] using h1171)
  · have h1172 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1172 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1172] using h1172)
  · have h1173 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1173 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1173] using h1173)
  · have h1174 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1174 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1174] using h1174)
  · have h1175 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1175 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1175] using h1175)
  · have h1176 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1176 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1176] using h1176)
  · have h1177 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1177 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1177] using h1177)
  · have h1178 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1178 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1178] using h1178)
  · have h1179 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1179 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1179] using h1179)
  · have h1180 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1180 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1180] using h1180)
  · have h1181 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1181 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1181] using h1181)
  · have h1182 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1182 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1182] using h1182)
  · have h1183 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1183 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1183] using h1183)
  · have h1184 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1184 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1184] using h1184)
  · have h1185 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1185 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1185] using h1185)
  · have h1186 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1186 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1186] using h1186)
  · have h1187 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1187 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1187] using h1187)

-- Slot 1

set_option maxHeartbeats 40000000 in
theorem schedule_bit_boolean_raw_slot1
    {air : C FBB ExtF} {row slot bit : ℕ}
    (hslot1 : slot = 1)
    (hbit : bit < 64)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    next_msg_schedule_w air slot bit row = 0 ∨
      next_msg_schedule_w air slot bit row = 1 := by
  subst hslot1
  rcases hs with ⟨_, _, _, h1200_1249, h1250_1299, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1200_1249 at h1200_1249
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1250_1299 at h1250_1299
  interval_cases bit
  · have h1200 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1200 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1200] using h1200)
  · have h1201 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1201 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1201] using h1201)
  · have h1202 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1202 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1202] using h1202)
  · have h1203 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1203 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1203] using h1203)
  · have h1204 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1204 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1204] using h1204)
  · have h1205 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1205 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1205] using h1205)
  · have h1206 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1206 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1206] using h1206)
  · have h1207 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1207 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1207] using h1207)
  · have h1208 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1208 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1208] using h1208)
  · have h1209 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1209 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1209] using h1209)
  · have h1210 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1210 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1210] using h1210)
  · have h1211 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1211 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1211] using h1211)
  · have h1212 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1212 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1212] using h1212)
  · have h1213 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1213 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1213] using h1213)
  · have h1214 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1214 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1214] using h1214)
  · have h1215 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1215 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1215] using h1215)
  · have h1216 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1216 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1216] using h1216)
  · have h1217 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1217 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1217] using h1217)
  · have h1218 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1218 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1218] using h1218)
  · have h1219 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1219 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1219] using h1219)
  · have h1220 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1220 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1220] using h1220)
  · have h1221 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1221 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1221] using h1221)
  · have h1222 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1222 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1222] using h1222)
  · have h1223 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1223 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1223] using h1223)
  · have h1224 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1224 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1224] using h1224)
  · have h1225 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1225 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1225] using h1225)
  · have h1226 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1226 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1226] using h1226)
  · have h1227 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1227 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1227] using h1227)
  · have h1228 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1228 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1228] using h1228)
  · have h1229 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1229 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1229] using h1229)
  · have h1230 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1230 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1230] using h1230)
  · have h1231 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1231 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1231] using h1231)
  · have h1232 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1232 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1232] using h1232)
  · have h1233 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1233 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1233] using h1233)
  · have h1234 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1234 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1234] using h1234)
  · have h1235 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1235 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1235] using h1235)
  · have h1236 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1236 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1236] using h1236)
  · have h1237 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1237 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1237] using h1237)
  · have h1238 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1238 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1238] using h1238)
  · have h1239 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1239 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1239] using h1239)
  · have h1240 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1240 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1240] using h1240)
  · have h1241 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1241 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1241] using h1241)
  · have h1242 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1242 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1242] using h1242)
  · have h1243 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1243 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1243] using h1243)
  · have h1244 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1244 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1244] using h1244)
  · have h1245 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1245 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1245] using h1245)
  · have h1246 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1246 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1246] using h1246)
  · have h1247 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1247 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1247] using h1247)
  · have h1248 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1248 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1248] using h1248)
  · have h1249 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1249 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1249] using h1249)
  · have h1250 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1250 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1250] using h1250)
  · have h1251 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1251 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1251] using h1251)
  · have h1252 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1252 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1252] using h1252)
  · have h1253 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1253 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1253] using h1253)
  · have h1254 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1254 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1254] using h1254)
  · have h1255 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1255 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1255] using h1255)
  · have h1256 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1256 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1256] using h1256)
  · have h1257 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1257 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1257] using h1257)
  · have h1258 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1258 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1258] using h1258)
  · have h1259 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1259 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1259] using h1259)
  · have h1260 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1260 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1260] using h1260)
  · have h1261 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1261 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1261] using h1261)
  · have h1262 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1262 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1262] using h1262)
  · have h1263 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1263 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1263] using h1263)

-- Slot 2

set_option maxHeartbeats 40000000 in
theorem schedule_bit_boolean_raw_slot2
    {air : C FBB ExtF} {row slot bit : ℕ}
    (hslot2 : slot = 2)
    (hbit : bit < 64)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    next_msg_schedule_w air slot bit row = 0 ∨
      next_msg_schedule_w air slot bit row = 1 := by
  subst hslot2
  rcases hs with ⟨_, _, _, _, h1250_1299, h1300_1349, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1250_1299 at h1250_1299
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1300_1349 at h1300_1349
  interval_cases bit
  · have h1276 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1276 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1276] using h1276)
  · have h1277 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1277 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1277] using h1277)
  · have h1278 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1278 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1278] using h1278)
  · have h1279 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1279 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1279] using h1279)
  · have h1280 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1280 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1280] using h1280)
  · have h1281 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1281 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1281] using h1281)
  · have h1282 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1282 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1282] using h1282)
  · have h1283 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1283 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1283] using h1283)
  · have h1284 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1284 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1284] using h1284)
  · have h1285 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1285 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1285] using h1285)
  · have h1286 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1286 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1286] using h1286)
  · have h1287 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1287 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1287] using h1287)
  · have h1288 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1288 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1288] using h1288)
  · have h1289 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1289 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1289] using h1289)
  · have h1290 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1290 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1290] using h1290)
  · have h1291 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1291 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1291] using h1291)
  · have h1292 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1292 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1292] using h1292)
  · have h1293 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1293 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1293] using h1293)
  · have h1294 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1294 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1294] using h1294)
  · have h1295 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1295 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1295] using h1295)
  · have h1296 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1296 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1296] using h1296)
  · have h1297 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1297 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1297] using h1297)
  · have h1298 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1298 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1298] using h1298)
  · have h1299 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1299 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1299] using h1299)
  · have h1300 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1300 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1300] using h1300)
  · have h1301 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1301 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1301] using h1301)
  · have h1302 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1302 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1302] using h1302)
  · have h1303 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1303 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1303] using h1303)
  · have h1304 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1304 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1304] using h1304)
  · have h1305 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1305 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1305] using h1305)
  · have h1306 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1306 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1306] using h1306)
  · have h1307 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1307 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1307] using h1307)
  · have h1308 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1308 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1308] using h1308)
  · have h1309 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1309 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1309] using h1309)
  · have h1310 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1310 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1310] using h1310)
  · have h1311 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1311 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1311] using h1311)
  · have h1312 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1312 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1312] using h1312)
  · have h1313 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1313 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1313] using h1313)
  · have h1314 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1314 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1314] using h1314)
  · have h1315 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1315 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1315] using h1315)
  · have h1316 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1316 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1316] using h1316)
  · have h1317 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1317 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1317] using h1317)
  · have h1318 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1318 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1318] using h1318)
  · have h1319 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1319 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1319] using h1319)
  · have h1320 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1320 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1320] using h1320)
  · have h1321 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1321 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1321] using h1321)
  · have h1322 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1322 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1322] using h1322)
  · have h1323 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1323 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1323] using h1323)
  · have h1324 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1324 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1324] using h1324)
  · have h1325 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1325 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1325] using h1325)
  · have h1326 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1326 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1326] using h1326)
  · have h1327 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1327 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1327] using h1327)
  · have h1328 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1328 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1328] using h1328)
  · have h1329 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1329 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1329] using h1329)
  · have h1330 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1330 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1330] using h1330)
  · have h1331 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1331 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1331] using h1331)
  · have h1332 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1332 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1332] using h1332)
  · have h1333 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1333 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1333] using h1333)
  · have h1334 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1334 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1334] using h1334)
  · have h1335 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1335 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1335] using h1335)
  · have h1336 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1336 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1336] using h1336)
  · have h1337 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1337 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1337] using h1337)
  · have h1338 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1338 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1338] using h1338)
  · have h1339 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1339 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1339] using h1339)

-- Slot 3

set_option maxHeartbeats 40000000 in
theorem schedule_bit_boolean_raw_slot3
    {air : C FBB ExtF} {row slot bit : ℕ}
    (hslot3 : slot = 3)
    (hbit : bit < 64)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    next_msg_schedule_w air slot bit row = 0 ∨
      next_msg_schedule_w air slot bit row = 1 := by
  subst hslot3
  rcases hs with ⟨_, _, _, _, _, _, h1350_1399, h1400_1449⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1350_1399 at h1350_1399
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1400_1449 at h1400_1449
  interval_cases bit
  · have h1352 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1352 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1352] using h1352)
  · have h1353 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1353 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1353] using h1353)
  · have h1354 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1354 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1354] using h1354)
  · have h1355 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1355 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1355] using h1355)
  · have h1356 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1356 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1356] using h1356)
  · have h1357 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1357 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1357] using h1357)
  · have h1358 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1358 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1358] using h1358)
  · have h1359 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1359 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1359] using h1359)
  · have h1360 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1360 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1360] using h1360)
  · have h1361 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1361 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1361] using h1361)
  · have h1362 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1362 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1362] using h1362)
  · have h1363 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1363 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1363] using h1363)
  · have h1364 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1364 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1364] using h1364)
  · have h1365 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1365 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1365] using h1365)
  · have h1366 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1366 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1366] using h1366)
  · have h1367 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1367 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1367] using h1367)
  · have h1368 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1368 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1368] using h1368)
  · have h1369 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1369 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1369] using h1369)
  · have h1370 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1370 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1370] using h1370)
  · have h1371 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1371 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1371] using h1371)
  · have h1372 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1372 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1372] using h1372)
  · have h1373 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1373 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1373] using h1373)
  · have h1374 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1374 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1374] using h1374)
  · have h1375 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1375 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1375] using h1375)
  · have h1376 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1376 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1376] using h1376)
  · have h1377 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1377 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1377] using h1377)
  · have h1378 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1378 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1378] using h1378)
  · have h1379 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1379 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1379] using h1379)
  · have h1380 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1380 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1380] using h1380)
  · have h1381 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1381 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1381] using h1381)
  · have h1382 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1382 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1382] using h1382)
  · have h1383 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1383 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1383] using h1383)
  · have h1384 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1384 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1384] using h1384)
  · have h1385 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1385 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1385] using h1385)
  · have h1386 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1386 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1386] using h1386)
  · have h1387 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1387 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1387] using h1387)
  · have h1388 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1388 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1388] using h1388)
  · have h1389 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1389 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1389] using h1389)
  · have h1390 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1390 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1390] using h1390)
  · have h1391 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1391 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1391] using h1391)
  · have h1392 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1392 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1392] using h1392)
  · have h1393 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1393 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1393] using h1393)
  · have h1394 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1394 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1394] using h1394)
  · have h1395 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1395 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1395] using h1395)
  · have h1396 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1396 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1396] using h1396)
  · have h1397 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1397 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1397] using h1397)
  · have h1398 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1398 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1398] using h1398)
  · have h1399 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1399 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1399] using h1399)
  · have h1400 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1400 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1400] using h1400)
  · have h1401 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1401 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1401] using h1401)
  · have h1402 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1402 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1402] using h1402)
  · have h1403 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1403 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1403] using h1403)
  · have h1404 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1404 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1404] using h1404)
  · have h1405 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1405 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1405] using h1405)
  · have h1406 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1406 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1406] using h1406)
  · have h1407 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1407 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1407] using h1407)
  · have h1408 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1408 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1408] using h1408)
  · have h1409 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1409 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1409] using h1409)
  · have h1410 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1410 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1410] using h1410)
  · have h1411 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1411 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1411] using h1411)
  · have h1412 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1412 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1412] using h1412)
  · have h1413 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1413 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1413] using h1413)
  · have h1414 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1414 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1414] using h1414)
  · have h1415 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1415 air row := by tauto
    exact bit_boolean_of_round_constraint hround_next (by simpa [constraint_1415] using h1415)

-- Raw dispatcher (all slots)

set_option maxHeartbeats 40000000 in
theorem schedule_bit_boolean_raw (air : C FBB ExtF) (row slot bit : ℕ)
    (hslot : slot < 4)
    (hbit : bit < 64)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    next_msg_schedule_w air slot bit row = 0 ∨
      next_msg_schedule_w air slot bit row = 1 := by
  interval_cases slot
  · exact schedule_bit_boolean_raw_slot0 rfl hbit hs hround_next
  · exact schedule_bit_boolean_raw_slot1 rfl hbit hs hround_next
  · exact schedule_bit_boolean_raw_slot2 rfl hbit hs hround_next
  · exact schedule_bit_boolean_raw_slot3 rfl hbit hs hround_next

-- Next-row wrapper

/-- Schedule word bits are boolean on round rows. -/
theorem schedule_bits_boolean (air : C FBB ExtF) (row : ℕ)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1) :
    ∀ slot bit, slot < 4 → bit < 64 →
      msg_schedule_w air slot bit (nextRow air row) = 0 ∨
      msg_schedule_w air slot bit (nextRow air row) = 1 := by
  intro slot bit hslot hbit
  simpa [next_msg_schedule_w_eq_nextRow air hrot slot bit row hrow] using
    schedule_bit_boolean_raw air row slot bit hslot hbit hs hround_next

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
