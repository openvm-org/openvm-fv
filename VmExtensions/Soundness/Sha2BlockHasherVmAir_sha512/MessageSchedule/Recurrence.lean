/-
  Layer B: Message Schedule Correctness (Recurrence)

  This SHA-512 recurrence slice covers the four successor-word limb equations
  and carry-buffer booleanness blocks extracted from the row-major schedule
  ranges `1112 .. 1415`.
-/
import VmExtensions.Soundness.Sha2BlockHasherVmAir_sha512.MessageSchedule.Core

set_option autoImplicit false
set_option maxHeartbeats 40000000

namespace Sha2BlockHasherVmAir_sha512.BlockSpec

open BabyBear
open Sha2BlockHasherVmAir_sha512.constraints

section MatrixProjection

variable {C : Type → Type → Type} {ExtF : Type} [Field ExtF] [Circuit FBB ExtF C]

/-! ### Isolated carry-bit extractors (slots 0–3) -/

theorem next_msg_schedule_carry_bits_raw_slot0_isolated
    {air : C FBB ExtF} {row byte : ℕ}
    (hs : schedule_constraints air row)
    (hbyte : byte < 8) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_carry_bit_constraint air row 0 byte := by
  rcases hs with ⟨_, h1100_1149, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1100_1149 at h1100_1149
  let h1101_1149 := h1100_1149.2
  let h1102_1149 := h1101_1149.2
  let h1103_1149 := h1102_1149.2
  let h1104_1149 := h1103_1149.2
  let h1105_1149 := h1104_1149.2
  let h1106_1149 := h1105_1149.2
  let h1107_1149 := h1106_1149.2
  let h1108_1149 := h1107_1149.2
  let h1109_1149 := h1108_1149.2
  let h1110_1149 := h1109_1149.2
  let h1111_1149 := h1110_1149.2
  let h1112_1149 := h1111_1149.2
  let h1113_1149 := h1112_1149.2
  let h1114_1149 := h1113_1149.2
  let h1115_1149 := h1114_1149.2
  let h1116_1149 := h1115_1149.2
  let h1117_1149 := h1116_1149.2
  let h1118_1149 := h1117_1149.2
  let h1119_1149 := h1118_1149.2
  let h1120_1149 := h1119_1149.2
  let h1121_1149 := h1120_1149.2
  let h1122_1149 := h1121_1149.2
  let h1123_1149 := h1122_1149.2
  have h1116 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1116 air row := h1116_1149.1
  have h1117 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1117 air row := h1117_1149.1
  have h1118 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1118 air row := h1118_1149.1
  have h1119 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1119 air row := h1119_1149.1
  have h1120 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1120 air row := h1120_1149.1
  have h1121 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1121 air row := h1121_1149.1
  have h1122 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1122 air row := h1122_1149.1
  have h1123 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1123 air row := h1123_1149.1
  interval_cases byte
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1116 air row
    exact h1116
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1117 air row
    exact h1117
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1118 air row
    exact h1118
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1119 air row
    exact h1119
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1120 air row
    exact h1120
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1121 air row
    exact h1121
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1122 air row
    exact h1122
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1123 air row
    exact h1123

theorem next_msg_schedule_carry_bits_raw_slot1_isolated
    {air : C FBB ExtF} {row byte : ℕ}
    (hs : schedule_constraints air row)
    (hbyte : byte < 8) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_carry_bit_constraint air row 1 byte := by
  rcases hs with ⟨_, _, h1150_1199, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1150_1199 at h1150_1199
  let h1151_1199 := h1150_1199.2
  let h1152_1199 := h1151_1199.2
  let h1153_1199 := h1152_1199.2
  let h1154_1199 := h1153_1199.2
  let h1155_1199 := h1154_1199.2
  let h1156_1199 := h1155_1199.2
  let h1157_1199 := h1156_1199.2
  let h1158_1199 := h1157_1199.2
  let h1159_1199 := h1158_1199.2
  let h1160_1199 := h1159_1199.2
  let h1161_1199 := h1160_1199.2
  let h1162_1199 := h1161_1199.2
  let h1163_1199 := h1162_1199.2
  let h1164_1199 := h1163_1199.2
  let h1165_1199 := h1164_1199.2
  let h1166_1199 := h1165_1199.2
  let h1167_1199 := h1166_1199.2
  let h1168_1199 := h1167_1199.2
  let h1169_1199 := h1168_1199.2
  let h1170_1199 := h1169_1199.2
  let h1171_1199 := h1170_1199.2
  let h1172_1199 := h1171_1199.2
  let h1173_1199 := h1172_1199.2
  let h1174_1199 := h1173_1199.2
  let h1175_1199 := h1174_1199.2
  let h1176_1199 := h1175_1199.2
  let h1177_1199 := h1176_1199.2
  let h1178_1199 := h1177_1199.2
  let h1179_1199 := h1178_1199.2
  let h1180_1199 := h1179_1199.2
  let h1181_1199 := h1180_1199.2
  let h1182_1199 := h1181_1199.2
  let h1183_1199 := h1182_1199.2
  let h1184_1199 := h1183_1199.2
  let h1185_1199 := h1184_1199.2
  let h1186_1199 := h1185_1199.2
  let h1187_1199 := h1186_1199.2
  let h1188_1199 := h1187_1199.2
  let h1189_1199 := h1188_1199.2
  let h1190_1199 := h1189_1199.2
  let h1191_1199 := h1190_1199.2
  let h1192_1199 := h1191_1199.2
  let h1193_1199 := h1192_1199.2
  let h1194_1199 := h1193_1199.2
  let h1195_1199 := h1194_1199.2
  let h1196_1199 := h1195_1199.2
  let h1197_1199 := h1196_1199.2
  let h1198_1199 := h1197_1199.2
  let h1199_1199 := h1198_1199.2
  have h1192 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1192 air row := h1192_1199.1
  have h1193 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1193 air row := h1193_1199.1
  have h1194 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1194 air row := h1194_1199.1
  have h1195 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1195 air row := h1195_1199.1
  have h1196 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1196 air row := h1196_1199.1
  have h1197 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1197 air row := h1197_1199.1
  have h1198 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1198 air row := h1198_1199.1
  have h1199 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1199 air row := h1199_1199
  interval_cases byte
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1192 air row
    exact h1192
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1193 air row
    exact h1193
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1194 air row
    exact h1194
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1195 air row
    exact h1195
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1196 air row
    exact h1196
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1197 air row
    exact h1197
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1198 air row
    exact h1198
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1199 air row
    exact h1199

theorem next_msg_schedule_carry_bits_raw_slot2_isolated
    {air : C FBB ExtF} {row byte : ℕ}
    (hs : schedule_constraints air row)
    (hbyte : byte < 8) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_carry_bit_constraint air row 2 byte := by
  rcases hs with ⟨_, _, _, _, h1250_1299, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1250_1299 at h1250_1299
  let h1251_1299 := h1250_1299.2
  let h1252_1299 := h1251_1299.2
  let h1253_1299 := h1252_1299.2
  let h1254_1299 := h1253_1299.2
  let h1255_1299 := h1254_1299.2
  let h1256_1299 := h1255_1299.2
  let h1257_1299 := h1256_1299.2
  let h1258_1299 := h1257_1299.2
  let h1259_1299 := h1258_1299.2
  let h1260_1299 := h1259_1299.2
  let h1261_1299 := h1260_1299.2
  let h1262_1299 := h1261_1299.2
  let h1263_1299 := h1262_1299.2
  let h1264_1299 := h1263_1299.2
  let h1265_1299 := h1264_1299.2
  let h1266_1299 := h1265_1299.2
  let h1267_1299 := h1266_1299.2
  let h1268_1299 := h1267_1299.2
  let h1269_1299 := h1268_1299.2
  let h1270_1299 := h1269_1299.2
  let h1271_1299 := h1270_1299.2
  let h1272_1299 := h1271_1299.2
  let h1273_1299 := h1272_1299.2
  let h1274_1299 := h1273_1299.2
  let h1275_1299 := h1274_1299.2
  have h1268 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1268 air row := h1268_1299.1
  have h1269 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1269 air row := h1269_1299.1
  have h1270 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1270 air row := h1270_1299.1
  have h1271 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1271 air row := h1271_1299.1
  have h1272 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1272 air row := h1272_1299.1
  have h1273 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1273 air row := h1273_1299.1
  have h1274 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1274 air row := h1274_1299.1
  have h1275 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1275 air row := h1275_1299.1
  interval_cases byte
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1268 air row
    exact h1268
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1269 air row
    exact h1269
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1270 air row
    exact h1270
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1271 air row
    exact h1271
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1272 air row
    exact h1272
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1273 air row
    exact h1273
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1274 air row
    exact h1274
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1275 air row
    exact h1275

theorem next_msg_schedule_carry_bits_raw_slot3_isolated
    {air : C FBB ExtF} {row byte : ℕ}
    (hs : schedule_constraints air row)
    (hbyte : byte < 8) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_carry_bit_constraint air row 3 byte := by
  rcases hs with ⟨_, _, _, _, _, h1300_1349, h1350_1399, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1300_1349 at h1300_1349
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1350_1399 at h1350_1399
  let h1301_1349 := h1300_1349.2
  let h1302_1349 := h1301_1349.2
  let h1303_1349 := h1302_1349.2
  let h1304_1349 := h1303_1349.2
  let h1305_1349 := h1304_1349.2
  let h1306_1349 := h1305_1349.2
  let h1307_1349 := h1306_1349.2
  let h1308_1349 := h1307_1349.2
  let h1309_1349 := h1308_1349.2
  let h1310_1349 := h1309_1349.2
  let h1311_1349 := h1310_1349.2
  let h1312_1349 := h1311_1349.2
  let h1313_1349 := h1312_1349.2
  let h1314_1349 := h1313_1349.2
  let h1315_1349 := h1314_1349.2
  let h1316_1349 := h1315_1349.2
  let h1317_1349 := h1316_1349.2
  let h1318_1349 := h1317_1349.2
  let h1319_1349 := h1318_1349.2
  let h1320_1349 := h1319_1349.2
  let h1321_1349 := h1320_1349.2
  let h1322_1349 := h1321_1349.2
  let h1323_1349 := h1322_1349.2
  let h1324_1349 := h1323_1349.2
  let h1325_1349 := h1324_1349.2
  let h1326_1349 := h1325_1349.2
  let h1327_1349 := h1326_1349.2
  let h1328_1349 := h1327_1349.2
  let h1329_1349 := h1328_1349.2
  let h1330_1349 := h1329_1349.2
  let h1331_1349 := h1330_1349.2
  let h1332_1349 := h1331_1349.2
  let h1333_1349 := h1332_1349.2
  let h1334_1349 := h1333_1349.2
  let h1335_1349 := h1334_1349.2
  let h1336_1349 := h1335_1349.2
  let h1337_1349 := h1336_1349.2
  let h1338_1349 := h1337_1349.2
  let h1339_1349 := h1338_1349.2
  let h1340_1349 := h1339_1349.2
  let h1341_1349 := h1340_1349.2
  let h1342_1349 := h1341_1349.2
  let h1343_1349 := h1342_1349.2
  let h1344_1349 := h1343_1349.2
  let h1345_1349 := h1344_1349.2
  let h1346_1349 := h1345_1349.2
  let h1347_1349 := h1346_1349.2
  let h1348_1349 := h1347_1349.2
  let h1349_1349 := h1348_1349.2
  let h1351_1399 := h1350_1399.2
  have h1344 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1344 air row := h1344_1349.1
  have h1345 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1345 air row := h1345_1349.1
  have h1346 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1346 air row := h1346_1349.1
  have h1347 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1347 air row := h1347_1349.1
  have h1348 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1348 air row := h1348_1349.1
  have h1349 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1349 air row := h1349_1349
  have h1350 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1350 air row := h1350_1399.1
  have h1351 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1351 air row := h1351_1399.1
  interval_cases byte
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1344 air row
    exact h1344
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1345 air row
    exact h1345
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1346 air row
    exact h1346
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1347 air row
    exact h1347
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1348 air row
    exact h1348
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1349 air row
    exact h1349
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1350 air row
    exact h1350
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1351 air row
    exact h1351

/-! ### Isolated recurrence extractors (slots 0–3) -/

theorem next_msg_schedule_recurrence_raw_slot0_isolated
    {air : C FBB ExtF} {row limb : ℕ}
    (hs : schedule_constraints air row)
    (hlimb : limb < 4) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_recurrence_constraint air row 0 limb := by
  rcases hs with ⟨_, h1100_1149, _, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1100_1149 at h1100_1149
  let h1101_1149 := h1100_1149.2
  let h1102_1149 := h1101_1149.2
  let h1103_1149 := h1102_1149.2
  let h1104_1149 := h1103_1149.2
  let h1105_1149 := h1104_1149.2
  let h1106_1149 := h1105_1149.2
  let h1107_1149 := h1106_1149.2
  let h1108_1149 := h1107_1149.2
  let h1109_1149 := h1108_1149.2
  let h1110_1149 := h1109_1149.2
  let h1111_1149 := h1110_1149.2
  let h1112_1149 := h1111_1149.2
  let h1113_1149 := h1112_1149.2
  let h1114_1149 := h1113_1149.2
  let h1115_1149 := h1114_1149.2
  have h1112 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1112 air row := h1112_1149.1
  have h1113 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1113 air row := h1113_1149.1
  have h1114 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1114 air row := h1114_1149.1
  have h1115 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1115 air row := h1115_1149.1
  interval_cases limb
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1112 air row
    exact h1112
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1113 air row
    exact h1113
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1114 air row
    exact h1114
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1115 air row
    exact h1115

theorem next_msg_schedule_recurrence_raw_slot1_isolated
    {air : C FBB ExtF} {row limb : ℕ}
    (hs : schedule_constraints air row)
    (hlimb : limb < 4) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_recurrence_constraint air row 1 limb := by
  rcases hs with ⟨_, _, h1150_1199, _, _, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1150_1199 at h1150_1199
  let h1151_1199 := h1150_1199.2
  let h1152_1199 := h1151_1199.2
  let h1153_1199 := h1152_1199.2
  let h1154_1199 := h1153_1199.2
  let h1155_1199 := h1154_1199.2
  let h1156_1199 := h1155_1199.2
  let h1157_1199 := h1156_1199.2
  let h1158_1199 := h1157_1199.2
  let h1159_1199 := h1158_1199.2
  let h1160_1199 := h1159_1199.2
  let h1161_1199 := h1160_1199.2
  let h1162_1199 := h1161_1199.2
  let h1163_1199 := h1162_1199.2
  let h1164_1199 := h1163_1199.2
  let h1165_1199 := h1164_1199.2
  let h1166_1199 := h1165_1199.2
  let h1167_1199 := h1166_1199.2
  let h1168_1199 := h1167_1199.2
  let h1169_1199 := h1168_1199.2
  let h1170_1199 := h1169_1199.2
  let h1171_1199 := h1170_1199.2
  let h1172_1199 := h1171_1199.2
  let h1173_1199 := h1172_1199.2
  let h1174_1199 := h1173_1199.2
  let h1175_1199 := h1174_1199.2
  let h1176_1199 := h1175_1199.2
  let h1177_1199 := h1176_1199.2
  let h1178_1199 := h1177_1199.2
  let h1179_1199 := h1178_1199.2
  let h1180_1199 := h1179_1199.2
  let h1181_1199 := h1180_1199.2
  let h1182_1199 := h1181_1199.2
  let h1183_1199 := h1182_1199.2
  let h1184_1199 := h1183_1199.2
  let h1185_1199 := h1184_1199.2
  let h1186_1199 := h1185_1199.2
  let h1187_1199 := h1186_1199.2
  let h1188_1199 := h1187_1199.2
  let h1189_1199 := h1188_1199.2
  let h1190_1199 := h1189_1199.2
  let h1191_1199 := h1190_1199.2
  have h1188 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1188 air row := h1188_1199.1
  have h1189 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1189 air row := h1189_1199.1
  have h1190 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1190 air row := h1190_1199.1
  have h1191 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1191 air row := h1191_1199.1
  interval_cases limb
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1188 air row
    exact h1188
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1189 air row
    exact h1189
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1190 air row
    exact h1190
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1191 air row
    exact h1191

theorem next_msg_schedule_recurrence_raw_slot2_isolated
    {air : C FBB ExtF} {row limb : ℕ}
    (hs : schedule_constraints air row)
    (hlimb : limb < 4) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_recurrence_constraint air row 2 limb := by
  rcases hs with ⟨_, _, _, _, h1250_1299, _, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1250_1299 at h1250_1299
  let h1251_1299 := h1250_1299.2
  let h1252_1299 := h1251_1299.2
  let h1253_1299 := h1252_1299.2
  let h1254_1299 := h1253_1299.2
  let h1255_1299 := h1254_1299.2
  let h1256_1299 := h1255_1299.2
  let h1257_1299 := h1256_1299.2
  let h1258_1299 := h1257_1299.2
  let h1259_1299 := h1258_1299.2
  let h1260_1299 := h1259_1299.2
  let h1261_1299 := h1260_1299.2
  let h1262_1299 := h1261_1299.2
  let h1263_1299 := h1262_1299.2
  let h1264_1299 := h1263_1299.2
  let h1265_1299 := h1264_1299.2
  let h1266_1299 := h1265_1299.2
  let h1267_1299 := h1266_1299.2
  have h1264 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1264 air row := h1264_1299.1
  have h1265 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1265 air row := h1265_1299.1
  have h1266 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1266 air row := h1266_1299.1
  have h1267 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1267 air row := h1267_1299.1
  interval_cases limb
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1264 air row
    exact h1264
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1265 air row
    exact h1265
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1266 air row
    exact h1266
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1267 air row
    exact h1267

theorem next_msg_schedule_recurrence_raw_slot3_isolated
    {air : C FBB ExtF} {row limb : ℕ}
    (hs : schedule_constraints air row)
    (hlimb : limb < 4) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_recurrence_constraint air row 3 limb := by
  rcases hs with ⟨_, _, _, _, _, h1300_1349, _, _⟩
  unfold Sha2BlockHasherVmAir_Sha512Config.extraction.constrain_rows_1300_1349 at h1300_1349
  let h1301_1349 := h1300_1349.2
  let h1302_1349 := h1301_1349.2
  let h1303_1349 := h1302_1349.2
  let h1304_1349 := h1303_1349.2
  let h1305_1349 := h1304_1349.2
  let h1306_1349 := h1305_1349.2
  let h1307_1349 := h1306_1349.2
  let h1308_1349 := h1307_1349.2
  let h1309_1349 := h1308_1349.2
  let h1310_1349 := h1309_1349.2
  let h1311_1349 := h1310_1349.2
  let h1312_1349 := h1311_1349.2
  let h1313_1349 := h1312_1349.2
  let h1314_1349 := h1313_1349.2
  let h1315_1349 := h1314_1349.2
  let h1316_1349 := h1315_1349.2
  let h1317_1349 := h1316_1349.2
  let h1318_1349 := h1317_1349.2
  let h1319_1349 := h1318_1349.2
  let h1320_1349 := h1319_1349.2
  let h1321_1349 := h1320_1349.2
  let h1322_1349 := h1321_1349.2
  let h1323_1349 := h1322_1349.2
  let h1324_1349 := h1323_1349.2
  let h1325_1349 := h1324_1349.2
  let h1326_1349 := h1325_1349.2
  let h1327_1349 := h1326_1349.2
  let h1328_1349 := h1327_1349.2
  let h1329_1349 := h1328_1349.2
  let h1330_1349 := h1329_1349.2
  let h1331_1349 := h1330_1349.2
  let h1332_1349 := h1331_1349.2
  let h1333_1349 := h1332_1349.2
  let h1334_1349 := h1333_1349.2
  let h1335_1349 := h1334_1349.2
  let h1336_1349 := h1335_1349.2
  let h1337_1349 := h1336_1349.2
  let h1338_1349 := h1337_1349.2
  let h1339_1349 := h1338_1349.2
  let h1340_1349 := h1339_1349.2
  let h1341_1349 := h1340_1349.2
  let h1342_1349 := h1341_1349.2
  let h1343_1349 := h1342_1349.2
  have h1340 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1340 air row := h1340_1349.1
  have h1341 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1341 air row := h1341_1349.1
  have h1342 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1342 air row := h1342_1349.1
  have h1343 : Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1343 air row := h1343_1349.1
  interval_cases limb
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1340 air row
    exact h1340
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1341 air row
    exact h1341
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1342 air row
    exact h1342
  · change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1343 air row
    exact h1343

/-! ### U16 limb helpers (from RecurrenceU16LimbRawAt) -/

private theorem next_msg_schedule_u16_limb_eq_nextScheduleBitsWord
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hlimb : limb < 4) :
    next_msg_schedule_u16_limb air slot limb row =
      composeU16Limb (nextScheduleBitsWord air row slot) ⟨limb, hlimb⟩ := by
  calc
    next_msg_schedule_u16_limb air slot limb row =
        ∑ i ∈ Finset.range 16, next_msg_schedule_w air slot (i + 16 * limb) row * 2 ^ i := by
          simp [next_msg_schedule_u16_limb]
    _ = composeU16Limb (nextScheduleBitsWord air row slot) ⟨limb, hlimb⟩ := by
          symm
          calc
            composeU16Limb (nextScheduleBitsWord air row slot) ⟨limb, hlimb⟩ =
                ∑ i ∈ Finset.range 16,
                  (if hi : i < 16 then
                    nextScheduleBitsWord air row slot ⟨i + 16 * limb, by omega⟩ * 2 ^ i
                   else 0) := by
                    simpa using composeU16Limb_range_eq (nextScheduleBitsWord air row slot)
                      ⟨limb, hlimb⟩
            _ = ∑ i ∈ Finset.range 16, next_msg_schedule_w air slot (i + 16 * limb) row * 2 ^ i := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hi16 : i < 16 := Finset.mem_range.mp hi
                  simp [nextScheduleBitsWord, hi16]

private theorem msg_schedule_small_sigma1_u16_limb_eq
    (air : C FBB ExtF) (row slot limb : ℕ)
    (_hslot : slot < 4)
    (hlimb : limb < 4) :
    msg_schedule_small_sigma1_u16_limb air slot limb row =
      composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row (slot + 2)))
        ⟨limb, hlimb⟩ := by
  symm
  calc
    composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row (slot + 2)))
        ⟨limb, hlimb⟩ =
        ∑ i ∈ Finset.range 16,
          (if hi : i < 16 then
            fieldSmallSigma1 (rawConcatScheduleBitsWord air row (slot + 2))
              ⟨i + 16 * limb, by omega⟩ *
              2 ^ i
           else 0) := by
            simpa using
              composeU16Limb_range_eq
                (fieldSmallSigma1 (rawConcatScheduleBitsWord air row (slot + 2))) ⟨limb, hlimb⟩
    _ = ∑ i ∈ Finset.range 16,
          msg_schedule_small_sigma1_bit air slot (i + 16 * limb) row * 2 ^ i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi16 : i < 16 := Finset.mem_range.mp hi
          by_cases hsource : slot + 2 < 4
          · simp [msg_schedule_small_sigma1_bit, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor,
              field_xor_expr, rawConcatScheduleBitsWord, raw_concat_schedule_bit, scheduleBitsWord,
              hsource, hi16]
          · simp [msg_schedule_small_sigma1_bit, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor,
              field_xor_expr, rawConcatScheduleBitsWord, raw_concat_schedule_bit, nextScheduleBitsWord,
              hsource, hi16]

theorem next_msg_schedule_recurrence_u16_limb_raw_at_isolated
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hs : schedule_constraints air row) :
    (if limb = 0 then 0 else next_msg_schedule_carry_value air slot (limb - 1) row) +
      msg_schedule_small_sigma1_u16_limb air slot limb row +
      next_msg_schedule_w7_u16_limb air slot limb row +
      intermed_12 air slot limb row =
    next_msg_schedule_u16_limb air slot limb row +
      next_msg_schedule_carry_value air slot limb row * (2 ^ 16 : ℕ) := by
  have hraw : Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_recurrence_constraint air row slot limb := by
    interval_cases slot
    · exact next_msg_schedule_recurrence_raw_slot0_isolated hs hlimb
    · exact next_msg_schedule_recurrence_raw_slot1_isolated hs hlimb
    · exact next_msg_schedule_recurrence_raw_slot2_isolated hs hlimb
    · exact next_msg_schedule_recurrence_raw_slot3_isolated hs hlimb
  interval_cases slot
  · interval_cases limb
    · have h1112 : constraint_1112 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1112 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1112 air row
        exact hraw
      have hpoly :
          composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 2)) ⟨0, by decide⟩ +
              schedule_helper_w_3 air 0 0 row +
              intermed_12 air 0 0 row -
            (composeU16Limb (nextScheduleBitsWord air row 0) ⟨0, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 0 0 row +
                2 * next_msg_schedule_carry_or_buffer air 0 1 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1112, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1112
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 0 0 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 0 0 (by decide)] using heq
    · have h1113 : constraint_1113 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1113 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1113 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 0 0 row +
              2 * next_msg_schedule_carry_or_buffer air 0 1 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 2)) ⟨1, by decide⟩ +
              schedule_helper_w_3 air 0 1 row +
              intermed_12 air 0 1 row -
            (composeU16Limb (nextScheduleBitsWord air row 0) ⟨1, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 0 2 row +
                2 * next_msg_schedule_carry_or_buffer air 0 3 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1113, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1113
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 0 1 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 0 1 (by decide)] using heq
    · have h1114 : constraint_1114 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1114 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1114 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 0 2 row +
              2 * next_msg_schedule_carry_or_buffer air 0 3 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 2)) ⟨2, by decide⟩ +
              schedule_helper_w_3 air 0 2 row +
              intermed_12 air 0 2 row -
            (composeU16Limb (nextScheduleBitsWord air row 0) ⟨2, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 0 4 row +
                2 * next_msg_schedule_carry_or_buffer air 0 5 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1114, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1114
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 0 2 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 0 2 (by decide)] using heq
    · have h1115 : constraint_1115 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1115 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1115 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 0 4 row +
              2 * next_msg_schedule_carry_or_buffer air 0 5 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 2)) ⟨3, by decide⟩ +
              schedule_helper_w_3 air 0 3 row +
              intermed_12 air 0 3 row -
            (composeU16Limb (nextScheduleBitsWord air row 0) ⟨3, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 0 6 row +
                2 * next_msg_schedule_carry_or_buffer air 0 7 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1115, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1115
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 0 3 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 0 3 (by decide)] using heq
  · interval_cases limb
    · have h1188 : constraint_1188 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1188 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1188 air row
        exact hraw
      have hpoly :
          composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 3)) ⟨0, by decide⟩ +
              schedule_helper_w_3 air 1 0 row +
              intermed_12 air 1 0 row -
            (composeU16Limb (nextScheduleBitsWord air row 1) ⟨0, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 1 0 row +
                2 * next_msg_schedule_carry_or_buffer air 1 1 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1188, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1188
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 1 0 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 1 0 (by decide)] using heq
    · have h1189 : constraint_1189 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1189 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1189 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 1 0 row +
              2 * next_msg_schedule_carry_or_buffer air 1 1 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 3)) ⟨1, by decide⟩ +
              schedule_helper_w_3 air 1 1 row +
              intermed_12 air 1 1 row -
            (composeU16Limb (nextScheduleBitsWord air row 1) ⟨1, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 1 2 row +
                2 * next_msg_schedule_carry_or_buffer air 1 3 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1189, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1189
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 1 1 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 1 1 (by decide)] using heq
    · have h1190 : constraint_1190 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1190 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1190 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 1 2 row +
              2 * next_msg_schedule_carry_or_buffer air 1 3 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 3)) ⟨2, by decide⟩ +
              schedule_helper_w_3 air 1 2 row +
              intermed_12 air 1 2 row -
            (composeU16Limb (nextScheduleBitsWord air row 1) ⟨2, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 1 4 row +
                2 * next_msg_schedule_carry_or_buffer air 1 5 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1190, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1190
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 1 2 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 1 2 (by decide)] using heq
    · have h1191 : constraint_1191 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1191 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1191 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 1 4 row +
              2 * next_msg_schedule_carry_or_buffer air 1 5 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 3)) ⟨3, by decide⟩ +
              schedule_helper_w_3 air 1 3 row +
              intermed_12 air 1 3 row -
            (composeU16Limb (nextScheduleBitsWord air row 1) ⟨3, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 1 6 row +
                2 * next_msg_schedule_carry_or_buffer air 1 7 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1191, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1191
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 1 3 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 1 3 (by decide)] using heq
  · interval_cases limb
    · have h1264 : constraint_1264 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1264 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1264 air row
        exact hraw
      have hpoly :
          composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 4)) ⟨0, by decide⟩ +
              schedule_helper_w_3 air 2 0 row +
              intermed_12 air 2 0 row -
            (composeU16Limb (nextScheduleBitsWord air row 2) ⟨0, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 2 0 row +
                2 * next_msg_schedule_carry_or_buffer air 2 1 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1264, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1264
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 2 0 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 2 0 (by decide)] using heq
    · have h1265 : constraint_1265 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1265 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1265 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 2 0 row +
              2 * next_msg_schedule_carry_or_buffer air 2 1 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 4)) ⟨1, by decide⟩ +
              schedule_helper_w_3 air 2 1 row +
              intermed_12 air 2 1 row -
            (composeU16Limb (nextScheduleBitsWord air row 2) ⟨1, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 2 2 row +
                2 * next_msg_schedule_carry_or_buffer air 2 3 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1265, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1265
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 2 1 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 2 1 (by decide)] using heq
    · have h1266 : constraint_1266 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1266 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1266 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 2 2 row +
              2 * next_msg_schedule_carry_or_buffer air 2 3 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 4)) ⟨2, by decide⟩ +
              schedule_helper_w_3 air 2 2 row +
              intermed_12 air 2 2 row -
            (composeU16Limb (nextScheduleBitsWord air row 2) ⟨2, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 2 4 row +
                2 * next_msg_schedule_carry_or_buffer air 2 5 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1266, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1266
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 2 2 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 2 2 (by decide)] using heq
    · have h1267 : constraint_1267 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1267 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1267 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 2 4 row +
              2 * next_msg_schedule_carry_or_buffer air 2 5 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 4)) ⟨3, by decide⟩ +
              schedule_helper_w_3 air 2 3 row +
              intermed_12 air 2 3 row -
            (composeU16Limb (nextScheduleBitsWord air row 2) ⟨3, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 2 6 row +
                2 * next_msg_schedule_carry_or_buffer air 2 7 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1267, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          schedule_helper_w_3, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1267
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 2 3 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 2 3 (by decide)] using heq
  · interval_cases limb
    · have h1340 : constraint_1340 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1340 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1340 air row
        exact hraw
      have hpoly :
          composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 5)) ⟨0, by decide⟩ +
              msg_schedule_u16_limb air 0 0 row +
              intermed_12 air 3 0 row -
            (composeU16Limb (nextScheduleBitsWord air row 3) ⟨0, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 3 0 row +
                2 * next_msg_schedule_carry_or_buffer air 3 1 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1340, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          msg_schedule_u16_limb, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1340
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 3 0 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 3 0 (by decide)] using heq
    · have h1341 : constraint_1341 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1341 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1341 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 3 0 row +
              2 * next_msg_schedule_carry_or_buffer air 3 1 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 5)) ⟨1, by decide⟩ +
              msg_schedule_u16_limb air 0 1 row +
              intermed_12 air 3 1 row -
            (composeU16Limb (nextScheduleBitsWord air row 3) ⟨1, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 3 2 row +
                2 * next_msg_schedule_carry_or_buffer air 3 3 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1341, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          msg_schedule_u16_limb, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1341
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 3 1 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 3 1 (by decide)] using heq
    · have h1342 : constraint_1342 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1342 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1342 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 3 2 row +
              2 * next_msg_schedule_carry_or_buffer air 3 3 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 5)) ⟨2, by decide⟩ +
              msg_schedule_u16_limb air 0 2 row +
              intermed_12 air 3 2 row -
            (composeU16Limb (nextScheduleBitsWord air row 3) ⟨2, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 3 4 row +
                2 * next_msg_schedule_carry_or_buffer air 3 5 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1342, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          msg_schedule_u16_limb, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1342
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 3 2 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 3 2 (by decide)] using heq
    · have h1343 : constraint_1343 air row := by
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1343 air row at hraw
        change Sha2BlockHasherVmAir_Sha512Config.extraction.constraint_1343 air row
        exact hraw
      have hpoly :
          (next_msg_schedule_carry_or_buffer air 3 4 row +
              2 * next_msg_schedule_carry_or_buffer air 3 5 row) +
              composeU16Limb (fieldSmallSigma1 (rawConcatScheduleBitsWord air row 5)) ⟨3, by decide⟩ +
              msg_schedule_u16_limb air 0 3 row +
              intermed_12 air 3 3 row -
            (composeU16Limb (nextScheduleBitsWord air row 3) ⟨3, by decide⟩ +
              (next_msg_schedule_carry_or_buffer air 3 6 row +
                2 * next_msg_schedule_carry_or_buffer air 3 7 row) * (2 ^ 16 : ℕ)) = 0 := by
        simpa [constraint_1343, rawConcatScheduleBitsWord, nextScheduleBitsWord, scheduleBitsWord,
          composeU16Limb_range_eq, fieldSmallSigma1, fieldRotr, fieldShr, fieldXor3_poly,
          msg_schedule_u16_limb, intermed_12, next_msg_schedule_carry_or_buffer, Finset.sum_range_succ]
          using h1343
      have heq := sub_eq_zero.mp hpoly
      simpa [next_msg_schedule_w7_u16_limb, next_msg_schedule_carry_value,
        msg_schedule_small_sigma1_u16_limb_eq air row 3 3 (by decide) (by decide),
        next_msg_schedule_u16_limb_eq_nextScheduleBitsWord air row 3 3 (by decide)] using heq

/-! ### Main Recurrence theorems -/

private theorem next_msg_schedule_u16_limb_eq
    (air : C FBB ExtF) (row slot limb : ℕ)
    (_hslot : slot < 4)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air) :
    next_msg_schedule_u16_limb air slot limb row =
      composeU16Limb (scheduleBitsWord air (nextRow air row) slot) ⟨limb, hlimb⟩ := by
  calc
    next_msg_schedule_u16_limb air slot limb row =
        ∑ i ∈ Finset.range 16,
          msg_schedule_w air slot (i + 16 * limb) (nextRow air row) * 2 ^ i := by
            rw [next_msg_schedule_u16_limb]
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [next_msg_schedule_w_eq_nextRow air hrot slot (i + 16 * limb) row hrow]
    _ = composeU16Limb (scheduleBitsWord air (nextRow air row) slot) ⟨limb, hlimb⟩ := by
          symm
          calc
            composeU16Limb (scheduleBitsWord air (nextRow air row) slot) ⟨limb, hlimb⟩ =
                ∑ i ∈ Finset.range 16,
                  (if hi : i < 16 then
                    scheduleBitsWord air (nextRow air row) slot ⟨i + 16 * limb, by omega⟩ *
                      2 ^ i
                   else 0) := by
                    simpa using
                      composeU16Limb_range_eq (scheduleBitsWord air (nextRow air row) slot)
                        ⟨limb, hlimb⟩
            _ = ∑ i ∈ Finset.range 16,
                  msg_schedule_w air slot (i + 16 * limb) (nextRow air row) * 2 ^ i := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    have hi16 : i < 16 := Finset.mem_range.mp hi
                    simp [scheduleBitsWord, hi16]

private theorem next_msg_schedule_carry_bits_raw
    {air : C FBB ExtF} {row slot byte : ℕ}
    (hs : schedule_constraints air row)
    (_hslot : slot < 4) (hbyte : byte < 8) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_carry_bit_constraint air row slot byte := by
  interval_cases slot
  · exact next_msg_schedule_carry_bits_raw_slot0_isolated hs hbyte
  · exact next_msg_schedule_carry_bits_raw_slot1_isolated hs hbyte
  · exact next_msg_schedule_carry_bits_raw_slot2_isolated hs hbyte
  · exact next_msg_schedule_carry_bits_raw_slot3_isolated hs hbyte

private theorem next_msg_schedule_recurrence_raw
    {air : C FBB ExtF} {row slot limb : ℕ}
    (hs : schedule_constraints air row)
    (_hslot : slot < 4) (hlimb : limb < 4) :
    Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_recurrence_constraint air row slot limb := by
  interval_cases slot
  · exact next_msg_schedule_recurrence_raw_slot0_isolated hs hlimb
  · exact next_msg_schedule_recurrence_raw_slot1_isolated hs hlimb
  · exact next_msg_schedule_recurrence_raw_slot2_isolated hs hlimb
  · exact next_msg_schedule_recurrence_raw_slot3_isolated hs hlimb

theorem next_msg_schedule_carry_bit_boolean_raw_at (air : C FBB ExtF) (row slot byte : ℕ)
    (hslot : slot < 4)
    (hbyte : byte < 8)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    next_msg_schedule_carry_or_buffer air slot byte row = 0 ∨
      next_msg_schedule_carry_or_buffer air slot byte row = 1 := by
  have hraw := next_msg_schedule_carry_bits_raw hs hslot hbyte
  have hpoly :
      next_msg_schedule_carry_or_buffer air slot byte row *
        (next_msg_schedule_carry_or_buffer air slot byte row - 1) = 0 := by
    interval_cases slot <;> interval_cases byte <;>
      simpa [Sha2BlockHasherVmAir_Sha512Config.extraction.raw_next_msg_schedule_carry_bit_constraint,
        next_msg_schedule_carry_bit_constraint, hround_next, hnot_first4_next,
        constraint_1116, constraint_1117, constraint_1118, constraint_1119,
        constraint_1120, constraint_1121, constraint_1122, constraint_1123,
        constraint_1192, constraint_1193, constraint_1194, constraint_1195,
        constraint_1196, constraint_1197, constraint_1198, constraint_1199,
        constraint_1268, constraint_1269, constraint_1270, constraint_1271,
        constraint_1272, constraint_1273, constraint_1274, constraint_1275,
        constraint_1344, constraint_1345, constraint_1346, constraint_1347,
        constraint_1348, constraint_1349, constraint_1350, constraint_1351] using hraw
  exact bit_boolean_of_sq_eq_zero _ hpoly

theorem next_msg_schedule_carry_bit_boolean_raw (air : C FBB ExtF) (row byte : ℕ)
    (hbyte : byte < 8)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    next_msg_schedule_carry_or_buffer air 0 byte row = 0 ∨
      next_msg_schedule_carry_or_buffer air 0 byte row = 1 := by
  exact next_msg_schedule_carry_bit_boolean_raw_at air row 0 byte (by omega) hbyte hs hround_next
    hnot_first4_next

/-- The first successor-word carry bits are boolean on schedule-expansion rows. -/
theorem next_msg_schedule_carry_bits_boolean_at (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    (msg_schedule_carry_or_buffer air slot (2 * limb) (nextRow air row) = 0 ∨
      msg_schedule_carry_or_buffer air slot (2 * limb) (nextRow air row) = 1) ∧
    (msg_schedule_carry_or_buffer air slot (2 * limb + 1) (nextRow air row) = 0 ∨
      msg_schedule_carry_or_buffer air slot (2 * limb + 1) (nextRow air row) = 1) := by
  have hb0 :=
    next_msg_schedule_carry_bit_boolean_raw_at air row slot (2 * limb) hslot (by omega) hs
      hround_next
      hnot_first4_next
  have hb1 :=
    next_msg_schedule_carry_bit_boolean_raw_at air row slot (2 * limb + 1) hslot (by omega) hs
      hround_next
      hnot_first4_next
  refine ⟨?_, ?_⟩
  · simpa [next_msg_schedule_carry_or_buffer_eq_nextRow air hrot slot (2 * limb) row hrow] using hb0
  · simpa [next_msg_schedule_carry_or_buffer_eq_nextRow air hrot slot (2 * limb + 1) row hrow]
      using hb1

/-- The first successor-word carry bits are boolean on schedule-expansion rows. -/
theorem next_msg_schedule_carry_bits_boolean (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    (msg_schedule_carry_or_buffer air 0 (2 * limb) (nextRow air row) = 0 ∨
      msg_schedule_carry_or_buffer air 0 (2 * limb) (nextRow air row) = 1) ∧
    (msg_schedule_carry_or_buffer air 0 (2 * limb + 1) (nextRow air row) = 0 ∨
      msg_schedule_carry_or_buffer air 0 (2 * limb + 1) (nextRow air row) = 1) := by
  exact next_msg_schedule_carry_bits_boolean_at air row 0 limb (by omega) hlimb hrow hrot hs
    hround_next hnot_first4_next

/-- The decoded first successor-word carry value lies in `{0,1,2,3}` on
    schedule-expansion rows. -/
theorem next_msg_schedule_carry_value_lt_four_at (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    (scheduleCarryValue air (nextRow air row) slot limb).val < 4 := by
  rcases
      next_msg_schedule_carry_bits_boolean_at air row slot limb hslot hlimb hrow hrot hs hround_next
        hnot_first4_next with
    ⟨hb0, hb1⟩
  rcases hb0 with hb0 | hb0 <;> rcases hb1 with hb1 | hb1 <;>
    simp [scheduleCarryValue, hb0, hb1]

/-- The decoded first successor-word carry value lies in `{0,1,2,3}` on
    schedule-expansion rows. -/
theorem next_msg_schedule_carry_value_lt_four (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row)
    (hround_next : next_is_round_row air row = 1)
    (hnot_first4_next : next_is_first_4_rows air row = 0) :
    (scheduleCarryValue air (nextRow air row) 0 limb).val < 4 := by
  exact next_msg_schedule_carry_value_lt_four_at air row 0 limb (by omega) hlimb hrow hrot hs
    hround_next hnot_first4_next

/-- Raw recurrence equation for the four 16-bit limbs of successor slot
    `slot`. -/
theorem next_msg_schedule_recurrence_u16_limb_raw_at
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hs : schedule_constraints air row) :
    (if limb = 0 then 0 else next_msg_schedule_carry_value air slot (limb - 1) row) +
      msg_schedule_small_sigma1_u16_limb air slot limb row +
      next_msg_schedule_w7_u16_limb air slot limb row +
      intermed_12 air slot limb row =
    next_msg_schedule_u16_limb air slot limb row +
      next_msg_schedule_carry_value air slot limb row * (2 ^ 16 : ℕ) := by
  exact next_msg_schedule_recurrence_u16_limb_raw_at_isolated air row slot limb hslot hlimb hs

/-- Raw recurrence equation for the four 16-bit limbs of the successor word
    `next.message_schedule.w[0]`. -/
theorem next_msg_schedule_recurrence_u16_limb_raw (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hs : schedule_constraints air row) :
    (if limb = 0 then 0 else next_msg_schedule_carry_value air 0 (limb - 1) row) +
      msg_schedule_small_sigma1_u16_limb air 0 limb row +
      schedule_helper_w_3 air 0 limb row +
      intermed_12 air 0 limb row =
    next_msg_schedule_u16_limb air 0 limb row +
      next_msg_schedule_carry_value air 0 limb row * (2 ^ 16 : ℕ) := by
  simpa [next_msg_schedule_w7_u16_limb] using
    next_msg_schedule_recurrence_u16_limb_raw_at air row 0 limb (by omega) hlimb hs

/-- Transport the raw successor-word recurrence onto the actual next row. -/
theorem next_msg_schedule_recurrence_u16_limb_at
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row) :
    (if limb = 0 then 0 else scheduleCarryValue air (nextRow air row) slot (limb - 1)) +
      composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) ⟨limb, hlimb⟩ +
      next_msg_schedule_w7_u16_limb air slot limb row +
      intermed_12 air slot limb row =
    composeU16Limb (scheduleBitsWord air (nextRow air row) slot) ⟨limb, hlimb⟩ +
      scheduleCarryValue air (nextRow air row) slot limb * (2 ^ 16 : ℕ) := by
  have hraw := next_msg_schedule_recurrence_u16_limb_raw_at air row slot limb hslot hlimb hs
  have hsource :
      rawConcatScheduleBitsWord air row (slot + 2) =
        concatScheduleBitsWord air row (slot + 2) :=
    rawConcatScheduleBitsWord_eq_concatScheduleBitsWord air row (slot + 2) hrot hrow
  have hsigma :
      msg_schedule_small_sigma1_u16_limb air slot limb row =
        composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2)))
          ⟨limb, hlimb⟩ := by
    simpa [hsource] using msg_schedule_small_sigma1_u16_limb_eq air row slot limb hslot hlimb
  have hnext_limb := next_msg_schedule_u16_limb_eq air row slot limb hslot hlimb hrow hrot
  have hcarry :
      next_msg_schedule_carry_value air slot limb row =
        scheduleCarryValue air (nextRow air row) slot limb := by
    simpa [next_msg_schedule_carry_value] using
      nextScheduleCarryValue_eq_scheduleCarryValue_nextRow air row slot limb hrot hrow
  have hcarry_prev :
      (if limb = 0 then 0 else next_msg_schedule_carry_value air slot (limb - 1) row) =
        (if limb = 0 then 0 else scheduleCarryValue air (nextRow air row) slot (limb - 1)) := by
    by_cases hzero : limb = 0
    · simp [hzero]
    · simp [hzero]
      simpa [next_msg_schedule_carry_value] using
        nextScheduleCarryValue_eq_scheduleCarryValue_nextRow air row slot (limb - 1) hrot hrow
  rw [hcarry_prev, hsigma, hnext_limb, hcarry] at hraw
  exact hraw

/-- Transport the raw successor-word recurrence onto the actual next row. -/
theorem next_msg_schedule_recurrence_u16_limb (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row) :
    (if limb = 0 then 0 else scheduleCarryValue air (nextRow air row) 0 (limb - 1)) +
      composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) ⟨limb, hlimb⟩ +
      schedule_helper_w_3 air 0 limb row +
      intermed_12 air 0 limb row =
    composeU16Limb (scheduleBitsWord air (nextRow air row) 0) ⟨limb, hlimb⟩ +
      scheduleCarryValue air (nextRow air row) 0 limb * (2 ^ 16 : ℕ) := by
  simpa [next_msg_schedule_w7_u16_limb] using
    next_msg_schedule_recurrence_u16_limb_at air row 0 limb (by omega) hlimb hrow hrot hs

/-- Repackage the successor-word recurrence with the generic `w[t-7]` limb
    surfaced through `scheduleW7U16Limb`. -/
theorem next_msg_schedule_recurrence_with_w7_at
    (air : C FBB ExtF) (row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row) :
    (if limb = 0 then 0 else scheduleCarryValue air (nextRow air row) slot (limb - 1)) +
      composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row (slot + 2))) ⟨limb, hlimb⟩ +
      scheduleW7U16Limb air row slot limb +
      intermed_12 air slot limb row =
    composeU16Limb (scheduleBitsWord air (nextRow air row) slot) ⟨limb, hlimb⟩ +
      scheduleCarryValue air (nextRow air row) slot limb * (2 ^ 16 : ℕ) := by
  have hrec :=
    next_msg_schedule_recurrence_u16_limb_at air row slot limb hslot hlimb hrow hrot hs
  by_cases hslot_lt3 : slot < 3
  · simpa [next_msg_schedule_w7_u16_limb, scheduleW7U16Limb, hslot_lt3] using hrec
  · have hslot_eq3 : slot = 3 := by
      omega
    have hmsg :
        msg_schedule_u16_limb air 0 limb row =
          concatScheduleU16Limb air row 0 limb := by
      exact msg_schedule_u16_limb_eq_concatScheduleU16Limb air row 0 limb (by omega) hlimb
    simpa [next_msg_schedule_w7_u16_limb, scheduleW7U16Limb, hslot_lt3, hslot_eq3, hmsg] using
      hrec

/-- Repackage the exposed successor-word recurrence with the `w[t-7]` limb
    surfaced through `scheduleW7U16Limb`. -/
theorem next_msg_schedule_word0_recurrence_with_w7
    (air : C FBB ExtF) (row limb : ℕ)
    (hlimb : limb < 4)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hs : schedule_constraints air row) :
    (if limb = 0 then 0 else scheduleCarryValue air (nextRow air row) 0 (limb - 1)) +
      composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) ⟨limb, hlimb⟩ +
      scheduleW7U16Limb air row 0 limb +
      intermed_12 air 0 limb row =
    composeU16Limb (scheduleBitsWord air (nextRow air row) 0) ⟨limb, hlimb⟩ +
      scheduleCarryValue air (nextRow air row) 0 limb * (2 ^ 16 : ℕ) := by
  simpa [scheduleW7U16Limb] using
    next_msg_schedule_recurrence_u16_limb air row limb hlimb hrow hrot hs

/-- The generic `w[t-7]` limb source is the previous row's concatenated
    schedule window at offset `slot + 1`. -/
theorem schedule_w7_u16_limb_from_concat_prev_at
    (air : C FBB ExtF) (start row slot limb : ℕ)
    (hslot : slot < 4)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    scheduleW7U16Limb air row slot limb =
      concatScheduleU16Limb air (prevRow air row) (slot + 1) limb := by
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have hprev_le : prevRow air row ≤ Circuit.last_row air := by
    rw [hprev_eq]
    omega
  have hprev_next : nextRow air (prevRow air row) = row := by
    rw [hprev_eq, nextRow]
    have hne : row - 1 ≠ Circuit.last_row air := by
      omega
    simp [hne]
    omega
  have hprev_round : is_round_row air (prevRow air row) = 1 := by
    have hoffset : prevRow air row - start < 20 := by
      rw [hprev_eq]
      omega
    have hshape_prev := hshape.2.1 (prevRow air row - start) hoffset
    have hrow_eq : start + (prevRow air row - start) = prevRow air row := by
      omega
    simpa [hrow_eq] using hshape_prev.2.1
  interval_cases slot
  · have hw3 :=
      w3_helper_correct air (prevRow air row) 0 limb (by omega) hlimb hprev_le hrot
        (hsc (prevRow air row)) hprev_round
    rw [hprev_next] at hw3
    simpa [scheduleW7U16Limb] using hw3
  ·
    have hw3 :=
      w3_helper_correct air (prevRow air row) 1 limb (by omega) hlimb hprev_le hrot
        (hsc (prevRow air row)) hprev_round
    rw [hprev_next] at hw3
    simpa [scheduleW7U16Limb] using hw3
  ·
    have hw3 :=
      w3_helper_correct air (prevRow air row) 2 limb (by omega) hlimb hprev_le hrot
        (hsc (prevRow air row)) hprev_round
    rw [hprev_next] at hw3
    simpa [scheduleW7U16Limb] using hw3
  · have hmsg :
        concatScheduleU16Limb air row 0 limb =
          concatScheduleU16Limb air (prevRow air row) 4 limb := by
      simp [concatScheduleU16Limb, hlimb, concatScheduleBitsWord, hprev_next]
    simp [scheduleW7U16Limb, hmsg]

/-- On the first exposed successor-word slice, the `w[t-7]` limb comes from the
    `w_3` helper carrying the predecessor row's local slot `1`. -/
theorem schedule_w7_u16_limb_from_helper
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    scheduleW7U16Limb air row 0 limb =
      concatScheduleU16Limb air (prevRow air row) 1 limb := by
  simpa using
    schedule_w7_u16_limb_from_concat_prev_at air start row 0 limb (by omega) hlimb hwindow hrot
      hshape hsc hnext hnext_bound

/-- Re-index the first exposed SHA-512 `w[t-7]` limb onto its block-local
    source row/slot. -/
theorem schedule_w7_u16_limb_from_source
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4
    scheduleW7U16Limb air row 0 limb =
      concatScheduleU16Limb air (start + (t - 7) / 4) ((t - 7) % 4) limb := by
  dsimp
  have hw7 :=
    schedule_w7_u16_limb_from_helper air start row limb hlimb hwindow hrot hshape hsc hnext
      hnext_bound
  have hsupp : start + 20 ≤ Circuit.last_row air := by
    simpa [blockWindowSupported] using hwindow
  have hrow_lt_last : row < Circuit.last_row air := by
    by_cases hlast : row = Circuit.last_row air
    · have hzero : nextRow air row = 0 := by
        simp [nextRow, hlast]
      omega
    · have hsucc : nextRow air row = row + 1 := by
        simp [nextRow, hlast]
      omega
  have hnext_succ : nextRow air row = row + 1 := by
    simp [nextRow, hrow_lt_last.ne]
  have hrow_pos : 0 < row := by
    omega
  have hprev_eq : prevRow air row = row - 1 := by
    simp [prevRow, Nat.ne_of_gt hrow_pos]
  have htarget_row :
      start + ((((nextRow air row - start) * 4) - 7) / 4) = prevRow air row := by
    rw [hprev_eq, hnext_succ]
    omega
  have htarget_slot :
      ((((nextRow air row - start) * 4) - 7) % 4) = 1 := by
    rw [hnext_succ]
    omega
  rw [htarget_row, htarget_slot]
  exact hw7

/-- The first exposed successor-word recurrence with `w[t-7]` rewritten onto
    the block-local source row/slot. -/
theorem next_msg_schedule_word0_recurrence_from_w7_source
    (air : C FBB ExtF) (start row limb : ℕ)
    (hlimb : limb < 4)
    (hwindow : blockWindowSupported air start)
    (hrow : row ≤ Circuit.last_row air)
    (hrot : rotation_consistent air)
    (hshape : blockWindowHasShape air start)
    (hsc : ∀ r, schedule_constraints air r)
    (hnext : start + 4 ≤ nextRow air row)
    (hnext_bound : nextRow air row ≤ start + 19) :
    let t := (nextRow air row - start) * 4
    (if limb = 0 then 0 else scheduleCarryValue air (nextRow air row) 0 (limb - 1)) +
      composeU16Limb (fieldSmallSigma1 (concatScheduleBitsWord air row 2)) ⟨limb, hlimb⟩ +
      concatScheduleU16Limb air (start + (t - 7) / 4) ((t - 7) % 4) limb +
      intermed_12 air 0 limb row =
    composeU16Limb (scheduleBitsWord air (nextRow air row) 0) ⟨limb, hlimb⟩ +
      scheduleCarryValue air (nextRow air row) 0 limb * (2 ^ 16 : ℕ) := by
  dsimp
  rw [← schedule_w7_u16_limb_from_source air start row limb hlimb hwindow hrot hshape hsc hnext
    hnext_bound]
  exact next_msg_schedule_word0_recurrence_with_w7 air row limb hlimb hrow hrot (hsc row)

end MatrixProjection

end Sha2BlockHasherVmAir_sha512.BlockSpec
