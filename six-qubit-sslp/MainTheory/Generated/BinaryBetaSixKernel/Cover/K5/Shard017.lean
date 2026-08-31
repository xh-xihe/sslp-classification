-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard017

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_2_2_2_2_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1272
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1273

theorem cover_p_2_2_2_2_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1274

theorem cover_p_2_2_2_3_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1275
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1276
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1277
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1278
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1279

theorem cover_p_2_2_2_3_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1280
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1281
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1282
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1283

theorem cover_p_2_2_2_3_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1284
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1285
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1286

theorem cover_p_2_2_2_3_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1287
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1288

theorem cover_p_2_2_2_3_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1289

theorem cover_p_2_2_2_4_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1290
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1291
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1292
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1293

theorem cover_p_2_2_2_4_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1294
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1295
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1296

theorem cover_p_2_2_2_4_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1297
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1298

theorem cover_p_2_2_2_4_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1299

theorem cover_p_2_2_2_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1300
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1301
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1302

theorem cover_p_2_2_2_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1303
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1304

theorem cover_p_2_2_2_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1305

theorem cover_p_2_2_2_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1306
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1307

theorem cover_p_2_2_2_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1308

theorem cover_p_2_2_2_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1309

theorem cover_p_2_2_3_3_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1310
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard081.canonicalBound_1311
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1312
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1313
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1314

theorem cover_p_2_2_3_3_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1315
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1316
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1317
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1318

theorem cover_p_2_2_3_3_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1319
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1320
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1321

theorem cover_p_2_2_3_3_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1322
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1323

theorem cover_p_2_2_3_3_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 3 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1324

theorem cover_p_2_2_3_4_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1325
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1326
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard082.canonicalBound_1327
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1328

theorem cover_p_2_2_3_4_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1329
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1330
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1331

theorem cover_p_2_2_3_4_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1332
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1333

theorem cover_p_2_2_3_4_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 4 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1334

theorem cover_p_2_2_3_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1335
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1336
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1337

theorem cover_p_2_2_3_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1338
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1339

theorem cover_p_2_2_3_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1340

theorem cover_p_2_2_3_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1341
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1342

theorem cover_p_2_2_3_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard083.canonicalBound_1343

theorem cover_p_2_2_3_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1344

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard017
