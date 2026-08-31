-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard088

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard018

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_2_2_4_4_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1345
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1346
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1347
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1348

theorem cover_p_2_2_4_4_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1349
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1350
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1351

theorem cover_p_2_2_4_4_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1352
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1353

theorem cover_p_2_2_4_4_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1354

theorem cover_p_2_2_4_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1355
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1356
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1357

theorem cover_p_2_2_4_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1358
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1359

theorem cover_p_2_2_4_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1360

theorem cover_p_2_2_4_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1361
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1362

theorem cover_p_2_2_4_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1363

theorem cover_p_2_2_4_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1364

theorem cover_p_2_2_5_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1365
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1366
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1367

theorem cover_p_2_2_5_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1368
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1369

theorem cover_p_2_2_5_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1370

theorem cover_p_2_2_5_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1371
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1372

theorem cover_p_2_2_5_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1373

theorem cover_p_2_2_5_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1374

theorem cover_p_2_2_6_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 6 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1375
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1376

theorem cover_p_2_2_6_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 6 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1377

theorem cover_p_2_2_6_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 6 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1378

theorem cover_p_2_2_7_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 7 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1379

theorem cover_p_2_3_3_3_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1380
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1381
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1382
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1383
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1384

theorem cover_p_2_3_3_3_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1385
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1386
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1387
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1388

theorem cover_p_2_3_3_3_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1389
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1390
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1391

theorem cover_p_2_3_3_3_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1392
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1393

theorem cover_p_2_3_3_3_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1394

theorem cover_p_2_3_3_4_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1395
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1396
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1397
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1398

theorem cover_p_2_3_3_4_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1399
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1400
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1401

theorem cover_p_2_3_3_4_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1402
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1403

theorem cover_p_2_3_3_4_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 4 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1404

theorem cover_p_2_3_3_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1405
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1406
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard087.canonicalBound_1407

theorem cover_p_2_3_3_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard088.canonicalBound_1408
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard088.canonicalBound_1409

theorem cover_p_2_3_3_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard088.canonicalBound_1410

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard018
