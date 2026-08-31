-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_0_0_3_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0290

theorem cover_p_0_0_3_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0291
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0292

theorem cover_p_0_0_3_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0293

theorem cover_p_0_0_3_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0294

theorem cover_p_0_0_4_4_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0295
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0296
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0297
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0298

theorem cover_p_0_0_4_4_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0299
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0300
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0301

theorem cover_p_0_0_4_4_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0302
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard018.canonicalBound_0303

theorem cover_p_0_0_4_4_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0304

theorem cover_p_0_0_4_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0305
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0306
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0307

theorem cover_p_0_0_4_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0308
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0309

theorem cover_p_0_0_4_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0310

theorem cover_p_0_0_4_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0311
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0312

theorem cover_p_0_0_4_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0313

theorem cover_p_0_0_4_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0314

theorem cover_p_0_0_5_5_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 5 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0315
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0316
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0317

theorem cover_p_0_0_5_5_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 5 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0318
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard019.canonicalBound_0319

theorem cover_p_0_0_5_5_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 5 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0320

theorem cover_p_0_0_5_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0321
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0322

theorem cover_p_0_0_5_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0323

theorem cover_p_0_0_5_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0324

theorem cover_p_0_0_6_6_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 6 6 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0325
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0326

theorem cover_p_0_0_6_6_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 6 6 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0327

theorem cover_p_0_0_6_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 6 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0328

theorem cover_p_0_0_7_7_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 7 7 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0329

theorem cover_p_0_1_1_1_1 (a5 : Fin 8)
    (h45 : 1 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 1 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0330
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0331
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0332
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0333
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0334
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0335
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0336

theorem cover_p_0_1_1_1_2 (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 2 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0337
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0338
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0339
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0340
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0341
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0342

theorem cover_p_0_1_1_1_3 (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 3 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0343
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0344
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0345
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0346
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0347

theorem cover_p_0_1_1_1_4 (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 4 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0348
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0349
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0350
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0351

theorem cover_p_0_1_1_1_5 (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 5 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0352
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0353
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0354

theorem cover_p_0_1_1_1_6 (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 6 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0355
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0356

theorem cover_p_0_1_1_1_7 (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 7 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0357

theorem cover_p_0_1_1_2_2 (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 2 a5.val)) 9 := by
  fin_cases a5
  · simp at h45
  · simp at h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0358
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0359
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0360
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0361
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0362
  · exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0363

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003
