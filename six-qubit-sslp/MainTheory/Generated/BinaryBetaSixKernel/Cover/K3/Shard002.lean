-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_2_2_2 (a3 a4 a5 : Fin 8)
    (h23 : 2 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_2_2 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_2_3 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_2_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_2_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_2_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_2_7 a4 a5 h34 h45

theorem cover_p_2_2_3 (a3 a4 a5 : Fin 8)
    (h23 : 3 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 3 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_3_3 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_3_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_3_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_3_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_3_7 a4 a5 h34 h45

theorem cover_p_2_2_4 (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_4_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_4_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_4_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_4_7 a4 a5 h34 h45

theorem cover_p_2_2_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_5_7 a4 a5 h34 h45

theorem cover_p_2_2_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_2_2_6_7 a4 a5 h34 h45

theorem cover_p_2_2_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_2_7_7 a4 a5 h34 h45

theorem cover_p_2_3_3 (a3 a4 a5 : Fin 8)
    (h23 : 3 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_3_3 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_3_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_3_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_3_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_3_7 a4 a5 h34 h45

theorem cover_p_2_3_4 (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_4_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_4_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_4_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_4_7 a4 a5 h34 h45

theorem cover_p_2_3_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_5_7 a4 a5 h34 h45

theorem cover_p_2_3_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_6_7 a4 a5 h34 h45

theorem cover_p_2_3_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_3_7_7 a4 a5 h34 h45

theorem cover_p_2_4_4 (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_4_4_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_4_4_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_4_4_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_4_4_7 a4 a5 h34 h45

theorem cover_p_2_4_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_4_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_4_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_4_5_7 a4 a5 h34 h45

theorem cover_p_2_4_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_4_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_4_6_7 a4 a5 h34 h45

theorem cover_p_2_4_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_4_7_7 a4 a5 h34 h45

theorem cover_p_2_5_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_5_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_5_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_5_5_7 a4 a5 h34 h45

theorem cover_p_2_5_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_5_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_5_6_7 a4 a5 h34 h45

theorem cover_p_2_5_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard007.cover_p_2_5_7_7 a4 a5 h34 h45

theorem cover_p_2_6_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 6 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_2_6_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_2_6_6_7 a4 a5 h34 h45

theorem cover_p_2_6_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 6 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_2_6_7_7 a4 a5 h34 h45

theorem cover_p_2_7_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 7 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_2_7_7_7 a4 a5 h34 h45

theorem cover_p_3_3_3 (a3 a4 a5 : Fin 8)
    (h23 : 3 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_3_3 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_3_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_3_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_3_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_3_7 a4 a5 h34 h45

theorem cover_p_3_3_4 (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_4_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_4_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_4_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_4_7 a4 a5 h34 h45

theorem cover_p_3_3_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_5_7 a4 a5 h34 h45

theorem cover_p_3_3_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_6_7 a4 a5 h34 h45

theorem cover_p_3_3_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_3_7_7 a4 a5 h34 h45

theorem cover_p_3_4_4 (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_4_4_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_4_4_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_4_4_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_4_4_7 a4 a5 h34 h45

theorem cover_p_3_4_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_4_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_4_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_4_5_7 a4 a5 h34 h45

theorem cover_p_3_4_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_4_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_4_6_7 a4 a5 h34 h45

theorem cover_p_3_4_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_4_7_7 a4 a5 h34 h45

theorem cover_p_3_5_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_5_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_5_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard008.cover_p_3_5_5_7 a4 a5 h34 h45

theorem cover_p_3_5_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_3_5_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_3_5_6_7 a4 a5 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002
