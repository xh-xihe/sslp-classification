-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_0_5_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_0_5_7_7 a4 a5 h34 h45

theorem cover_p_0_6_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 6 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_0_6_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_0_6_6_7 a4 a5 h34 h45

theorem cover_p_0_6_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 6 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_0_6_7_7 a4 a5 h34 h45

theorem cover_p_0_7_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 7 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_0_7_7_7 a4 a5 h34 h45

theorem cover_p_1_1_1 (a3 a4 a5 : Fin 8)
    (h23 : 1 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_1_1_1_1 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_1_1_1_2 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_1_1_1_3 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_1_1_1_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_1_1_1_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_1_1_1_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_1_1_1_7 a4 a5 h34 h45

theorem cover_p_1_1_2 (a3 a4 a5 : Fin 8)
    (h23 : 2 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard003.cover_p_1_1_2_2 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_2_3 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_2_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_2_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_2_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_2_7 a4 a5 h34 h45

theorem cover_p_1_1_3 (a3 a4 a5 : Fin 8)
    (h23 : 3 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_3_3 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_3_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_3_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_3_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_3_7 a4 a5 h34 h45

theorem cover_p_1_1_4 (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_4_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_4_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_4_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_4_7 a4 a5 h34 h45

theorem cover_p_1_1_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_5_7 a4 a5 h34 h45

theorem cover_p_1_1_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_6_7 a4 a5 h34 h45

theorem cover_p_1_1_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_1_7_7 a4 a5 h34 h45

theorem cover_p_1_2_2 (a3 a4 a5 : Fin 8)
    (h23 : 2 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_2_2 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_2_3 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_2_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_2_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_2_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_2_7 a4 a5 h34 h45

theorem cover_p_1_2_3 (a3 a4 a5 : Fin 8)
    (h23 : 3 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_3_3 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_3_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_3_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_3_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_3_7 a4 a5 h34 h45

theorem cover_p_1_2_4 (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard004.cover_p_1_2_4_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_2_4_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_2_4_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_2_4_7 a4 a5 h34 h45

theorem cover_p_1_2_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_2_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_2_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_2_5_7 a4 a5 h34 h45

theorem cover_p_1_2_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_2_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_2_6_7 a4 a5 h34 h45

theorem cover_p_1_2_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_2_7_7 a4 a5 h34 h45

theorem cover_p_1_3_3 (a3 a4 a5 : Fin 8)
    (h23 : 3 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_3_3 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_3_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_3_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_3_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_3_7 a4 a5 h34 h45

theorem cover_p_1_3_4 (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_4_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_4_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_4_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_4_7 a4 a5 h34 h45

theorem cover_p_1_3_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_5_7 a4 a5 h34 h45

theorem cover_p_1_3_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_6_7 a4 a5 h34 h45

theorem cover_p_1_3_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_3_7_7 a4 a5 h34 h45

theorem cover_p_1_4_4 (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_4_4_4 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_4_4_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_4_4_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_4_4_7 a4 a5 h34 h45

theorem cover_p_1_4_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_4_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_4_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_4_5_7 a4 a5 h34 h45

theorem cover_p_1_4_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005.cover_p_1_4_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_4_6_7 a4 a5 h34 h45

theorem cover_p_1_4_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_4_7_7 a4 a5 h34 h45

theorem cover_p_1_5_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_5_5_5 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_5_5_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_5_5_7 a4 a5 h34 h45

theorem cover_p_1_5_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_5_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_5_6_7 a4 a5 h34 h45

theorem cover_p_1_5_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_5_7_7 a4 a5 h34 h45

theorem cover_p_1_6_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 6 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_6_6_6 a4 a5 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_6_6_7 a4 a5 h34 h45

theorem cover_p_1_6_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 6 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_6_7_7 a4 a5 h34 h45

theorem cover_p_1_7_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 7 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · simp at h23
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard006.cover_p_1_7_7_7 a4 a5 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001
