-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_1_2_4_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_4_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_4_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_4_5_7 a5 h45

theorem cover_p_1_2_4_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_4_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_4_6_7 a5 h45

theorem cover_p_1_2_4_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 4 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_4_7_7 a5 h45

theorem cover_p_1_2_5_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_5_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_5_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_5_5_7 a5 h45

theorem cover_p_1_2_5_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_5_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_5_6_7 a5 h45

theorem cover_p_1_2_5_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_5_7_7 a5 h45

theorem cover_p_1_2_6_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 6 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_6_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_6_6_7 a5 h45

theorem cover_p_1_2_6_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 6 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_6_7_7 a5 h45

theorem cover_p_1_2_7_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 7 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_2_7_7_7 a5 h45

theorem cover_p_1_3_3_3 (a4 a5 : Fin 8)
    (h34 : 3 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_3_3_3_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_3_3_3_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_3_3_3_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_3_3_3_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_3_3_3_7 a5 h45

theorem cover_p_1_3_3_4 (a4 a5 : Fin 8)
    (h34 : 4 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 4 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_3_3_4_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_3_3_4_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_3_3_4_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_3_3_4_7 a5 h45

theorem cover_p_1_3_3_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard014.cover_p_1_3_3_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_3_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_3_5_7 a5 h45

theorem cover_p_1_3_3_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_3_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_3_6_7 a5 h45

theorem cover_p_1_3_3_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_3_7_7 a5 h45

theorem cover_p_1_3_4_4 (a4 a5 : Fin 8)
    (h34 : 4 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_4_4_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_4_4_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_4_4_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_4_4_7 a5 h45

theorem cover_p_1_3_4_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_4_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_4_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_4_5_7 a5 h45

theorem cover_p_1_3_4_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_4_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_4_6_7 a5 h45

theorem cover_p_1_3_4_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_4_7_7 a5 h45

theorem cover_p_1_3_5_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_5_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_5_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_5_5_7 a5 h45

theorem cover_p_1_3_5_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_5_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_5_6_7 a5 h45

theorem cover_p_1_3_5_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_5_7_7 a5 h45

theorem cover_p_1_3_6_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 6 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_6_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_6_6_7 a5 h45

theorem cover_p_1_3_6_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 6 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_6_7_7 a5 h45

theorem cover_p_1_3_7_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 7 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_3_7_7_7 a5 h45

theorem cover_p_1_4_4_4 (a4 a5 : Fin 8)
    (h34 : 4 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 4 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_4_4_4_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_4_4_4_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_4_4_4_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_4_4_4_7 a5 h45

theorem cover_p_1_4_4_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_4_4_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_4_4_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard015.cover_p_1_4_4_5_7 a5 h45

theorem cover_p_1_4_4_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_4_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_4_6_7 a5 h45

theorem cover_p_1_4_4_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 4 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_4_7_7 a5 h45

theorem cover_p_1_4_5_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_5_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_5_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_5_5_7 a5 h45

theorem cover_p_1_4_5_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_5_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_5_6_7 a5 h45

theorem cover_p_1_4_5_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 5 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_5_7_7 a5 h45

theorem cover_p_1_4_6_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 6 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_6_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard016.cover_p_1_4_6_6_7 a5 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard005
