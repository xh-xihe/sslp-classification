-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard000

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_0_0_0_0 (a4 a5 : Fin 8)
    (h34 : 0 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 a4.val a5.val)) 9 := by
  fin_cases a4
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_0_0 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_0_1 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_0_2 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_0_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_0_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_0_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_0_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_0_7 a5 h45

theorem cover_p_0_0_0_1 (a4 a5 : Fin 8)
    (h34 : 1 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_1_1 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_1_2 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_1_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_1_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_1_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_1_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_1_7 a5 h45

theorem cover_p_0_0_0_2 (a4 a5 : Fin 8)
    (h34 : 2 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_2_2 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_2_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_2_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_2_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_2_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_2_7 a5 h45

theorem cover_p_0_0_0_3 (a4 a5 : Fin 8)
    (h34 : 3 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_3_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_3_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_3_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_3_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_3_7 a5 h45

theorem cover_p_0_0_0_4 (a4 a5 : Fin 8)
    (h34 : 4 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 4 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_4_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_4_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_4_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_4_7 a5 h45

theorem cover_p_0_0_0_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard000.cover_p_0_0_0_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_0_5_7 a5 h45

theorem cover_p_0_0_0_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_0_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_0_6_7 a5 h45

theorem cover_p_0_0_0_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_0_7_7 a5 h45

theorem cover_p_0_0_1_1 (a4 a5 : Fin 8)
    (h34 : 1 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_1_1 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_1_2 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_1_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_1_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_1_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_1_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_1_7 a5 h45

theorem cover_p_0_0_1_2 (a4 a5 : Fin 8)
    (h34 : 2 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_2_2 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_2_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_2_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_2_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_2_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_2_7 a5 h45

theorem cover_p_0_0_1_3 (a4 a5 : Fin 8)
    (h34 : 3 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_3_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_3_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_3_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_3_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_3_7 a5 h45

theorem cover_p_0_0_1_4 (a4 a5 : Fin 8)
    (h34 : 4 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_4_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_4_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_4_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_4_7 a5 h45

theorem cover_p_0_0_1_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_5_7 a5 h45

theorem cover_p_0_0_1_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_6_7 a5 h45

theorem cover_p_0_0_1_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard001.cover_p_0_0_1_7_7 a5 h45

theorem cover_p_0_0_2_2 (a4 a5 : Fin 8)
    (h34 : 2 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_2_2 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_2_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_2_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_2_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_2_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_2_7 a5 h45

theorem cover_p_0_0_2_3 (a4 a5 : Fin 8)
    (h34 : 3 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_3_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_3_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_3_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_3_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_3_7 a5 h45

theorem cover_p_0_0_2_4 (a4 a5 : Fin 8)
    (h34 : 4 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 4 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_4_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_4_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_4_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_4_7 a5 h45

theorem cover_p_0_0_2_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_5_7 a5 h45

theorem cover_p_0_0_2_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_6_7 a5 h45

theorem cover_p_0_0_2_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_2_7_7 a5 h45

theorem cover_p_0_0_3_3 (a4 a5 : Fin 8)
    (h34 : 3 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_3_3 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_3_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_3_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_3_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_3_7 a5 h45

theorem cover_p_0_0_3_4 (a4 a5 : Fin 8)
    (h34 : 4 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_4_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_4_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_4_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_4_7 a5 h45

theorem cover_p_0_0_3_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard002.cover_p_0_0_3_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_3_5_7 a5 h45

theorem cover_p_0_0_3_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_3_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_3_6_7 a5 h45

theorem cover_p_0_0_3_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_3_7_7 a5 h45

theorem cover_p_0_0_4_4 (a4 a5 : Fin 8)
    (h34 : 4 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 4 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_4_4_4 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_4_4_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_4_4_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_4_4_7 a5 h45

theorem cover_p_0_0_4_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_4_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_4_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_4_5_7 a5 h45

theorem cover_p_0_0_4_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_4_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_4_6_7 a5 h45

theorem cover_p_0_0_4_7 (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 4 7 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_4_7_7 a5 h45

theorem cover_p_0_0_5_5 (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 5 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_5_5_5 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_5_5_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_5_5_7 a5 h45

theorem cover_p_0_0_5_6 (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 5 6 a4.val a5.val)) 9 := by
  fin_cases a4
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · simp at h34
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_5_6_6 a5 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.Shard003.cover_p_0_0_5_6_7 a5 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard000
