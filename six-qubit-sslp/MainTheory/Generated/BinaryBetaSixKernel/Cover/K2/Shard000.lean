-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_0_0 (a2 a3 a4 a5 : Fin 8)
    (h12 : 0 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_0_0 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_0_1 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_0_2 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_0_3 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_0_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_0_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_0_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_0_7 a3 a4 a5 h23 h34 h45

theorem cover_p_0_1 (a2 a3 a4 a5 : Fin 8)
    (h12 : 1 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_1_1 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_1_2 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_1_3 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_1_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_1_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_1_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_1_7 a3 a4 a5 h23 h34 h45

theorem cover_p_0_2 (a2 a3 a4 a5 : Fin 8)
    (h12 : 2 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_2_2 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_2_3 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_2_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_2_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_2_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_2_7 a3 a4 a5 h23 h34 h45

theorem cover_p_0_3 (a2 a3 a4 a5 : Fin 8)
    (h12 : 3 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_3_3 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_3_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_3_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_3_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_3_7 a3 a4 a5 h23 h34 h45

theorem cover_p_0_4 (a2 a3 a4 a5 : Fin 8)
    (h12 : 4 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 4 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_4_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_4_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_4_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_4_7 a3 a4 a5 h23 h34 h45

theorem cover_p_0_5 (a2 a3 a4 a5 : Fin 8)
    (h12 : 5 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 5 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_5_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard000.cover_p_0_5_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_0_5_7 a3 a4 a5 h23 h34 h45

theorem cover_p_0_6 (a2 a3 a4 a5 : Fin 8)
    (h12 : 6 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 6 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_0_6_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_0_6_7 a3 a4 a5 h23 h34 h45

theorem cover_p_0_7 (a2 a3 a4 a5 : Fin 8)
    (h12 : 7 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 7 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_0_7_7 a3 a4 a5 h23 h34 h45

theorem cover_p_1_1 (a2 a3 a4 a5 : Fin 8)
    (h12 : 1 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_1_1 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_1_2 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_1_3 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_1_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_1_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_1_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_1_7 a3 a4 a5 h23 h34 h45

theorem cover_p_1_2 (a2 a3 a4 a5 : Fin 8)
    (h12 : 2 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_2_2 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_2_3 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_2_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_2_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_2_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_2_7 a3 a4 a5 h23 h34 h45

theorem cover_p_1_3 (a2 a3 a4 a5 : Fin 8)
    (h12 : 3 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_3_3 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_3_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_3_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_3_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_3_7 a3 a4 a5 h23 h34 h45

theorem cover_p_1_4 (a2 a3 a4 a5 : Fin 8)
    (h12 : 4 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_4_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_4_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_4_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_4_7 a3 a4 a5 h23 h34 h45

theorem cover_p_1_5 (a2 a3 a4 a5 : Fin 8)
    (h12 : 5 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 5 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_5_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_5_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_5_7 a3 a4 a5 h23 h34 h45

theorem cover_p_1_6 (a2 a3 a4 a5 : Fin 8)
    (h12 : 6 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 6 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_6_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_6_7 a3 a4 a5 h23 h34 h45

theorem cover_p_1_7 (a2 a3 a4 a5 : Fin 8)
    (h12 : 7 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 7 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard001.cover_p_1_7_7 a3 a4 a5 h23 h34 h45

theorem cover_p_2_2 (a2 a3 a4 a5 : Fin 8)
    (h12 : 2 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_2_2 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_2_3 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_2_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_2_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_2_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_2_7 a3 a4 a5 h23 h34 h45

theorem cover_p_2_3 (a2 a3 a4 a5 : Fin 8)
    (h12 : 3 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_3_3 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_3_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_3_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_3_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_3_7 a3 a4 a5 h23 h34 h45

theorem cover_p_2_4 (a2 a3 a4 a5 : Fin 8)
    (h12 : 4 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 4 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_4_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_4_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_4_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_4_7 a3 a4 a5 h23 h34 h45

theorem cover_p_2_5 (a2 a3 a4 a5 : Fin 8)
    (h12 : 5 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_5_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_5_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_5_7 a3 a4 a5 h23 h34 h45

theorem cover_p_2_6 (a2 a3 a4 a5 : Fin 8)
    (h12 : 6 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 6 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_6_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_6_7 a3 a4 a5 h23 h34 h45

theorem cover_p_2_7 (a2 a3 a4 a5 : Fin 8)
    (h12 : 7 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 7 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_2_7_7 a3 a4 a5 h23 h34 h45

theorem cover_p_3_3 (a2 a3 a4 a5 : Fin 8)
    (h12 : 3 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_3_3 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_3_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_3_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_3_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_3_7 a3 a4 a5 h23 h34 h45

theorem cover_p_3_4 (a2 a3 a4 a5 : Fin 8)
    (h12 : 4 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_4_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_4_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_4_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_4_7 a3 a4 a5 h23 h34 h45

theorem cover_p_3_5 (a2 a3 a4 a5 : Fin 8)
    (h12 : 5 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_5_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard002.cover_p_3_5_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_3_5_7 a3 a4 a5 h23 h34 h45

theorem cover_p_3_6 (a2 a3 a4 a5 : Fin 8)
    (h12 : 6 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 6 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_3_6_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_3_6_7 a3 a4 a5 h23 h34 h45

theorem cover_p_3_7 (a2 a3 a4 a5 : Fin 8)
    (h12 : 7 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 7 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_3_7_7 a3 a4 a5 h23 h34 h45

theorem cover_p_4_4 (a2 a3 a4 a5 : Fin 8)
    (h12 : 4 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_4_4_4 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_4_4_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_4_4_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_4_4_7 a3 a4 a5 h23 h34 h45

theorem cover_p_4_5 (a2 a3 a4 a5 : Fin 8)
    (h12 : 5 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_4_5_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_4_5_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_4_5_7 a3 a4 a5 h23 h34 h45

theorem cover_p_4_6 (a2 a3 a4 a5 : Fin 8)
    (h12 : 6 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 6 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_4_6_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_4_6_7 a3 a4 a5 h23 h34 h45

theorem cover_p_4_7 (a2 a3 a4 a5 : Fin 8)
    (h12 : 7 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 7 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_4_7_7 a3 a4 a5 h23 h34 h45

theorem cover_p_5_5 (a2 a3 a4 a5 : Fin 8)
    (h12 : 5 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_5_5_5 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_5_5_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_5_5_7 a3 a4 a5 h23 h34 h45

theorem cover_p_5_6 (a2 a3 a4 a5 : Fin 8)
    (h12 : 6 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 6 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_5_6_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_5_6_7 a3 a4 a5 h23 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000
