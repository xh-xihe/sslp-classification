-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003

-- Each branch below dispatches to exactly one child, so no failed `exact`
-- ever unfolds a determinant circuit.  The budget is raised modestly anyway,
-- because the deepest levels still elaborate large terms once.
set_option maxHeartbeats 4000000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard001

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_5_7 (a2 a3 a4 a5 : Fin 8)
    (h12 : 7 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 7 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_5_7_7 a3 a4 a5 h23 h34 h45

theorem cover_p_6_6 (a2 a3 a4 a5 : Fin 8)
    (h12 : 6 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 6 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_6_6_6 a3 a4 a5 h23 h34 h45
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_6_6_7 a3 a4 a5 h23 h34 h45

theorem cover_p_6_7 (a2 a3 a4 a5 : Fin 8)
    (h12 : 7 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 7 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_6_7_7 a3 a4 a5 h23 h34 h45

theorem cover_p_7_7 (a2 a3 a4 a5 : Fin 8)
    (h12 : 7 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 7 7 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · simp at h12
  · exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003.cover_p_7_7_7 a3 a4 a5 h23 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard001
