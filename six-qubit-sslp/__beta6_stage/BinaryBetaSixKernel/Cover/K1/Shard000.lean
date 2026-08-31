-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard001

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_0 (a1 a2 a3 a4 a5 : Fin 8)
    (h01 : 0 <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a1 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_0_0 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_0_1 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_0_2 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_0_3 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_0_4 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_0_5 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_0_6 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_0_7 a2 a3 a4 a5 h12 h23 h34 h45

theorem cover_p_1 (a1 a2 a3 a4 a5 : Fin 8)
    (h01 : 1 <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a1 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_1_1 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_1_2 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_1_3 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_1_4 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_1_5 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_1_6 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_1_7 a2 a3 a4 a5 h12 h23 h34 h45

theorem cover_p_2 (a1 a2 a3 a4 a5 : Fin 8)
    (h01 : 2 <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a1 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_2_2 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_2_3 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_2_4 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_2_5 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_2_6 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_2_7 a2 a3 a4 a5 h12 h23 h34 h45

theorem cover_p_3 (a1 a2 a3 a4 a5 : Fin 8)
    (h01 : 3 <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a1 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_3_3 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_3_4 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_3_5 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_3_6 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_3_7 a2 a3 a4 a5 h12 h23 h34 h45

theorem cover_p_4 (a1 a2 a3 a4 a5 : Fin 8)
    (h01 : 4 <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a1 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_4_4 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_4_5 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_4_6 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_4_7 a2 a3 a4 a5 h12 h23 h34 h45

theorem cover_p_5 (a1 a2 a3 a4 a5 : Fin 8)
    (h01 : 5 <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a1 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_5_5 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard000.cover_p_5_6 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard001.cover_p_5_7 a2 a3 a4 a5 h12 h23 h34 h45

theorem cover_p_6 (a1 a2 a3 a4 a5 : Fin 8)
    (h01 : 6 <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a1 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard001.cover_p_6_6 a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard001.cover_p_6_7 a2 a3 a4 a5 h12 h23 h34 h45

theorem cover_p_7 (a1 a2 a3 a4 a5 : Fin 8)
    (h01 : 7 <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 7 a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a1 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.Shard001.cover_p_7_7 a2 a3 a4 a5 h12 h23 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000
