-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_p_3_5_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 5 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_3_5_7_7 a4 a5 h34 h45

theorem cover_p_3_6_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 6 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_3_6_6_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_3_6_6_7 a4 a5 h34 h45

theorem cover_p_3_6_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 6 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_3_6_7_7 a4 a5 h34 h45

theorem cover_p_3_7_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 7 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_3_7_7_7 a4 a5 h34 h45

theorem cover_p_4_4_4 (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_4_4_4 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_4_4_5 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_4_4_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_4_4_7 a4 a5 h34 h45

theorem cover_p_4_4_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_4_5_5 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_4_5_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_4_5_7 a4 a5 h34 h45

theorem cover_p_4_4_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_4_6_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_4_6_7 a4 a5 h34 h45

theorem cover_p_4_4_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 4 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_4_7_7 a4 a5 h34 h45

theorem cover_p_4_5_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_5_5_5 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_5_5_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_5_5_7 a4 a5 h34 h45

theorem cover_p_4_5_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_5_6_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_5_6_7 a4 a5 h34 h45

theorem cover_p_4_5_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 5 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_5_7_7 a4 a5 h34 h45

theorem cover_p_4_6_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 6 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_6_6_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_6_6_7 a4 a5 h34 h45

theorem cover_p_4_6_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 6 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_6_7_7 a4 a5 h34 h45

theorem cover_p_4_7_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 4 7 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_4_7_7_7 a4 a5 h34 h45

theorem cover_p_5_5_5 (a3 a4 a5 : Fin 8)
    (h23 : 5 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 5 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_5_5_5_5 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_5_5_5_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_5_5_5_7 a4 a5 h34 h45

theorem cover_p_5_5_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_5_5_6_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard009.cover_p_5_5_6_7 a4 a5 h34 h45

theorem cover_p_5_5_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 5 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010.cover_p_5_5_7_7 a4 a5 h34 h45

theorem cover_p_5_6_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 6 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010.cover_p_5_6_6_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010.cover_p_5_6_6_7 a4 a5 h34 h45

theorem cover_p_5_6_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 6 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010.cover_p_5_6_7_7 a4 a5 h34 h45

theorem cover_p_5_7_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 5 7 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010.cover_p_5_7_7_7 a4 a5 h34 h45

theorem cover_p_6_6_6 (a3 a4 a5 : Fin 8)
    (h23 : 6 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 6 6 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010.cover_p_6_6_6_6 a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010.cover_p_6_6_6_7 a4 a5 h34 h45

theorem cover_p_6_6_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 6 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010.cover_p_6_6_7_7 a4 a5 h34 h45

theorem cover_p_6_7_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 6 7 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010.cover_p_6_7_7_7 a4 a5 h34 h45

theorem cover_p_7_7_7 (a3 a4 a5 : Fin 8)
    (h23 : 7 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 7 7 7 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.Shard010.cover_p_7_7_7_7 a4 a5 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.Shard003
