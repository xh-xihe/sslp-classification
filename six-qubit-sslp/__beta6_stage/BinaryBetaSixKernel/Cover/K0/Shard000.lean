-- Generated proof-only `Fin 8` coverage shard.
-- At most 32 independent theorems; heartbeat limits reset per command.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K0.Shard000

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover_root (a0 a1 a2 a3 a4 a5 : Fin 8)
    (h01 : a0.val <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 a0.val a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a0 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000.cover_p_0 a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000.cover_p_1 a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000.cover_p_2 a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000.cover_p_3 a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000.cover_p_4 a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000.cover_p_5 a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000.cover_p_6 a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.Shard000.cover_p_7 a1 a2 a3 a4 a5 h01 h12 h23 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K0.Shard000
