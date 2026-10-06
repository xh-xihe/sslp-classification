-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard059

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_3_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard059.canonicalBound_0947
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard059.canonicalBound_0948
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard059.canonicalBound_0949
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard059.canonicalBound_0950

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_3_4_4
