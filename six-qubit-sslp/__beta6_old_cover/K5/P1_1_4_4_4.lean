-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard060

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_4_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 4 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard060.canonicalBound_0967
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard060.canonicalBound_0968
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard060.canonicalBound_0969
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard060.canonicalBound_0970

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_4_4_4
