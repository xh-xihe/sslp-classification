-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_1_1_1

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 1 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 1 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049.canonicalBound_0792
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049.canonicalBound_0793
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049.canonicalBound_0794
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049.canonicalBound_0795
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049.canonicalBound_0796
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049.canonicalBound_0797
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049.canonicalBound_0798

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_1_1_1
