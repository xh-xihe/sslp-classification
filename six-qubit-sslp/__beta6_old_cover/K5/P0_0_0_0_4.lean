-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_0_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0026
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0027
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0028
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0029

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_0_4
