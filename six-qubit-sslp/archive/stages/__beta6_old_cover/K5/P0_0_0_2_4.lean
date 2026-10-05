-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_2_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0075
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0076
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0077
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0078

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_2_4
