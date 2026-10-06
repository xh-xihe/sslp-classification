-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard042

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_3_3_3_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041.canonicalBound_0671
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard042.canonicalBound_0672
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard042.canonicalBound_0673
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard042.canonicalBound_0674

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_3_3_3_4
