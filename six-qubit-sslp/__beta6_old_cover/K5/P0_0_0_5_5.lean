-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_5_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 5 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0110
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard006.canonicalBound_0111
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0112

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_5_5
