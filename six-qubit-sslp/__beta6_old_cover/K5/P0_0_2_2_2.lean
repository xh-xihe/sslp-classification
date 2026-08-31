-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard013

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_2_2_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 2 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0204
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0205
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0206
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard012.canonicalBound_0207
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard013.canonicalBound_0208
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard013.canonicalBound_0209

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_2_2_2
