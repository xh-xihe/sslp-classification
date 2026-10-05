-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard014

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_2_3_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 3 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard014.canonicalBound_0225
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard014.canonicalBound_0226
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard014.canonicalBound_0227
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard014.canonicalBound_0228
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard014.canonicalBound_0229

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_2_3_3
