-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard028

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_2_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard028.canonicalBound_0450
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard028.canonicalBound_0451
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard028.canonicalBound_0452
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard028.canonicalBound_0453

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_2_4_4
