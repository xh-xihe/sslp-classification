-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard057

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_2_4_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 4 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard057.canonicalBound_0916
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard057.canonicalBound_0917
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard057.canonicalBound_0918

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_2_4_5
