-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_6_6_6

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 6 6 6 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041.canonicalBound_0661
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041.canonicalBound_0662

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_6_6_6
