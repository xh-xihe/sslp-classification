-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_5_6_6

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 5 6 6 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041.canonicalBound_0657
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041.canonicalBound_0658

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_5_6_6
