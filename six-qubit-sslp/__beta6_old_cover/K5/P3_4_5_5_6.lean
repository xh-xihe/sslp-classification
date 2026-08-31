-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard099
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard100

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_4_5_5_6

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 5 5 6 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard099.canonicalBound_1599
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard100.canonicalBound_1600

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_4_5_5_6
