-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_3_3_3_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 3 3 3 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041.canonicalBound_0666
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041.canonicalBound_0667
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041.canonicalBound_0668
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041.canonicalBound_0669
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard041.canonicalBound_0670

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_3_3_3_3
