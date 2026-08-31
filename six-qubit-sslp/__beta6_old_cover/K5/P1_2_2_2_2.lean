-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard062

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_2_2_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 2 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard062.canonicalBound_1002
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard062.canonicalBound_1003
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard062.canonicalBound_1004
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard062.canonicalBound_1005
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard062.canonicalBound_1006
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard062.canonicalBound_1007

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_2_2_2
