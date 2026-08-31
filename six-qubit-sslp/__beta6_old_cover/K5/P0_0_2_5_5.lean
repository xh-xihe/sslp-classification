-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard015

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_2_5_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 5 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard015.canonicalBound_0250
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard015.canonicalBound_0251
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard015.canonicalBound_0252

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_2_5_5
