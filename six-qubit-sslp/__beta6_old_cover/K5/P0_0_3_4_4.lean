-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard017

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_3_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard017.canonicalBound_0275
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard017.canonicalBound_0276
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard017.canonicalBound_0277
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard017.canonicalBound_0278

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_3_4_4
