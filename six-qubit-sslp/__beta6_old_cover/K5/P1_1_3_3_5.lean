-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard058

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_3_3_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 3 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard058.canonicalBound_0941
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard058.canonicalBound_0942
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard058.canonicalBound_0943

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_3_3_5
