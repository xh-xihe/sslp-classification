-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard060

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_3_7_7

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 3 7 7 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard060.canonicalBound_0966

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_3_7_7
