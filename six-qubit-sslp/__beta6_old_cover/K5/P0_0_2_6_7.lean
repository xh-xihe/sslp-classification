-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard016

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_2_6_7

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 2 6 7 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard016.canonicalBound_0258

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_2_6_7
