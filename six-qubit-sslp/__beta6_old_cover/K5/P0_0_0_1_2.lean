-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_1_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 1 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0043
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0044
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0045
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0046
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard002.canonicalBound_0047
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard003.canonicalBound_0048

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_1_2
