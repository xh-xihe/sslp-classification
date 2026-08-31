-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard078

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_2_2_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard078.canonicalBound_1254
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard078.canonicalBound_1255
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard078.canonicalBound_1256
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard078.canonicalBound_1257
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard078.canonicalBound_1258
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard078.canonicalBound_1259

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_2_2_2
