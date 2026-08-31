-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_2_2_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 2 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1265
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1266
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1267
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard079.canonicalBound_1268

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_2_2_4
