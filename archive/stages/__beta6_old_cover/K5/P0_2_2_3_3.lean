-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_2_3_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 3 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0561
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0562
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0563
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0564
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard035.canonicalBound_0565

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_2_3_3
