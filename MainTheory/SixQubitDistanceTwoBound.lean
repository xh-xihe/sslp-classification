import MainTheory.BinaryBetaSeven
import MainTheory.QuantitativeGroup

namespace MainTheory.SixQubitDistanceTwoBound

open MainTheory.QuantitativeGroup
open MainTheory.GlobalClassificationBridge MainTheory.GeneralLiftOrder

/-- The paper's numerical bound for every actual six-qubit rank-two code
detecting single-qubit errors, and every nontrivial intrinsic diagonal action. -/
theorem qMin_le_eighteen {d : ℕ} (C : MainTheory.CodeSpec.ExactCode 6 2 d)
    (hd : 2 ≤ d) (g : IntrinsicGroup C) (hg : g ≠ 1) : qMin C hd g ≤ 18 :=
  (k2_q_bound MainTheory.BinaryBetaSeven.betaSevenBound C hd g hg).2

end MainTheory.SixQubitDistanceTwoBound
