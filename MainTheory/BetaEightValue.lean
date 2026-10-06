import MainTheory.BinaryBetaEight
import MainTheory.BetaExactValue

namespace MainTheory.BetaEightValue

theorem betaOf_eight : MainTheory.BetaExists.betaOf 8 = 42 :=
  MainTheory.BetaExactValue.betaOf_eq_of_exact
    MainTheory.BinaryBetaEight.betaEightExact

end MainTheory.BetaEightValue
