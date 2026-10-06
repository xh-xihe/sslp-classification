import MainTheory.BinaryBetaNine
import MainTheory.BetaExactValue

/-!
# `beta_9 = 120`

`eq:small-beta` tabulates `beta_5 = 5`, `beta_6 = 9`, `beta_7 = 18`,
`beta_8 = 42` and `beta_9 = 120`.  The size-nine entry was the last one whose
universal upper bound was outstanding: the sign-prefix DAG for size nine was
generated and every one of its modules compiled, but the capstone that reads
the DAG certificate as `BetaBound 9 120` had never itself been compiled, so
the entry could not be claimed.

`MainTheory.BinaryBetaNine.betaNineExact` closes it, and this file converts
that exact certificate into the value of the finite-supremum definition, the
same way `BetaEightValue` does at size eight.
-/

namespace MainTheory.BetaNineValue

theorem betaOf_nine : MainTheory.BetaExists.betaOf 9 = 120 :=
  MainTheory.BetaExactValue.betaOf_eq_of_exact
    MainTheory.BinaryBetaNine.betaNineExact

end MainTheory.BetaNineValue
