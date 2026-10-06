import MainTheory.SignPrefixBetaBound
import MainTheory.Generated.SignBeta7.Proof.G01_0000
import MainTheory.BinaryBetaSevenLower

namespace MainTheory.BinaryBetaSeven

open MainTheory.BinaryBeta

/-- All sign-matrix completions are checked by the finite Gram-prefix DAG;
the sign/binary bridge and identity padding cover every positive size ≤ 7. -/
theorem betaSevenBound : BetaBound 7 18 := by
  have hrows : MainTheory.Generated.SignBeta7.Data.N01_0000.rowsMatrix =
      (fun _ _ => (1 : ℤ)) := by
    ext i j
    fin_cases i
    fin_cases j <;> rfl
  apply MainTheory.SignPrefixBetaBound.betaBound_of_allOnesPrefix
  simpa only [hrows] using MainTheory.Generated.SignBeta7.Proof.N01_0000.certificate

/-- The exact binary inverse-denominator constant, with independently checked
upper bound and an explicit attaining zero-one matrix. -/
theorem betaSevenExact : BetaExact 7 18 :=
  ⟨betaSevenBound, MainTheory.BinaryBetaSevenLower.betaSevenAttained⟩

end MainTheory.BinaryBetaSeven
