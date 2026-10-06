import MainTheory.SignPrefixBetaBound
import MainTheory.Generated.SignBeta8.Proof.G01_0000
import MainTheory.BinaryBetaEightLower

namespace MainTheory.BinaryBetaEight

open MainTheory.BinaryBeta

/-- All sign-matrix completions are checked by the finite Gram-prefix DAG;
the sign/binary bridge and identity padding cover every positive size ≤ 8. -/
theorem betaEightBound : BetaBound 8 42 := by
  have hrows : MainTheory.Generated.SignBeta8.Data.N01_0000.rowsMatrix =
      (fun _ _ => (1 : ℤ)) := by
    ext i j
    fin_cases i
    fin_cases j <;> rfl
  apply MainTheory.SignPrefixBetaBound.betaBound_of_allOnesPrefix
  simpa only [hrows] using MainTheory.Generated.SignBeta8.Proof.N01_0000.certificate

/-- The exact binary inverse-denominator constant, with independently checked
upper bound and an explicit attaining zero-one matrix. -/
theorem betaEightExact : BetaExact 8 42 :=
  ⟨betaEightBound, MainTheory.BinaryBetaEightLower.betaEightAttained⟩

end MainTheory.BinaryBetaEight
