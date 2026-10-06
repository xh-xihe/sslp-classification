import MainTheory.SignPrefixBetaBound
import MainTheory.Generated.SignBeta9.Proof.G01_0000
import MainTheory.BinaryBetaNineLower

namespace MainTheory.BinaryBetaNine

open MainTheory.BinaryBeta

/-- All sign-matrix completions are checked by the finite Gram-prefix DAG;
the sign/binary bridge and identity padding cover every positive size ≤ 9. -/
theorem betaNineBound : BetaBound 9 120 := by
  have hrows : MainTheory.Generated.SignBeta9.Data.N01_0000.rowsMatrix =
      (fun _ _ => (1 : ℤ)) := by
    ext i j
    fin_cases i
    fin_cases j <;> rfl
  apply MainTheory.SignPrefixBetaBound.betaBound_of_allOnesPrefix
  simpa only [hrows] using MainTheory.Generated.SignBeta9.Proof.N01_0000.certificate

/-- The exact binary inverse-denominator constant, with independently checked
upper bound and an explicit attaining zero-one matrix. -/
theorem betaNineExact : BetaExact 9 120 :=
  ⟨betaNineBound, MainTheory.BinaryBetaNineLower.betaNineAttained⟩

end MainTheory.BinaryBetaNine
