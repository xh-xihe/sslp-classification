-- Generated semantic endpoint for size 4.
import MainTheory.Generated.BinaryBetaSmall.Size4.Node.K0.Root
import MainTheory.BinaryBetaSmallLower

namespace MainTheory.Generated.BinaryBetaSmall.Size4.Certificate

open MainTheory.BinaryBeta
open MainTheory.BinaryBetaSmallSemantic

theorem monotonePrefix : MonotonePrefixCertificate 3 3 := by
  intro f hf
  have hvec : f = ![f 0, f 1, f 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
  have h01 := hf (show (0 : Fin 3) ≤ 1 by decide)
  have h12 := hf (show (1 : Fin 3) ≤ 2 by decide)
  exact MainTheory.Generated.BinaryBetaSmall.Size4.Node.K0.Root.cover (f 0) (f 1) (f 2) h01 h12

theorem upper : BetaBound 4 3 := by
  simpa using betaBound_of_monotonePrefixCertificate monotonePrefix

theorem betaExact : BetaExact 4 3 :=
  ⟨upper, MainTheory.BinaryBetaSmallLower.Four.betaFourAttained⟩

end MainTheory.Generated.BinaryBetaSmall.Size4.Certificate
