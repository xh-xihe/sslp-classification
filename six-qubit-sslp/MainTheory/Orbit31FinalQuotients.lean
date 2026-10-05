import MainTheory.Orbit31FinalCross

/-! The final support's printed quotient substitutions follow from the
actual common-product equations, with active denominators explicitly proved. -/
set_option autoImplicit false
namespace MainTheory.Orbit31FinalQuotients
noncomputable section
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31CanonicalPhase
open MainTheory.Orbit31SignedSupport
open MainTheory.Generated.Orbit31DirectTriangles.Type02 (mask)

theorem common_quotients {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) :
    ∃ K : ℂ, K ≠ 0 ∧ ∀ e, c (B 0 e)=K/c (A e) := by
  obtain ⟨K,hK,he⟩ := MainTheory.Orbit31FinalCross.Type02.commonK hp hs hm
  refine ⟨K,hK,?_⟩
  intro e
  have hn : c (A e) ≠ 0 := by
    apply (hm _).mp
    fin_cases e <;> decide +kernel
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using he e

end
end MainTheory.Orbit31FinalQuotients
