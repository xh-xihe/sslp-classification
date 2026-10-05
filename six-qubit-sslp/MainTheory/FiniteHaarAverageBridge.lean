import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! A finite unitary average with invariant image equals the normalized Haar average. -/

namespace MainTheory.FiniteHaarAverageBridge
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators
variable {G K E : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable [Fintype K] [Nonempty K]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def average (ρ : G → E →L[ℝ] E) (s : K → G) (x : E) : E :=
  (Fintype.card K : ℝ)⁻¹ • ∑ k, ρ (s k) x

theorem equals_haar (μ : Measure G) [IsProbabilityMeasure μ] [IsMulRightInvariant μ]
    (ρ : G → E →L[ℝ] E) (s : K → G)
    (hmul : ∀ g h x, ρ g (ρ h x)=ρ (g*h) x) (x : E)
    (hx : Integrable (fun g => ρ g x) μ)
    (hfixed : ∀ g, ρ g (average ρ s x)=average ρ s x) :
    average ρ s x=∫ g, ρ g x ∂μ := by
  have hc : (Fintype.card K : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    average ρ s x=∫ g, ρ g (average ρ s x) ∂μ := by simp only [hfixed]; simp
    _=∫ g, (Fintype.card K : ℝ)⁻¹ • ∑ k, ρ (g*s k) x ∂μ := by
      congr 1
      funext g
      simp only [average,map_smul,_root_.map_sum,hmul]
    _=(Fintype.card K : ℝ)⁻¹ • ∑ k, ∫ g, ρ (g*s k) x ∂μ := by
      rw [integral_smul,integral_finset_sum]
      intro k _
      exact hx.comp_mul_right (s k)
    _=(Fintype.card K : ℝ)⁻¹ • ∑ _ : K, ∫ g, ρ g x ∂μ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      exact integral_mul_right_eq_self (fun g => ρ g x) (s k)
    _=∫ g, ρ g x ∂μ := by
      rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ,
        smul_smul,inv_mul_cancel₀ hc,one_smul]

end
end MainTheory.FiniteHaarAverageBridge
