import MainTheory.OrderNineMomentUniqueness
import MainTheory.OrderNineCovariance
import MainTheory.ProbabilityPhaseParametrization

namespace MainTheory.OrderNineProbabilityPolytope

open MainTheory.OrderNineMomentStatistics MainTheory.OrderNineMomentUniqueness
open MainTheory.FiniteMomentMatrix MainTheory.CodeAffineSpanBridge

noncomputable def probabilityR : Sum (Fin 7) (Fin 7) → ℝ := fun z => probability z

def feasibleSet : Set (Sum (Fin 7) (Fin 7) → ℝ) :=
  {p | MainTheory.ExactLP.RealFeasible
    (MainTheory.MomentMatrix23.matrixQ leftWords rightWords) rhsQ p}

theorem probability_feasible : probabilityR ∈ feasibleSet := by
  obtain ⟨p, hp⟩ := (MainTheory.ExactLP.rational_feasible_iff_real
    (MainTheory.MomentMatrix23.matrixQ leftWords rightWords) rhsQ).mp
      ⟨probability, moment_feasible⟩
  rw [real_probability_unique p hp] at hp
  exact hp

theorem feasibleSet_singleton : feasibleSet = {probabilityR} := by
  ext p
  constructor
  · intro hp
    exact Set.mem_singleton_iff.mpr (real_probability_unique p hp)
  · rintro rfl
    exact probability_feasible

theorem affine_dimension_zero :
    Module.finrank ℝ (affineSpan ℝ feasibleSet).direction = 0 := by
  rw [feasibleSet_singleton]
  simp [direction_affineSpan]

theorem positive_coordinates (p : Sum (Fin 7) (Fin 7) → ℝ) (hp : p ∈ feasibleSet) :
    ∀ z, 0 < p z := by
  rw [real_probability_unique p hp]
  intro z
  cases z with
  | inl i =>
    change 0 < (weights i : ℝ)
    exact_mod_cast weights_positive i
  | inr i =>
    change 0 < (weights i : ℝ)
    exact_mod_cast weights_positive i

theorem real_mean : (fun j => ∑ i, (weights i : ℝ) * bitPoint (vertices i) j) =
    fun _ => 1/2 := by
  funext j
  have h := congrArg (fun f : Fin 6 → ℚ => (f j : ℝ)) mean_exact
  change ((∑ i, weights i * pointQ i j : ℚ) : ℝ) = _ at h
  push_cast at h
  have hpoint (i : Fin 7) : (pointQ i j : ℝ) = bitPoint (vertices i) j := by
    cases hv : vertices i j <;> simp [pointQ, bitPoint, hv]
  simpa only [hpoint] using h

theorem complementary_mean :
    (fun j => ∑ i, (weights i : ℝ) * bitPoint (SS.complement (vertices i)) j) =
      fun _ => 1/2 := by
  funext j
  have hc (i : Fin 7) : bitPoint (SS.complement (vertices i)) j =
      1 - bitPoint (vertices i) j := by
    cases hv : vertices i j <;> simp [bitPoint, SS.complement, hv]
  simp_rw [hc, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, congrFun real_mean j]
  have hw : ∑ i, (weights i : ℝ) = 1 := by exact_mod_cast weights_normalized
  rw [hw]
  norm_num

theorem phase_parametrization (amplitude : Sum (Fin 7) (Fin 7) → ℂ)
    (hp : (fun z => Complex.normSq (amplitude z)) ∈ feasibleSet) :
    ∃ alpha : Sum (Fin 7) (Fin 7) → ℝ,
      ∀ z, amplitude z = (Real.sqrt (probabilityR z) : ℂ) *
        Complex.exp (Complex.I * (alpha z : ℂ)) := by
  have h := real_probability_unique _ hp
  choose alpha ha using fun z => MainTheory.ProbabilityPhaseParametrization.exists_phase
    (amplitude z) (probabilityR z) (congrFun h z)
  exact ⟨alpha, ha⟩

end MainTheory.OrderNineProbabilityPolytope
