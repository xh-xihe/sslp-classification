import MainTheory.Orbit36PhaseMapMatrix
import MainTheory.ProbabilityPhaseParametrization

set_option autoImplicit false

namespace MainTheory.Orbit36PhaseMap

open MainTheory.Orbit36PhaseMapMatrix

noncomputable def realMatrix : Matrix (Fin 7) (Fin 7) ℝ := phaseMatrix.map (algebraMap ℚ ℝ)

theorem real_determinant : realMatrix.det = -5 := by
  calc
    realMatrix.det = (phaseMatrix.det : ℝ) := ((algebraMap ℚ ℝ).map_det phaseMatrix).symm
    _ = -5 := by rw [determinant_exact]; norm_num

theorem real_phase_surjective : Function.Surjective realMatrix.mulVec := by
  apply Matrix.mulVec_surjective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det realMatrix).mpr
  rw [real_determinant]
  norm_num

def monomialMap (z : Fin 7 → ℂ) (i : Fin 7) : ℂ := ∏ j, z j ^ exponents i j

theorem monomialMap_exp (theta : Fin 7 → ℝ) (i : Fin 7) :
    monomialMap (fun j => Complex.exp (Complex.I * (theta j : ℂ))) i =
      Complex.exp (Complex.I * ((realMatrix.mulVec theta i : ℝ) : ℂ)) := by
  unfold monomialMap
  simp_rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  change (∑ j, (exponents i j : ℂ) * (Complex.I * (theta j : ℂ))) =
    Complex.I * ((∑ j, (phaseMatrix i j : ℝ) * theta j : ℝ) : ℂ)
  simp only [phaseMatrix]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem unit_phase_surjective (target : Fin 7 → ℂ)
    (ht : ∀ j, Complex.normSq (target j) = 1) :
    ∃ z : Fin 7 → ℂ, (∀ j, Complex.normSq (z j) = 1) ∧ monomialMap z = target := by
  choose phi hphi using fun j =>
    MainTheory.ProbabilityPhaseParametrization.exists_phase (target j) 1 (ht j)
  obtain ⟨theta, htheta⟩ := real_phase_surjective phi
  refine ⟨fun j => Complex.exp (Complex.I * (theta j : ℂ)), ?_, ?_⟩
  · intro j
    simp [Complex.normSq_eq_norm_sq]
  · funext i
    rw [monomialMap_exp, htheta]
    simpa using (hphi i).symm

theorem anchor_row (z : Fin 7 → ℂ) : monomialMap z 0 = z 0 := by
  simp [monomialMap, exponents, Fin.prod_univ_succ]

theorem last_row (z : Fin 7 → ℂ) : monomialMap z 6 =
    z 0 ^ 3 * z 1 ^ 2 * z 2 ^ 2 * z 3 ^ 2 * z 4 ^ 2 * z 5 ^ 2 * z 6 := by
  simp [monomialMap, exponents, Fin.prod_univ_succ, mul_assoc]

end MainTheory.Orbit36PhaseMap
