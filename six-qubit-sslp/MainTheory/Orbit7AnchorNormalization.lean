import MainTheory.TwoSpinorScaledForm
import SixQubit.Orbit7Boundary

set_option autoImplicit false

namespace MainTheory.Orbit7AnchorNormalization

open SixQubit.Orbit7Universal MainTheory.TwoSpinorNormalization

theorem unit_coordinates (alpha : ℝ) (h0 : 0 ≤ alpha) (h1 : alpha ≤ 1) :
    alpha^2 + (Real.sqrt (1-alpha^2))^2 = 1 := by
  rw [Real.sq_sqrt (by nlinarith : 0 ≤ 1-alpha^2)]
  ring

theorem anchor_normal_form (c d : SS.State 6 ℂ)
    (hu : uMass c = 1/6) (hv : vMass d = 1/6) :
    ∃ (T : Mat) (lambda : ℂ) (alpha : ℝ),
      T * T.conjTranspose = 1 ∧ T.conjTranspose * T = 1 ∧
      Complex.normSq lambda = 1 ∧ 0 ≤ alpha ∧ alpha ≤ 1 ∧
      (fun i => lambda * (T.mulVec (uSpin c) i)) =
        ![1/(Real.sqrt 6 : ℂ),0] ∧
      T.mulVec (vSpin d) =
        ![(alpha : ℂ)/(Real.sqrt 6 : ℂ),
          (Real.sqrt (1-alpha^2) : ℂ)/(Real.sqrt 6 : ℂ)] := by
  let r : ℝ := 1/Real.sqrt 6
  have hr : 0 < r := one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  have hr2 : r^2 = 1/6 := by
    dsimp only [r]
    rw [div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num
  have hu' : Complex.normSq (uSpin c 0) + Complex.normSq (uSpin c 1) = r^2 := by
    rw [hr2]
    exact hu
  have hv' : Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1) = r^2 := by
    rw [hr2]
    exact hv
  obtain ⟨T,lambda,alpha,hT,hT',hl,ha0,ha1,h0,h1⟩ :=
    scaled_standard_form (uSpin c) (vSpin d) r hr hu' hv'
  refine ⟨T,lambda,alpha,hT,hT',hl,ha0,ha1,?_,?_⟩
  · simpa [r] using h0
  · simpa [r,div_eq_mul_inv,mul_comm] using h1

end MainTheory.Orbit7AnchorNormalization
