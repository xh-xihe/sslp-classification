import MainTheory.Orbit7BoundaryDisplays

set_option autoImplicit false

namespace MainTheory.Orbit7BoundaryMass

open SixQubit.Orbit7Universal MainTheory.Orbit7SpinorCoordinates

theorem eval_outer (s a : Spinor) :
    matEval s (outer a) s = (Complex.normSq (spinInner s a) : ℂ) := by
  have he : matEval s (outer a) s = spinInner s a * spinInner a s := by
    simp only [matEval,outer,spinInner,Fin.sum_univ_two]
    ring
  rw [he,← star_spinInner s a,← SixQubit.star_mul_self]
  exact mul_comm _ _

theorem eval_sum {E : Type*} [DecidableEq E] (F : Finset E)
    (s : Spinor) (M : E → Mat2) :
    matEval s (fun i j => ∑ e ∈ F, M e i j) s = ∑ e ∈ F, matEval s (M e) s := by
  simp [matEval,Finset.mul_sum,Finset.sum_mul,Finset.sum_comm]

theorem xmass {E : Type*} [DecidableEq E] (F : Finset E)
    (a : E → Spinor) (c d : ℝ) (hcd : c^2+d^2=1)
    (hf : (fun i j => ∑ e ∈ F, outer (a e) i j) =
      (1/3 : ℂ) • outer (![1,0]) + (1/2 : ℂ) • outer (nvec c d)) :
    (∑ e ∈ F, Complex.normSq (spinInner (nvec c d) (a e))) = (3+2*c^2)/6 ∧
      (1/2 : ℝ) ≤ (3+2*c^2)/6 := by
  have hC : (c : ℂ)^2+(d : ℂ)^2=1 := by exact_mod_cast hcd
  have he : matEval (nvec c d)
      ((1/3 : ℂ) • outer (![1,0]) + (1/2 : ℂ) • outer (nvec c d)) (nvec c d) =
      (((3+2*c^2)/6 : ℝ) : ℂ) := by
    simp [matEval,outer,nvec,Fin.sum_univ_two]
    linear_combination (((c : ℂ)^2+(d : ℂ)^2+1)/2)*hC
  have hh := congrArg (fun M => matEval (nvec c d) M (nvec c d)) hf
  change matEval (nvec c d) (fun i j => ∑ e ∈ F, outer (a e) i j) (nvec c d) = _ at hh
  rw [eval_sum F (nvec c d) (fun e => outer (a e))] at hh
  simp_rw [eval_outer] at hh
  rw [he,← Complex.ofReal_sum] at hh
  constructor
  · exact_mod_cast hh
  · nlinarith [sq_nonneg c]

end MainTheory.Orbit7BoundaryMass
