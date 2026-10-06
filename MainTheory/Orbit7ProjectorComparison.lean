import MainTheory.Orbit7NormalizedProjectors
import SixQubit.Orbit7ProjectorAlgebra

set_option autoImplicit false

namespace MainTheory.Orbit7ProjectorComparison

open SixQubit.Orbit7Universal MainTheory.Orbit7SpinorCoordinates
open MainTheory.Orbit7FourHafnians MainTheory.Orbit7NormalizedProjectors

theorem cleared_entries (c d : ℝ) (t p : ℂ)
    (hp : Complex.normSq p=Complex.normSq t)
    (hf : Pa c d t+Pb p=outer (![1,0])+outer (nvec c d)) :
    ((c : ℂ)-(d : ℂ)*t)*((c : ℂ)-(d : ℂ)*star t)+1 =
      (1+t*star t)*(1+(c : ℂ)*(c : ℂ)) ∧
    ((c : ℂ)-(d : ℂ)*t)*((d : ℂ)+(c : ℂ)*star t)-p =
      (1+t*star t)*((c : ℂ)*(d : ℂ)) := by
  have hk : (1+(Complex.normSq t : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (denominator_positive t)
  have hn : (Complex.normSq t : ℂ)=t*star t := by
    rw [← SixQubit.star_mul_self]
    ring
  have h00 := congrFun (congrFun hf 0) 0
  have h01 := congrFun (congrFun hf 0) 1
  simp [Pa,Pb,projector,scaledOuter,avec,bvec,outer,nvec,hp] at h00 h01
  field_simp at h00 h01
  rw [hn] at h00 h01
  simp only [Complex.star_def] at h00 h01 ⊢
  constructor
  · linear_combination h00
  · linear_combination h01

theorem circle_and_conjugate (c d : ℝ) (t p : ℂ) (hc : c ≠ 0)
    (hu : c^2+d^2=1) (hp : Complex.normSq p=Complex.normSq t)
    (hf : Pa c d t+Pb p=outer (![1,0])+outer (nvec c d)) :
    c*Complex.normSq t+d*t.re=0 ∧ p=star t := by
  obtain ⟨h00,h01⟩ := cleared_entries c d t p hp hf
  have huC : (c : ℂ)*(c : ℂ)+(d : ℂ)*(d : ℂ)=1 := by
    exact_mod_cast (show c*c+d*d=1 by nlinarith [hu])
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  obtain ⟨hcircle,hconj⟩ := SixQubit.Orbit7ProjectorAlgebra.projector_entries_force_conj
    (c : ℂ) (d : ℂ) t p huC hcC h00 h01
  refine ⟨?_,hconj⟩
  have hr := congrArg Complex.re hcircle
  simp [Complex.mul_re,Complex.normSq_apply] at hr ⊢
  nlinarith

end MainTheory.Orbit7ProjectorComparison
