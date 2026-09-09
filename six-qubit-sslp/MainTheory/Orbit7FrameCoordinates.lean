import MainTheory.Orbit7BoundaryMass
import MainTheory.Orbit7FourHafnians

set_option autoImplicit false

namespace MainTheory.Orbit7FrameCoordinates

open SixQubit.Orbit7Universal MainTheory.Orbit7SpinorCoordinates
open MainTheory.Orbit7FourHafnians

theorem xz_total {E : Type*} [DecidableEq E] (F : Finset E)
    (x z : E → ℂ) (c d : ℝ)
    (hf : (fun i j => ∑ e ∈ F, outer (bvec (x e) (z e)) i j) =
      (1/2 : ℂ) • outer (![1,0]) + (1/3 : ℂ) • outer (nvec c d)) :
    (∑ e ∈ F, star (x e)*z e) = -(c : ℂ)*(d : ℂ)/3 := by
  have hh := congrFun (congrFun hf 0) 1
  simp [outer,bvec,nvec] at hh
  simp only [Complex.star_def]
  linear_combination -hh

theorem constant_slope_impossible (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    -(d/c)*((3+2*c^2)/6) ≠ -(c*d)/3 := by
  intro h
  have hh := h
  field_simp at hh
  have hz : d=0 := by nlinarith
  exact hd hz

end MainTheory.Orbit7FrameCoordinates
