import MainTheory.Orbit7FourHafnians
import SixQubit.Orbit7PairSum

set_option autoImplicit false

namespace MainTheory.Orbit7AffineDisplays

open SixQubit.Orbit7Universal MainTheory.Orbit7SpinorCoordinates
open MainTheory.Orbit7FourHafnians

theorem amplitude_factors (c d : ℝ) (x t p : ℂ) :
    avec c d x (t*x) = (fun i => x*(nvec c d i+t*mvec c d i)) ∧
    bvec x (p*x) = (fun i => star x*(![-1,star p] : Spinor) i) := by
  constructor
  all_goals funext i; fin_cases i <;> simp [avec,nvec,mvec,bvec] <;> ring

theorem parameter_norm (x t p : ℂ) (hx : x ≠ 0) (h : ‖p*x‖=‖t*x‖) : ‖p‖=‖t‖ := by
  simp only [norm_mul] at h
  exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hx) h

theorem cross_factor (c d : ℝ) (xe xf te tf pe pf : ℂ) :
    spinInner (avec c d xe (te*xe)) (bvec xf (pf*xf)) -
      spinInner (avec c d xf (tf*xf)) (bvec xe (pe*xe)) =
      star (xe*xf)*star ((d : ℂ)*(te-tf+pf-pe)+(c : ℂ)*(te*pf-tf*pe)) := by
  simp [spinInner,avec,bvec]
  ring

theorem disjoint_equation (c d : ℝ) (xe xf te tf pe pf : ℂ)
    (he : xe ≠ 0) (hf : xf ≠ 0)
    (h : spinInner (avec c d xe (te*xe)) (bvec xf (pf*xf)) =
      spinInner (avec c d xf (tf*xf)) (bvec xe (pe*xe))) :
    (d : ℂ)*(te-tf+pf-pe)+(c : ℂ)*(te*pf-tf*pe)=0 := by
  have hh := cross_factor c d xe xf te tf pe pf
  rw [h,sub_self] at hh
  have hz := (mul_eq_zero.mp hh.symm).resolve_left (star_ne_zero.mpr (mul_ne_zero he hf))
  exact star_eq_zero.mp hz

theorem factored_disjoint (c d te tf pe pf : ℂ) (hd : d ≠ 0)
    (h : d*(te-tf+pf-pe)+c*(te*pf-tf*pe)=0) :
    (te-pe)*(1+(c/d)*tf)=(tf-pf)*(1+(c/d)*te) := by
  apply (mul_right_cancel₀ hd)
  field_simp
  linear_combination h

noncomputable def hvertex (k : ℂ) (r : Fin 5 → ℂ) (i : Fin 5) : ℂ := 1/2+k*r i
noncomputable def delta (r q : Fin 5 → ℂ) (i : Fin 5) : ℂ := q i-r i

theorem pair_condition (k : ℂ) (r q : Fin 5 → ℂ) (i j a b : Fin 5)
    (h : ((r i+r j)-(q i+q j))*(1+k*(r a+r b)) =
      ((r a+r b)-(q a+q b))*(1+k*(r i+r j))) :
    (hvertex k r i+hvertex k r j)*(delta r q a+delta r q b) =
      (hvertex k r a+hvertex k r b)*(delta r q i+delta r q j) := by
  simp only [hvertex,delta]
  linear_combination h

theorem affine_parameters (k lambda : ℂ) (r q : Fin 5 → ℂ)
    (h : ∀ i,delta r q i=lambda*hvertex k r i) (i j : Fin 5) :
    q i+q j = (1+lambda*k)*(r i+r j)+lambda := by
  have hi := h i
  have hj := h j
  simp only [delta,hvertex] at hi hj
  linear_combination hi+hj

theorem twice_vector {V : Type*} [AddCommGroup V] (u v w : V) :
    u+u=(u+v)+(u+w)-(v+w) := by abel

theorem polar_affine (x y : Fin 5 × Fin 5 → ℂ) (mu nu : ℂ) (i : Fin 5) :
    PolarHafnian5 y (fun e => mu*y e+nu*x e) i =
      2*mu*Hafnian5 y i+nu*PolarHafnian5 x y i := by
  fin_cases i <;> simp [PolarHafnian5,Hafnian5] <;> ring

theorem hafnian_y_zero (x y : Fin 5 × Fin 5 → ℂ) (mu nu : ℂ) (hm : mu ≠ 0)
    (hxy : ∀ i,PolarHafnian5 x y i=0)
    (hyz : ∀ i,PolarHafnian5 y (fun e => mu*y e+nu*x e) i=0) :
    ∀ i,Hafnian5 y i=0 := by
  intro i
  have h := hyz i
  rw [polar_affine,hxy i,mul_zero,add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hm)

end MainTheory.Orbit7AffineDisplays
