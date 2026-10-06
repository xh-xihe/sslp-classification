import MainTheory.Orbit7BoundaryDisplays
import MainTheory.Orbit7NormalizedProjectors

set_option autoImplicit false

namespace MainTheory.Orbit7EndpointDisplays

open SixQubit.Orbit7Universal MainTheory.Orbit7SpinorCoordinates
open MainTheory.Orbit7NormalizedProjectors MainTheory.Orbit7FourHafnians

theorem n_endpoint (c d : ℝ) (hc : c ≠ 0) (h : c^2+d^2=1) :
    (fun i => nvec c d i-((d/c : ℝ) : ℂ)*mvec c d i) =
      (![(1/c : ℝ),0] : Fin 2 → ℂ) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hC : (c : ℂ)^2+(d : ℂ)^2=1 := by exact_mod_cast h
  funext i
  fin_cases i <;> simp [nvec,mvec]
  · field_simp
    linear_combination hC
  · field_simp
    ring

theorem bad_star_sum :
    (fun (P Q : Matrix (Fin 2) (Fin 2) ℂ) =>
      (1/3 : ℂ) • P+(1/2 : ℂ) • Q-(1/2 : ℂ) • P) =
      fun P Q => (1/2 : ℂ) • Q-(1/6 : ℂ) • P := by
  funext P Q i j
  simp
  ring

theorem bad_star_expectation (c d : ℝ) :
    matEval (mvec c d)
      ((1/2 : ℂ) • outer (nvec c d)-(1/6 : ℂ) • outer (![1,0]))
      (mvec c d) = ((-d^2/6 : ℝ) : ℂ) := by
  simp [matEval,nvec,mvec,outer,Fin.sum_univ_two]
  ring

theorem bad_star_negative (d : ℝ) (hd : 0 < d) : -d^2/6 < 0 := by
  nlinarith [sq_pos_of_pos hd]

theorem orthogonal_projector_iff (t p : ℂ)
    (hp : Complex.normSq p=Complex.normSq t) :
    Pa 0 1 t+Pb p=(1 : Matrix (Fin 2) (Fin 2) ℂ) ↔ p = -t := by
  have hk : (1+(Complex.normSq t : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (denominator_positive t)
  have hn : (Complex.normSq t : ℂ)=t*star t := by
    rw [← SixQubit.star_mul_self]
    ring
  constructor
  · intro h
    have hh := congrFun (congrFun h 0) 1
    simp [Pa,Pb,projector,scaledOuter,avec,bvec,hp] at hh
    field_simp at hh
    linear_combination -hh
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Pa,Pb,projector,scaledOuter,avec,bvec,h]
    all_goals field_simp
    all_goals simp only [← SixQubit.star_mul_self,Complex.star_def]
    all_goals ring

theorem orthogonal_affine_equal (T N pT pN nu : ℂ)
    (hT : pT=T+nu) (hN : pN=N+nu) (hTp : pT = -T) (hNp : pN = -N) : T=N := by
  linear_combination (hTp-hT-hNp+hN)/2

end MainTheory.Orbit7EndpointDisplays
