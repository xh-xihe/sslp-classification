import MainTheory.Orbit7MatrixDisplays
import MainTheory.Orbit7SpinorCoordinates
import MainTheory.Orbit7SixGraphs

set_option autoImplicit false

namespace MainTheory.Orbit7BoundaryDisplays

open SixQubit.Orbit7Universal MainTheory.Orbit7MatrixDisplays
open MainTheory.Orbit7SpinorCoordinates

theorem support_graph_classification (x : Fin 5 × Fin 5 → ℂ)
    (hH : ∀ i, Hafnian5 x i = 0) (hi : ¬ SixQubit.Orbit7Mask.Isolated (supportMask x)) :
    ∃ k : Fin 6, ∃ p : Equiv.Perm (Fin 5), ∀ i j,
      SixQubit.Orbit7Mask.edge (supportMask x) i j =
        SixQubit.Orbit7Mask.edge (MainTheory.Orbit7SixGraphs.templates k) (p i) (p j) :=
  MainTheory.Orbit7SixGraphs.classification _ (supportMask_admissible x hH) hi

theorem frame_projectors (C D : SS.State 6 ℂ)
    (hframe : ∀ i j, sumA C i j = 2*U C i j+3*W D i j) :
    sumA C = (1/3 : ℂ) • Pu C + (1/2 : ℂ) • Pv D := by
  funext i j
  simp [Pu,Pv,hframe]
  ring

theorem outer_scalar_sum {E : Type*} [DecidableEq E] (F : Finset E)
    (y : E → ℂ) (m : Spinor) (hs : ∑ e ∈ F, Complex.normSq (y e) = 1/3) :
    (fun i j => ∑ e ∈ F, outer (fun k => y e*m k) i j) = (1/3 : ℂ) • outer m := by
  have he (e : E) (i j : Fin 2) : outer (fun k => y e*m k) i j =
      (Complex.normSq (y e) : ℂ)*(m i*star (m j)) := by
    rw [← SixQubit.star_mul_self]
    simp only [outer,star_mul']
    ring
  funext i j
  simp_rw [he]
  simp only [← Finset.sum_mul,← Complex.ofReal_sum,hs,Pi.smul_apply,smul_eq_mul,outer]
  norm_num

theorem nonincident_matrix_sum (A : (Fin 5 × Fin 5) → Mat2) (s : Fin 5) (i j : Fin 2) :
    (∑ e ∈ nonincidentPairs s, A e i j) =
      (∑ e ∈ edgePairs, A e i j) - ∑ e ∈ incidentPairs s, A e i j := by
  have h := Finset.sum_filter_add_sum_filter_not edgePairs
    (fun e : Fin 5 × Fin 5 => e.1=s ∨ e.2=s) (fun e => A e i j)
  change (∑ e ∈ incidentPairs s, A e i j) +
    (∑ e ∈ edgePairs.filter (fun e => ¬(e.1=s ∨ e.2=s)),A e i j) = _ at h
  have he : edgePairs.filter (fun e => ¬(e.1=s ∨ e.2=s)) = nonincidentPairs s := by
    ext e
    simp [nonincidentPairs]
  rw [he] at h
  linear_combination h

theorem isolated_remainder (C D : SS.State 6 ℂ) (s : Fin 5) (Pm : Matrix (Fin 2) (Fin 2) ℂ)
    (hf : ∀ i j, sumA C i j = 2*U C i j+3*W D i j)
    (hs : starA C s = (1/3 : ℂ) • Pm) :
    (fun i j => ∑ e ∈ nonincidentPairs s, AMat C e i j) =
      (1/3 : ℂ) • Pu C + (1/2 : ℂ) • Pv D - (1/3 : ℂ) • Pm := by
  have hg := frame_projectors C D hf
  funext i j
  rw [nonincident_matrix_sum]
  change sumA C i j - starA C s i j = _
  rw [hg,hs]
  rfl

theorem isolated_expectation (c d : ℝ) (h : c^2+d^2=1) :
    matEval (mvec c d)
      ((1/3 : ℂ) • outer (![1,0]) + (1/2 : ℂ) • outer (nvec c d) -
        (1/3 : ℂ) • outer (mvec c d)) (mvec c d) = ((-c^2/3 : ℝ) : ℂ) := by
  have hC : (c : ℂ)^2+(d : ℂ)^2=1 := by exact_mod_cast h
  simp [matEval,outer,mvec,nvec,Fin.sum_univ_two]
  linear_combination (-((c : ℂ)^2+(d : ℂ)^2)/3)*hC

theorem isolated_negative (c d : ℝ) (h : c^2+d^2=1) (hc : 0 < c) :
    (1/3 : ℝ)*Complex.normSq (mvec c d 0)-1/3 = -c^2/3 ∧ -c^2/3 < 0 := by
  norm_num [mvec,Complex.normSq_ofReal]
  constructor <;> nlinarith [sq_pos_of_pos hc]

end MainTheory.Orbit7BoundaryDisplays
