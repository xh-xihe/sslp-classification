import MainTheory.Orbit7NormalizedProjectors

set_option autoImplicit false

namespace MainTheory.Orbit7FamilyProjectors

open SixQubit.Orbit7Universal MainTheory.Orbit7NormalizedProjectors

theorem outer_family {E : Type*} [DecidableEq E] (F : Finset E)
    (x : E → ℂ) (s : Spinor) :
    (fun i j => ∑ e ∈ F, outer (fun a => x e*s a) i j) =
      ((∑ e ∈ F,Complex.normSq (x e) : ℝ) : ℂ) • outer s := by
  have he (e : E) (i j : Fin 2) : outer (fun a => x e*s a) i j =
      (Complex.normSq (x e) : ℂ)*outer s i j := by
    rw [← SixQubit.star_mul_self]
    simp only [outer,star_mul']
    ring
  funext i j
  simp_rw [he]
  simp only [← Finset.sum_mul,← Complex.ofReal_sum,Pi.smul_apply,smul_eq_mul]

theorem weight_factor {E : Type*} [DecidableEq E] (F : Finset E)
    (x : E → ℂ) (s : Spinor) (k : ℝ)
    (hs : ∑ i : Fin 2,Complex.normSq (s i)=k) :
    (∑ e ∈ F,∑ i : Fin 2,Complex.normSq (x e*s i)) =
      (∑ e ∈ F,Complex.normSq (x e))*k := by
  simp_rw [Complex.normSq_mul,← Finset.mul_sum,hs]
  exact (Finset.sum_mul ..).symm

theorem family_projector {E : Type*} [DecidableEq E] (F : Finset E)
    (x : E → ℂ) (s : Spinor) (k w : ℝ) (hk : 0 < k)
    (hmass : (∑ e ∈ F,Complex.normSq (x e))*k=w) :
    (fun i j => ∑ e ∈ F, outer (fun a => x e*s a) i j) =
      (w : ℂ) • projector s k := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  have hmC : ((∑ e ∈ F,Complex.normSq (x e) : ℝ) : ℂ)*(k : ℂ)=(w : ℂ) := by
    exact_mod_cast hmass
  rw [outer_family,← hmC]
  funext i j
  simp [projector,scaledOuter,outer]
  field_simp

theorem paired_projectors {E : Type*} [DecidableEq E] (F : Finset E)
    (x : E → ℂ) (s t : Spinor) (k w : ℝ) (hk : 0 < k) (hw : w ≠ 0)
    (hmass : (∑ e ∈ F,Complex.normSq (x e))*k=w)
    (R : Matrix (Fin 2) (Fin 2) ℂ)
    (hf : (fun i j => ∑ e ∈ F, outer (fun a => x e*s a) i j) +
      (fun i j => ∑ e ∈ F, outer (fun a => star (x e)*t a) i j) = (w : ℂ) • R) :
    projector s k+projector t k=R := by
  have hb : (∑ e ∈ F,Complex.normSq (star (x e)))*k=w := by simpa using hmass
  rw [family_projector F x s k w hk hmass,
    family_projector F (fun e => star (x e)) t k w hk hb] at hf
  have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  ext i j
  have hh := congrFun (congrFun hf i) j
  change (w : ℂ)*projector s k i j+(w : ℂ)*projector t k i j=(w : ℂ)*R i j at hh
  apply mul_left_cancel₀ hwC
  change (w : ℂ)*(projector s k i j+projector t k i j)=(w : ℂ)*R i j
  linear_combination hh

end MainTheory.Orbit7FamilyProjectors
