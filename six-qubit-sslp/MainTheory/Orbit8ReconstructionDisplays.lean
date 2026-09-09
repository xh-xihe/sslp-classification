import SixQubit.Orbit8UniversalHafnianIsolate

set_option autoImplicit false

namespace MainTheory.Orbit8ReconstructionDisplays

open SixQubit.Orbit8Universal

theorem sum_away (d : SS.State 6 ℂ) (i j : Fin 6) (hij : i ≠ j) :
    (∑ k : Fin 6,if k ≠ i ∧ k ≠ j then p d k else 0)=r d-p d i-p d j := by
  fin_cases i <;> fin_cases j <;> simp [r,Fin.sum_univ_succ] at hij ⊢ <;> ring

variable (c d : SS.State 6 ℂ)
  (hc : ∀ x,SS.weight av x ≠ 0 → c x=0)
  (hd : ∀ x,SS.weight av x ≠ 1 → d x=0)
  (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
  (hcode : SS.HasDistance ![c,d] 3)

include hc hd hnc hnd hcode

theorem edge_mass_chain (i j : Fin 6) (hij : i ≠ j) :
    w d i j=1/12-(p d i+p d j)/2 ∧
    1/12-(p d i+p d j)/2=(r d-p d i-p d j)/2 ∧
    (r d-p d i-p d j)/2=(1/2 : ℝ)*(∑ k : Fin 6,if k ≠ i ∧ k ≠ j then p d k else 0) := by
  have hr := (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  refine ⟨w_formula c d hc hd hnc hnd hcode i j hij,?_,?_⟩
  · rw [hr]
    ring
  · rw [sum_away d i j hij]
    ring

theorem triple_normalized (b : ℝ) (hb : ball c=(b : ℂ))
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    a c i j k= -(1/(b : ℂ))*(u d i*star (v d j k)+u d j*star (v d i k)+
      u d k*star (v d i j)) := by
  have h := triple_reconstruct c d hc hd hnc hnd hcode i j k hij hik hjk
  have hb0 : (b : ℂ) ≠ 0 := by
    rw [← hb]
    exact (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.2
  simp [hb] at h
  field_simp [hb0]
  simp only [Complex.star_def]
  linear_combination h

theorem hafnian_forced (i j : Fin 6) (hij : i ≠ j) : u d j*compHaf d i j=0 := by
  have h := compHaf_forced c d hc hd hnc hnd hcode i j hij
  rcases mul_eq_zero.mp h with h | h
  · simp [h]
  · simp [star_eq_zero.mp h]

end MainTheory.Orbit8ReconstructionDisplays
