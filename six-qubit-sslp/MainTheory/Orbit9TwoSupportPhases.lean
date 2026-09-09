import MainTheory.Orbit9TwoSupportEdges

set_option autoImplicit false

namespace MainTheory.Orbit9TwoSupportPhases

open SixQubit.Orbit9Universal

theorem rho_normSq (c d : SS.State 6 ℂ) (H : FullKL c d) (i : Fin 6) (hi : Active c i) :
    Complex.normSq (rho c d i)=1 := by
  have hpq := pq_equal c d H.support0 H.support1 H.norm0 H.norm1 H.distance i
  change Complex.normSq (xamp c i)=Complex.normSq (yamp d i) at hpq
  rw [rho,Complex.normSq_div]
  simp only [Complex.star_def,Complex.normSq_conj]
  rw [← hpq]
  exact div_self (ne_of_gt hi)

theorem rho_unit (c d : SS.State 6 ℂ) (H : FullKL c d) (i : Fin 6) (hi : Active c i) :
    rho c d i*star (rho c d i)=1 := by
  have h : star (rho c d i)*rho c d i=(Complex.normSq (rho c d i) : ℂ) :=
    Complex.normSq_eq_conj_mul_self.symm
  rw [rho_normSq c d H i hi] at h
  simpa only [mul_comm,Complex.ofReal_one] using h

theorem phase_form (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hs : TwoSupportAt c a b) (z : ℝ) (hz : z ≠ 0)
    (hxa : xamp c a=(z : ℂ)) (hxb : xamp c b=(z : ℂ))
    (hra : rho c d a=1) (eta : ℂ) (hrb : rho c d b=eta)
    (t : Fin 6) (hta : t ≠ a) (htb : t ≠ b) :
    damp c b t= -eta*damp c a t ∧ camp d a t=star (damp c a t) ∧
      camp d b t= -star (damp c a t) := by
  have hu : eta*star eta=1 := hrb ▸ rho_unit c d H b hs.right_pos
  have hya : yamp d a=(z : ℂ) := by
    have h := rho_mul_star_xamp c d a hs.left_pos
    simpa [hra,hxa] using h.symm
  have hyb : yamp d b=eta*(z : ℂ) := by
    have h := rho_mul_star_xamp c d b hs.right_pos
    simpa [hrb,hxb] using h.symm
  have hrow := MainTheory.Orbit9TwoSupportDisplays.two_row c d H a b hs t
  rw [damp_symm c t a,damp_symm c t b,hya,hyb,star_mul] at hrow
  simp only [Complex.star_def,Complex.conj_ofReal] at hrow
  have hfac : (damp c a t+star eta*damp c b t)*(z : ℂ)=0 := by
    simp only [Complex.star_def]
    linear_combination hrow
  have hr : damp c a t+star eta*damp c b t=0 :=
    (mul_eq_zero.mp hfac).resolve_right (by exact_mod_cast hz)
  have hdb : damp c b t= -eta*damp c a t := by
    linear_combination eta*hr-damp c b t*hu
  have hca := camp_eq_rho_mul_star_damp c d H.support0 H.support1 H.distance t a
    (Ne.symm hta) hs.left_pos
  have hcb := camp_eq_rho_mul_star_damp c d H.support0 H.support1 H.distance t b
    (Ne.symm htb) hs.right_pos
  rw [camp_symm d t a,damp_symm c t a,hra,one_mul] at hca
  rw [camp_symm d t b,damp_symm c t b,hrb,hdb,star_mul,star_neg] at hcb
  refine ⟨hdb,hca,?_⟩
  linear_combination hcb-star (damp c a t)*hu

end MainTheory.Orbit9TwoSupportPhases
