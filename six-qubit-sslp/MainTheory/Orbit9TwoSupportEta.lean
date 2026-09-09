import MainTheory.Orbit9TwoSupportPhases
import MainTheory.Orbit9ComponentDisplays

set_option autoImplicit false

namespace MainTheory.Orbit9TwoSupportEta

open SixQubit.Orbit9Universal MainTheory.Orbit9TwoSupportPhases

theorem active_edge_zero (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hs : TwoSupportAt c a b) : damp c a b=0 ∧ camp d a b=0 := by
  have hr := MainTheory.Orbit9TwoSupportDisplays.two_row c d H a b hs a
  have hdiag : damp c a a=0 := by simp [damp]
  rw [hdiag,zero_mul,zero_add] at hr
  have hy : yamp d b ≠ 0 := by
    apply Complex.normSq_pos.mp
    change 0 < q d b
    rw [← pq_equal c d H.support0 H.support1 H.norm0 H.norm1 H.distance b]
    exact hs.right_pos
  have hd := (mul_eq_zero.mp hr).resolve_right (star_ne_zero.mpr hy)
  refine ⟨hd,?_⟩
  rw [camp_eq_rho_mul_star_damp c d H.support0 H.support1 H.distance a b
    (Ne.symm hs.distinct) hs.right_pos,hd,star_zero,mul_zero]

theorem eta_equation (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hs : TwoSupportAt c a b) (z : ℝ) (hz : z ≠ 0)
    (hxa : xamp c a=(z : ℂ)) (hxb : xamp c b=(z : ℂ))
    (hra : rho c d a=1) (eta : ℂ) (hrb : rho c d b=eta)
    (t u : Fin 6) (hta : t ≠ a) (htb : t ≠ b) (hua : u ≠ a) (hub : u ≠ b)
    (htu : t ≠ u) :
    -2*(1+star eta)*star (damp c a t)*star (damp c a u)=0 := by
  obtain ⟨hbt,hat,hct⟩ := phase_form c d H a b hs z hz hxa hxb hra eta hrb t hta htb
  obtain ⟨hbu,hau,hcu⟩ := phase_form c d H a b hs z hz hxa hxb hra eta hrb u hua hub
  obtain ⟨hdab,hcab⟩ := active_edge_zero c d H a b hs
  have hp := MainTheory.Orbit9ComponentDisplays.pair_flip c d H a b t u hs.distinct
    (Ne.symm hta) (Ne.symm hua) (Ne.symm htb) (Ne.symm hub) htu
  rw [hdab,hcab,hbt,hbu,hat,hau,hct,hcu] at hp
  simp only [star_zero,zero_mul,mul_zero,zero_add,star_mul,star_neg] at hp
  linear_combination hp

theorem eta_negative_one (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hs : TwoSupportAt c a b) (z : ℝ) (hz : z ≠ 0)
    (hxa : xamp c a=(z : ℂ)) (hxb : xamp c b=(z : ℂ))
    (hra : rho c d a=1) (eta : ℂ) (hrb : rho c d b=eta)
    (t u : Fin 6) (hta : t ≠ a) (htb : t ≠ b) (hua : u ≠ a) (hub : u ≠ b)
    (htu : t ≠ u) : eta= -1 := by
  have ht := (MainTheory.Orbit9TwoSupportEdges.edges c d H a b hs t hta htb).1
  have hu := (MainTheory.Orbit9TwoSupportEdges.edges c d H a b hs u hua hub).1
  have hnt : damp c a t ≠ 0 := by
    intro hzero
    rw [r_symm c t a] at ht
    have he := (MainTheory.Orbit9MomentDisplays.probability_definitions c d a t).2.2.1
    rw [hzero,Complex.normSq_zero] at he
    linarith
  have hnu : damp c a u ≠ 0 := by
    intro hzero
    rw [r_symm c u a] at hu
    have he := (MainTheory.Orbit9MomentDisplays.probability_definitions c d a u).2.2.1
    rw [hzero,Complex.normSq_zero] at he
    linarith
  have he := eta_equation c d H a b hs z hz hxa hxb hra eta hrb t u hta htb hua hub htu
  have hsEta : 1+star eta=0 := by
    have h1 := (mul_eq_zero.mp he).resolve_right (star_ne_zero.mpr hnu)
    have h2 := (mul_eq_zero.mp h1).resolve_right (star_ne_zero.mpr hnt)
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have h := congrArg star hsEta
  simp only [star_add,star_one,star_star,star_zero] at h
  linear_combination h

end MainTheory.Orbit9TwoSupportEta
