import MainTheory.Orbit9TwoSupportEta

set_option autoImplicit false

namespace MainTheory.Orbit9TwoSupportExpectations

open SixQubit.Orbit9Universal

theorem opposite_expectations (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hs : TwoSupportAt c 0 1) (z : ℝ) (hz : z ≠ 0)
    (hx0 : xamp c 0=(z : ℂ)) (hx1 : xamp c 1=(z : ℂ)) (hr0 : rho c d 0=1) :
    SS.innerC c (SixQubit.Orbit8Universal.hop 0 1 c)=(1/2 : ℂ) ∧
    SS.innerC d (SixQubit.Orbit8Universal.hop 0 1 d)=(-1/2 : ℂ) := by
  have hr1 := MainTheory.Orbit9TwoSupportEta.eta_negative_one c d H 0 1 hs z hz hx0 hx1
    hr0 (rho c d 1) rfl 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp (t : Fin 6) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
      damp c 1 t=damp c 0 t ∧ camp d 0 t=star (damp c 0 t) ∧
      camp d 1 t= -star (damp c 0 t) := by
    simpa using MainTheory.Orbit9TwoSupportPhases.phase_form c d H 0 1 hs z hz hx0 hx1
      hr0 (-1) hr1 t ht0 ht1
  have hprod (t : Fin 6) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
      star (damp c 0 t)*damp c 0 t=(1/12 : ℂ) := by
    have he := (MainTheory.Orbit9MomentDisplays.probability_definitions c d 0 t).2.2.1
    rw [r_symm c 0 t,(MainTheory.Orbit9TwoSupportEdges.edges c d H 0 1 hs t ht0 ht1).1] at he
    calc
      star (damp c 0 t)*damp c 0 t=(Complex.normSq (damp c 0 t) : ℂ) :=
        Complex.normSq_eq_conj_mul_self.symm
      _ = (1/12 : ℂ) := by rw [← he]; norm_num
  have hbottom (t : Fin 6) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
      star (damp c 1 t)*damp c 0 t=(1/12 : ℂ) := by
    rw [(hp t ht0 ht1).1]
    exact hprod t ht0 ht1
  have htop (t : Fin 6) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
      star (camp d 0 t)*camp d 1 t=(-1/12 : ℂ) := by
    rw [(hp t ht0 ht1).2.1,(hp t ht0 ht1).2.2,star_star]
    have hn := hprod t ht0 ht1
    linear_combination -hn
  have hzz : (z : ℂ)*(z : ℂ)=(1/6 : ℂ) := by
    have h := (MainTheory.Orbit9TwoSupportDisplays.probabilities c d H 0 1 hs).1
    change Complex.normSq (xamp c 0)=(1/6 : ℝ) at h
    rw [hx0] at h
    simp only [Complex.normSq_apply,Complex.ofReal_re,Complex.ofReal_im,mul_zero,add_zero] at h
    have hh := congrArg (fun v : ℝ => (v : ℂ)) h
    push_cast at hh
    exact hh
  have hy0 : yamp d 0=(z : ℂ) := by
    have h := rho_mul_star_xamp c d 0 hs.left_pos
    simpa [hr0,hx0] using h.symm
  have hy1 : yamp d 1= -(z : ℂ) := by
    have h := rho_mul_star_xamp c d 1 hs.right_pos
    simpa [hr1,hx1] using h.symm
  constructor
  · rw [inner_hop01_S0 c H.support0,hx0,hx1,
      hbottom 2 (by decide) (by decide),hbottom 3 (by decide) (by decide),
      hbottom 4 (by decide) (by decide),hbottom 5 (by decide) (by decide)]
    simp only [Complex.star_def,Complex.conj_ofReal]
    linear_combination hzz
  · rw [inner_hop01_S1 d H.support1,hy0,hy1,
      htop 2 (by decide) (by decide),htop 3 (by decide) (by decide),
      htop 4 (by decide) (by decide),htop 5 (by decide) (by decide)]
    simp only [star_neg,Complex.star_def,Complex.conj_ofReal]
    linear_combination -hzz

end MainTheory.Orbit9TwoSupportExpectations
