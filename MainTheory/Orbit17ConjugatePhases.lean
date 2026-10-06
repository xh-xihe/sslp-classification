import MainTheory.Orbit17MomentDisplays
import MainTheory.Orbit17PhaseData
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit17ConjugatePhases
open scoped BigOperators
open SixQubit.Orbit17 MainTheory.Orbit17MomentDisplays MainTheory.Orbit17PhaseData
noncomputable section
def phaseRatio (c d : SS.State 6 ℂ) : ℂ := -d z15/star (c y0)
theorem scalar_anchor_phase (a b u v : ℂ) (ha : a≠0)
    (he : star a*v+star u*b=0) : v=(-b/star a)*star u := by
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (star_ne_zero.mpr ha)).mpr
  linear_combination he
theorem indexed_anchor_flips (c d : SS.State 6 ℂ) (h : PhaseData c d) (e : Fin 15) :
    star (c y0)*d (top ⟨14-e.val,by omega⟩)+
      star (c (bottom ⟨e.val+1,by omega⟩))*d z15=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50⟩ := h
  fin_cases e <;> norm_num [bottom,top] <;> assumption
theorem physical_phase_unit (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Complex.normSq (phaseRatio c d)=1 := by
  have hm := physical_moments c d hc hd hnc hnd hkl
  have ha := bottom_anchor _ _ hm
  have hb := top_anchor _ _ hm
  change Complex.normSq (c y0)=1/4 at ha
  change Complex.normSq (d z15)=1/4 at hb
  simp [phaseRatio,Complex.normSq_conj,ha,hb]
theorem physical_conjugate_phases (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (e : Fin 15) :
    d (top ⟨14-e.val,by omega⟩)=
      phaseRatio c d*star (c (bottom ⟨e.val+1,by omega⟩)) := by
  have hm := physical_moments c d hc hd hnc hnd hkl
  have han := bottom_anchor _ _ hm
  change Complex.normSq (c y0)=1/4 at han
  have hne : c y0≠0 := by intro hz; rw [hz] at han; norm_num at han
  exact scalar_anchor_phase _ _ _ _ hne
    (indexed_anchor_flips c d (physical_phase_data c d hc hd hnc hnd hkl) e)
end
end MainTheory.Orbit17ConjugatePhases
