import MainTheory.Orbit9DegreeBudgets
import SixQubit.Orbit9S2Transport

set_option autoImplicit false

namespace MainTheory.Orbit9TwoSupportDisplays

open SixQubit.Orbit9Universal SixQubit.CodeEquiv

theorem sum_two (f : Fin 6 → ℂ) (a b : Fin 6) (hab : a ≠ b)
    (hz : ∀ i,i ≠ a → i ≠ b → f i=0) : (∑ i,f i)=f a+f b := by
  classical
  have hs : (∑ i ∈ ({a,b} : Finset (Fin 6)),f i)=∑ i,f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hn : i ≠ a ∧ i ≠ b := by simpa using hi
    exact hz i hn.1 hn.2
  rw [← hs,Finset.sum_pair hab]

theorem two_row (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hs : TwoSupportAt c a b) (t : Fin 6) :
    damp c t a*star (yamp d a)+damp c t b*star (yamp d b)=0 := by
  have hr := companion_row_univ c d H t
  have hz (i : Fin 6) (hia : i ≠ a) (hib : i ≠ b) : damp c t i*star (yamp d i)=0 := by
    have hq : q d i=0 := by
      rw [← pq_equal c d H.support0 H.support1 H.norm0 H.norm1 H.distance i]
      exact hs.other_zero i hia hib
    have hy : yamp d i=0 := Complex.normSq_eq_zero.mp hq
    rw [hy,star_zero,mul_zero]
  rwa [sum_two _ a b hs.distinct hz] at hr

theorem probabilities (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hs : TwoSupportAt c a b) : p c a=1/6 ∧ p c b=1/6 := by
  let sigma := pairTo01 a b
  have ha : sigma a=0 := pairTo01_apply_left a b hs.distinct
  have hb : sigma b=1 := pairTo01_apply_right a b
  have hs' := twoSupport01_permAct_of_twoSupportAt c a b hs
  have hn0 : SS.innerC (permAct sigma c) (permAct sigma c)=1 := by
    rw [innerC_permAct,H.norm0]
  have hn1 : SS.innerC (permAct sigma d) (permAct sigma d)=1 := by
    rw [innerC_permAct,H.norm1]
  obtain ⟨hp0,hp1,_⟩ := twoSupport01_probabilities (permAct sigma c) (permAct sigma d)
    (support_S0_permAct sigma c H.support0) (support_S1_permAct sigma d H.support1)
    hn0 hn1 (hasDistance_permAct sigma c d H.distance) hs'
  rw [← ha,p_permAct,Equiv.symm_apply_apply] at hp0
  rw [← hb,p_permAct,Equiv.symm_apply_apply] at hp1
  exact ⟨hp0,hp1⟩

theorem monotone_equation (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hs : TwoSupportAt c a b) :
    p c a*(1/6+p c a)=p c b*(1/6+p c b) := by
  obtain ⟨ha,hb⟩ := probabilities c d H a b hs
  rw [ha,hb]

theorem probability_function_strict (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) :
    x*(1/6+x) < y*(1/6+y) := by nlinarith

end MainTheory.Orbit9TwoSupportDisplays
