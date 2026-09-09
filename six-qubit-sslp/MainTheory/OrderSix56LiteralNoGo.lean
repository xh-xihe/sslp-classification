import MainTheory.OrderSixPhaseRows
import MainTheory.OrderSixForcedParameters
import MainTheory.OrderSix56MomentClosure
import MainTheory.NegativePhaseEquations

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace MainTheory.OrderSix56LiteralNoGo

open MainTheory.OrderSixSupportDisplays MainTheory.OrderSixPhaseRows
open MainTheory.NegativePhaseEquations MainTheory.MomentPolytope
open MainTheory.OrderSixMoment56 MainTheory.ComplementPhaseRatios
open SixQubit.Orbit56 (S0 S1)

noncomputable def phase (c d : SS.State 6 ℂ) := rho (c (bottom56 1)) (d (top56 1))

theorem phase_relation (c d : SS.State 6 ℂ) (h1 : c (bottom56 1) ≠ 0)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 10) (hi : 2 ≤ i.val ∧ i.val ≤ 7) :
    d (top56 i)= -phase c d*star (c (bottom56 i)) := by
  apply from_anchor _ _ _ _ h1
  fin_cases i <;> norm_num at hi
  · exact Orbit56_edge1_2.equation c d hc hd hkl
  · exact Orbit56_edge1_3.equation c d hc hd hkl
  · exact Orbit56_edge1_4.equation c d hc hd hkl
  · exact Orbit56_edge1_5.equation c d hc hd hkl
  · exact Orbit56_edge1_6.equation c d hc hd hkl
  · exact Orbit56_edge1_7.equation c d hc hd hkl

theorem binomials (c d : SS.State 6 ℂ) (hc1 : c (bottom56 1) ≠ 0) (hd1 : d (top56 1) ≠ 0)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    c (bottom56 3)*c (bottom56 7)+c (bottom56 4)*c (bottom56 6)=0 ∧
    c (bottom56 2)*c (bottom56 7)+c (bottom56 4)*c (bottom56 5)=0 ∧
    c (bottom56 2)*c (bottom56 6)+c (bottom56 3)*c (bottom56 5)=0 := by
  have hr : phase c d ≠ 0 := div_ne_zero hd1 (star_ne_zero.mpr hc1)
  have hrel := phase_relation c d hc1 hc hd hkl
  constructor
  · apply four_binomial (phase c d) _ _ _ _ _ _ _ _ hr
      (hrel 3 (by decide)) (hrel 7 (by decide)) (hrel 4 (by decide)) (hrel 6 (by decide))
    exact Orbit56_binomial1.equation c d hc hd hkl
  constructor
  · apply four_binomial (phase c d) _ _ _ _ _ _ _ _ hr
      (hrel 2 (by decide)) (hrel 7 (by decide)) (hrel 4 (by decide)) (hrel 5 (by decide))
    exact Orbit56_binomial2.equation c d hc hd hkl
  · apply four_binomial (phase c d) _ _ _ _ _ _ _ _ hr
      (hrel 2 (by decide)) (hrel 6 (by decide)) (hrel 3 (by decide)) (hrel 5 (by decide))
    exact Orbit56_binomial3.equation c d hc hd hkl

theorem no_go (c d : SS.State 6 ℂ) (p : Sum (Fin 10) (Fin 10) → ℝ)
    (H : Feasible bottom56 top56 p)
    (hc : ∀ i,Complex.normSq (c (bottom56 i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (top56 i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ S0 → c x=0) (hs1 : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  obtain ⟨hp0,hp1⟩ := probabilities p H
  have ht := MainTheory.OrderSixForcedParameters.orbit56 c d p H hc hd hs0 hs1 hkl
  have hc1 := (hc 1).trans (congrFun hp0 1)
  have hd1 := (hd 1).trans (congrFun hp1 1)
  change Complex.normSq (c (bottom56 1))=1/4-p (Sum.inl 0) at hc1
  change Complex.normSq (d (top56 1))=1/4-p (Sum.inl 0) at hd1
  rw [ht] at hc1 hd1
  have nonzero (z : ℂ) (h : 0<Complex.normSq z) : z ≠ 0 := by
    intro hz
    simp [hz] at h
  have hcn := nonzero _ (by rw [hc1]; norm_num)
  have hdn := nonzero _ (by rw [hd1]; norm_num)
  obtain ⟨b1,b2,b3⟩ := binomials c d hcn hdn hs0 hs1 hkl
  have m1 := binomial_magnitudes _ _ _ _ b1
  have m3 := binomial_magnitudes _ _ _ _ b3
  have he : ∀ i,Complex.normSq (c (bottom56 i))=
      pattern (p (Sum.inl 3)) (p (Sum.inl 2)) (p (Sum.inl 0)) i := by
    intro i
    exact (hc i).trans (congrFun hp0 i)
  simp_rw [he] at m1 m3
  obtain ⟨hr,hs⟩ := MainTheory.OrderSix56MomentClosure.parameters _ _ _ m1 m3
  have hC : ∀ i,c (bottom56 i) ≠ 0 := by
    intro i
    apply nonzero
    rw [he,hr,hs,ht]
    exact MainTheory.OrderSix56MomentClosure.positive i
  apply odd_binomials (c (bottom56 3)) (c (bottom56 6)) (c (bottom56 4)) (c (bottom56 7))
    (c (bottom56 2)) (c (bottom56 5)) (hC 3) (hC 6) (hC 7) (hC 5)
  · linear_combination b3
  · linear_combination b2
  · linear_combination b1

end MainTheory.OrderSix56LiteralNoGo
