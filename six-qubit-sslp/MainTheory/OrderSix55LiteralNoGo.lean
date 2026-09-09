import MainTheory.OrderSixPhaseRows
import MainTheory.OrderSix55Boundary
import MainTheory.NegativePhaseEquations

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace MainTheory.OrderSix55LiteralNoGo

open MainTheory.OrderSixSupportDisplays MainTheory.OrderSixPhaseRows
open MainTheory.NegativePhaseEquations MainTheory.MomentPolytope
open MainTheory.OrderSixMoment55
open SixQubit.Orbit55 (S0 S1)

noncomputable def phase (c d : SS.State 6 ℂ) :=
  MainTheory.ComplementPhaseRatios.rho (c (bottom55 6)) (d (top55 6))

theorem phase_relation (c d : SS.State 6 ℂ) (h6 : c (bottom55 6) ≠ 0)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 11) (hi : i ∈ ({2,3,4,5,9,10} : Finset (Fin 11))) :
    d (top55 i)= -phase c d*star (c (bottom55 i)) := by
  apply from_anchor _ _ _ _ h6
  fin_cases i <;> norm_num [Fin.ext_iff] at hi
  · exact Orbit55_edge62.equation c d hc hd hkl
  · exact Orbit55_edge63.equation c d hc hd hkl
  · exact Orbit55_edge64.equation c d hc hd hkl
  · exact Orbit55_edge65.equation c d hc hd hkl
  · rw [add_comm]
    exact Orbit55_edge96.equation c d hc hd hkl
  · rw [add_comm]
    exact Orbit55_edge106.equation c d hc hd hkl

theorem binomials (c d : SS.State 6 ℂ) (hc6 : c (bottom55 6) ≠ 0) (hd6 : d (top55 6) ≠ 0)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    c (bottom55 2)*c (bottom55 10)+c (bottom55 3)*c (bottom55 9)=0 ∧
    c (bottom55 4)*c (bottom55 10)+c (bottom55 5)*c (bottom55 9)=0 ∧
    c (bottom55 2)*c (bottom55 5)+c (bottom55 3)*c (bottom55 4)=0 := by
  have hr : phase c d ≠ 0 := div_ne_zero hd6 (star_ne_zero.mpr hc6)
  have hrel := phase_relation c d hc6 hc hd hkl
  constructor
  · apply four_binomial (phase c d) _ _ _ _ _ _ _ _ hr
      (hrel 2 (by decide)) (hrel 10 (by decide)) (hrel 3 (by decide)) (hrel 9 (by decide))
    have h := Orbit55_binomial1.equation c d hc hd hkl
    linear_combination h
  constructor
  · apply four_binomial (phase c d) _ _ _ _ _ _ _ _ hr
      (hrel 4 (by decide)) (hrel 10 (by decide)) (hrel 5 (by decide)) (hrel 9 (by decide))
    have h := Orbit55_binomial2.equation c d hc hd hkl
    linear_combination h
  · apply four_binomial (phase c d) _ _ _ _ _ _ _ _ hr
      (hrel 2 (by decide)) (hrel 5 (by decide)) (hrel 3 (by decide)) (hrel 4 (by decide))
    have h := Orbit55_binomial3.equation c d hc hd hkl
    linear_combination h

theorem no_go (c d : SS.State 6 ℂ) (p : Sum (Fin 11) (Fin 11) → ℝ)
    (H : Feasible bottom55 top55 p)
    (hc : ∀ i,Complex.normSq (c (bottom55 i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (top55 i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ S0 → c x=0) (hs1 : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  obtain ⟨hp0,hp1⟩ := probabilities p H
  have hc6 := (hc 6).trans (congrFun hp0 6)
  have hd6 := (hd 6).trans (congrFun hp1 6)
  change Complex.normSq (c (bottom55 6))=1/6 at hc6
  change Complex.normSq (d (top55 6))=1/6 at hd6
  have nonzero (z : ℂ) (h : 0<Complex.normSq z) : z ≠ 0 := by
    intro hz
    simp [hz] at h
  have hcn := nonzero _ (by rw [hc6]; norm_num)
  have hdn := nonzero _ (by rw [hd6]; norm_num)
  obtain ⟨b1,b2,b3⟩ := binomials c d hcn hdn hs0 hs1 hkl
  have m1 := binomial_magnitudes _ _ _ _ b1
  have m3 := binomial_magnitudes _ _ _ _ b3
  have he : ∀ i,Complex.normSq (c (bottom55 i))=
      pattern (p (Sum.inl 4)) (p (Sum.inl 3)) (p (Sum.inl 2)) (p (Sum.inl 0)) i := by
    intro i
    exact (hc i).trans (congrFun hp0 i)
  simp_rw [he] at m1 m3
  have hn : ∀ i,0 ≤ pattern (p (Sum.inl 4)) (p (Sum.inl 3)) (p (Sum.inl 2)) (p (Sum.inl 0)) i := by
    intro i
    rw [← congrFun hp0 i]
    exact H.nonneg (Sum.inl i)
  obtain ⟨h2,h3,_,h5,_,h10⟩ := MainTheory.OrderSix55Boundary.of_pattern _ _ _ _ hn m1 m3
  exact odd_binomials _ _ _ _ _ _
    (nonzero _ (by rw [he]; exact h2)) (nonzero _ (by rw [he]; exact h3))
    (nonzero _ (by rw [he]; exact h5)) (nonzero _ (by rw [he]; exact h10)) b1 b2 b3

end MainTheory.OrderSix55LiteralNoGo
