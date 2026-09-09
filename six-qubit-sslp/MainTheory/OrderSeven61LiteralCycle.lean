import MainTheory.OrderSeven61PhaseFlips
import MainTheory.OrderSevenMoment61
import MainTheory.ComplementPhaseRatios

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderSeven61LiteralCycle

open MainTheory.OrderSevenSupportDisplays MainTheory.OrderSeven61PhaseFlips
open MainTheory.ComplementPhaseRatios MainTheory.OrderSevenMoment61 MainTheory.MomentPolytope
open SixQubit.Orbit61 (S0 S1)

noncomputable def r (c d : SS.State 6 ℂ) (i : Fin 9) := rho (c (bottom61 i)) (d (top61 i))

theorem cycle1 (c d : SS.State 6 ℂ) (h3 : c (bottom61 3) ≠ 0) (h4 : c (bottom61 4) ≠ 0)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : r c d 4= -r c d 3 :=
  antisymmetric _ _ _ _ h3 h4 (edge34 c d hc hd hkl)

theorem cycle2 (c d : SS.State 6 ℂ) (h4 : c (bottom61 4) ≠ 0) (h8 : c (bottom61 8) ≠ 0)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : r c d 8= -r c d 4 :=
  antisymmetric _ _ _ _ h4 h8 (edge48 c d hc hd hkl)

theorem cycle_plus (a b c : ℂ) (h1 : b= -a) (h2 : c= -b) : c=a := by
  linear_combination h2-h1

theorem cycle_minus (c d : SS.State 6 ℂ) (h3 : c (bottom61 3) ≠ 0) (h8 : c (bottom61 8) ≠ 0)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : r c d 8= -r c d 3 :=
  antisymmetric _ _ _ _ h3 h8 (edge38 c d hc hd hkl)

theorem no_go (c d : SS.State 6 ℂ) (p : Sum (Fin 9) (Fin 9) → ℝ)
    (H : Feasible bottom61 top61 p)
    (hc : ∀ i,Complex.normSq (c (bottom61 i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (top61 i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ S0 → c x=0) (hs1 : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  obtain ⟨hp0,_⟩ := probabilities p H
  have h3 := (hc 3).trans (congrFun hp0 3)
  have h4 := (hc 4).trans (congrFun hp0 4)
  have h8 := (hc 8).trans (congrFun hp0 8)
  change Complex.normSq (c (bottom61 3))=3/14 at h3
  change Complex.normSq (c (bottom61 4))=1/7 at h4
  change Complex.normSq (c (bottom61 8))=p (Sum.inl 0)+1/14 at h8
  have ht := H.nonneg (Sum.inl 0)
  have nonzero (z : ℂ) (hz : 0<Complex.normSq z) : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hn3 := nonzero _ (by rw [h3]; norm_num)
  have hn4 := nonzero _ (by rw [h4]; norm_num)
  have hn8 := nonzero _ (by rw [h8]; linarith)
  have h1 := cycle1 c d hn3 hn4 hs0 hs1 hkl
  have h2 := cycle2 c d hn4 hn8 hs0 hs1 hkl
  have hp := cycle_plus _ _ _ h1 h2
  have hm := cycle_minus c d hn3 hn8 hs0 hs1 hkl
  have hz : r c d 3=0 := by linear_combination (hm-hp)/2
  have hu : ‖r c d 3‖=1 := unit_norm _ _ hn3 (by
    rw [hc,hd]
    exact equal_probabilities p H 3)
  simp [hz] at hu

end MainTheory.OrderSeven61LiteralCycle
