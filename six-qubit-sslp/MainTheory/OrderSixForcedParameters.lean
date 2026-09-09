import MainTheory.OrderSixWalshMagnitudes
import MainTheory.OrderSixMomentPinning

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderSixForcedParameters
open MainTheory.OrderSixSupportDisplays MainTheory.MomentPolytope


theorem orbit53 (c d : SS.State 6 ℂ) (p : Sum (Fin 10) (Fin 10) → ℝ)
    (H : Feasible bottom53 top53 p)
    (hc : ∀ i,Complex.normSq (c (bottom53 i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (top53 i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ SixQubit.Orbit53.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit53.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p (Sum.inl 5)=1/12 ∧ p (Sum.inl 4)=1/12 ∧ p (Sum.inl 0)=1/6 := by
  obtain ⟨hp0,hp1⟩ := MainTheory.OrderSixMoment53.probabilities p H
  have hc' : ∀ i,Complex.normSq (c (bottom53 i))=MainTheory.OrderSixMoment53.pattern (p (Sum.inl 5)) (p (Sum.inl 4)) (p (Sum.inl 0)) i := by
    intro i
    exact (hc i).trans (congrFun hp0 i)
  have hd' : ∀ i,Complex.normSq (d (top53 i))=MainTheory.OrderSixMoment53.pattern (p (Sum.inl 5)) (p (Sum.inl 4)) (p (Sum.inl 0)) i := by
    intro i
    exact (hd i).trans (congrFun hp1 i)
  exact MainTheory.OrderSixMomentPinning.parameters53 _ _ _

    (MainTheory.OrderSixWalshMagnitudes.orbit53X1 c d _ hc' hd' hs0 hs1 hkl)

    (MainTheory.OrderSixWalshMagnitudes.orbit53X2 c d _ hc' hd' hs0 hs1 hkl)

    (MainTheory.OrderSixWalshMagnitudes.orbit53X3 c d _ hc' hd' hs0 hs1 hkl)


theorem orbit54 (c d : SS.State 6 ℂ) (p : Sum (Fin 9) (Fin 9) → ℝ)
    (H : Feasible bottom54 top54 p)
    (hc : ∀ i,Complex.normSq (c (bottom54 i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (top54 i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ SixQubit.Orbit54.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit54.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p (Sum.inl 0)=5/36 ∧ p (Sum.inl 5)=5/36 := by
  obtain ⟨hp0,hp1⟩ := MainTheory.OrderSixMoment54.probabilities p H
  have hc' : ∀ i,Complex.normSq (c (bottom54 i))=MainTheory.OrderSixMoment54.pattern (p (Sum.inl 5)) (p (Sum.inl 0)) i := by
    intro i
    exact (hc i).trans (congrFun hp0 i)
  have hd' : ∀ i,Complex.normSq (d (top54 i))=MainTheory.OrderSixMoment54.pattern (p (Sum.inl 5)) (p (Sum.inl 0)) i := by
    intro i
    exact (hd i).trans (congrFun hp1 i)
  exact MainTheory.OrderSixMomentPinning.parameters54 _ _

    (MainTheory.OrderSixWalshMagnitudes.orbit54X1 c d _ hc' hd' hs0 hs1 hkl)

    (MainTheory.OrderSixWalshMagnitudes.orbit54X2 c d _ hc' hd' hs0 hs1 hkl)


theorem orbit56 (c d : SS.State 6 ℂ) (p : Sum (Fin 10) (Fin 10) → ℝ)
    (H : Feasible bottom56 top56 p)
    (hc : ∀ i,Complex.normSq (c (bottom56 i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (top56 i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ SixQubit.Orbit56.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit56.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p (Sum.inl 0)=1/12 := by
  obtain ⟨hp0,hp1⟩ := MainTheory.OrderSixMoment56.probabilities p H
  have hc' : ∀ i,Complex.normSq (c (bottom56 i))=MainTheory.OrderSixMoment56.pattern (p (Sum.inl 3)) (p (Sum.inl 2)) (p (Sum.inl 0)) i := by
    intro i
    exact (hc i).trans (congrFun hp0 i)
  have hd' : ∀ i,Complex.normSq (d (top56 i))=MainTheory.OrderSixMoment56.pattern (p (Sum.inl 3)) (p (Sum.inl 2)) (p (Sum.inl 0)) i := by
    intro i
    exact (hd i).trans (congrFun hp1 i)
  exact MainTheory.OrderSixMomentPinning.parameter56 _ _ _

    (MainTheory.OrderSixWalshMagnitudes.orbit56X1 c d _ hc' hd' hs0 hs1 hkl)


end MainTheory.OrderSixForcedParameters
