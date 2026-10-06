import MainTheory.OrderSeven58Walsh
import MainTheory.OrderSeven58MomentPoint

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderSeven58ForcedPoint

open MainTheory.OrderSeven58Walsh MainTheory.OrderSevenSupportDisplays
open MainTheory.OrderSevenWalshMatrix MainTheory.OrderSeven58MomentPoint
open MainTheory.OrderSevenMoment58 MainTheory.MomentPolytope
open SixQubit.Orbit58 (S0 S1)

theorem magnitude_relations (c d : SS.State 6 ℂ) (p : Fin 9 → ℝ)
    (hc : ∀ i,Complex.normSq (c (bottom58 i))=p i)
    (hd : ∀ i,Complex.normSq (d (top58 i))=p i)
    (h1 : W.mulVec (products1 c d)=0) (h2 : W.mulVec (products2 c d)=0) :
    p 0*p 8=p 4*p 6 ∧ p 0*p 7=p 3*p 6 := by
  have he1 := (relations _ h1).2.2
  have he2 := (relations _ h2).2.2
  change star (c (bottom58 4))*d (top58 6)= -(star (c (bottom58 0))*d (top58 8)) at he1
  change star (c (bottom58 3))*d (top58 6)= -(star (c (bottom58 0))*d (top58 7)) at he2
  have hn1 := congrArg Complex.normSq he1
  have hn2 := congrArg Complex.normSq he2
  simp only [Complex.normSq_neg,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,hc,hd] at hn1 hn2
  exact ⟨hn1.symm,hn2.symm⟩

theorem forced_parameters (c d : SS.State 6 ℂ) (p : Sum (Fin 9) (Fin 9) → ℝ)
    (H : Feasible bottom58 top58 p)
    (hc : ∀ i,Complex.normSq (c (bottom58 i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (top58 i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ S0 → c x=0) (hs1 : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : p (Sum.inl 3)=3/28 ∧ p (Sum.inl 0)=1/7 := by
  obtain ⟨hp0,hp1⟩ := probabilities p H
  have hc' : ∀ i,Complex.normSq (c (bottom58 i))=
      MainTheory.OrderSevenMoment58.pattern (p (Sum.inl 3)) (p (Sum.inl 0)) i := by
    intro i
    exact (hc i).trans (congrFun hp0 i)
  have hd' : ∀ i,Complex.normSq (d (top58 i))=
      MainTheory.OrderSevenMoment58.pattern (p (Sum.inl 3)) (p (Sum.inl 0)) i := by
    intro i
    exact (hd i).trans (congrFun hp1 i)
  obtain ⟨h1,h2⟩ := magnitude_relations c d _ hc' hd'
    (matrix1 c d hs0 hs1 hkl) (matrix2 c d hs0 hs1 hkl)
  exact unique_parameters _ _ ((first_linear _ _).1 h1) ((second_linear _ _).1 h2)

end MainTheory.OrderSeven58ForcedPoint
