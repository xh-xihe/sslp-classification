import MainTheory.OrderSixForcedParameters
import MainTheory.NegativePhaseEquations

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace MainTheory.OrderSix54LiteralNoGo

open MainTheory.OrderSixSupportDisplays MainTheory.OrderSixWalshDisplays
open MainTheory.OrderSevenWalshMatrix MainTheory.MomentPolytope
open MainTheory.OrderSixMoment54 MainTheory.ComplementPhaseRatios

theorem no_go (c d : SS.State 6 ℂ) (p : Sum (Fin 9) (Fin 9) → ℝ)
    (H : Feasible bottom54 top54 p)
    (hc : ∀ i,Complex.normSq (c (bottom54 i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (top54 i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ SixQubit.Orbit54.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit54.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  let C : Fin 9 → ℂ := fun i => c (bottom54 i)
  let D : Fin 9 → ℂ := fun i => d (top54 i)
  let r : Fin 9 → ℂ := fun i => rho (C i) (D i)
  obtain ⟨hp0,_⟩ := probabilities p H
  obtain ⟨ht,hs⟩ := MainTheory.OrderSixForcedParameters.orbit54 c d p H hc hd hs0 hs1 hkl
  have hC : ∀ i,C i ≠ 0 := by
    intro i hz
    have hn := hc i
    change Complex.normSq (C i)=p (Sum.inl i) at hn
    rw [hz,congrFun hp0 i,hs,ht] at hn
    have hpos := MainTheory.OrderSixMomentPinning.positive54 i
    norm_num at hn
    linarith
  have hr : r 0 ≠ 0 := by
    have hn : ‖r 0‖=1 := unit_norm (C 0) (D 0) (hC 0) (by
      change Complex.normSq (c (bottom54 0))=Complex.normSq (d (top54 0))
      rw [hc,hd]
      exact equal_probabilities p H 0)
    intro hz
    simp [hz] at hn
  have h1 := relations _ (Orbit54X1.matrix_equation c d hs0 hs1 hkl)
  have h2 := relations _ (Orbit54X2.matrix_equation c d hs0 hs1 hkl)
  have h6 := relations _ (Orbit54X6.matrix_equation c d hs0 hs1 hkl)
  change star (C 8)*D 0=star (C 0)*D 8 ∧ star (C 6)*D 4=star (C 4)*D 6 ∧
    star (C 6)*D 4= -(star (C 8)*D 0) at h1
  change star (C 7)*D 0=star (C 0)*D 7 ∧ star (C 5)*D 4=star (C 4)*D 5 ∧
    star (C 5)*D 4= -(star (C 7)*D 0) at h2
  change star (C 8)*D 5=star (C 5)*D 8 ∧ star (C 7)*D 6=star (C 6)*D 7 ∧
    star (C 7)*D 6= -(star (C 8)*D 5) at h6
  have h08 : r 0=r 8 := symmetric _ _ _ _ (hC 8) (hC 0) (sub_eq_zero.mpr h1.1)
  have h46 : r 4=r 6 := symmetric _ _ _ _ (hC 6) (hC 4) (sub_eq_zero.mpr h1.2.1)
  have h07 : r 0=r 7 := symmetric _ _ _ _ (hC 7) (hC 0) (sub_eq_zero.mpr h2.1)
  have h45 : r 4=r 5 := symmetric _ _ _ _ (hC 5) (hC 4) (sub_eq_zero.mpr h2.2.1)
  have h58 : r 5=r 8 := symmetric _ _ _ _ (hC 8) (hC 5) (sub_eq_zero.mpr h6.1)
  have h40 : r 4=r 0 := h45.trans (h58.trans h08.symm)
  have h50 : r 5=r 0 := h58.trans h08.symm
  have h60 : r 6=r 0 := h46.symm.trans h40
  have hz (i j : Fin 9) (hj : r j=r 0) : star (C i)*D j=r 0*star (C i*C j) := by
    change MainTheory.ComplementPhaseRatios.z (C i) (D j)=_
    rw [factor _ _ _ (hC j)]
    change r j*star (C i*C j)=_
    rw [hj]
  have hp1 : C 6*C 4= -(C 8*C 0) := by
    apply MainTheory.OrderSeven58PhaseAlgebra.product_equation (r 0) _ _ _ _ hr
    simpa only [hz 6 4 h40,hz 8 0 rfl] using h1.2.2
  have hp2 : C 5*C 4= -(C 7*C 0) := by
    apply MainTheory.OrderSeven58PhaseAlgebra.product_equation (r 0) _ _ _ _ hr
    simpa only [hz 5 4 h40,hz 7 0 rfl] using h2.2.2
  have hp3 : C 7*C 6= -(C 8*C 5) := by
    apply MainTheory.OrderSeven58PhaseAlgebra.product_equation (r 0) _ _ _ _ hr
    simpa only [hz 7 6 h60,hz 8 5 h50] using h6.2.2
  apply MainTheory.NegativePhaseEquations.odd_binomials (C 6) (C 8) (C 5) (C 7) (C 0) (C 4)
    (hC 6) (hC 8) (hC 7) (hC 4)
  · linear_combination hp1
  · linear_combination hp2
  · linear_combination hp3

end MainTheory.OrderSix54LiteralNoGo
