import MainTheory.OrderSixForcedParameters
import MainTheory.OrderSixPhaseRows
import MainTheory.NegativePhaseEquations

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace MainTheory.OrderSix53LiteralNoGo

open MainTheory.OrderSixSupportDisplays MainTheory.OrderSixWalshDisplays
open MainTheory.OrderSevenWalshMatrix MainTheory.MomentPolytope
open MainTheory.OrderSixMoment53 MainTheory.ComplementPhaseRatios
open MainTheory.OrderSixPhaseRows

theorem contradiction_value (C : Fin 10 → ℂ) (h0 : C 0 ≠ 0)
    (h1 : C 3*C 5= -(C 0*C 8)) (h2 : C 3*C 4= -(C 0*C 7)) :
    C 4*C 8+C 5*C 7= -(2*C 3*C 4*C 5/C 0) := by
  field_simp [h0]
  linear_combination C 4*h1+C 5*h2

theorem no_go (c d : SS.State 6 ℂ) (p : Sum (Fin 10) (Fin 10) → ℝ)
    (H : Feasible bottom53 top53 p)
    (hc : ∀ i,Complex.normSq (c (bottom53 i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (top53 i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ SixQubit.Orbit53.S0 → c x=0)
    (hs1 : ∀ x,x ∉ SixQubit.Orbit53.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  let C : Fin 10 → ℂ := fun i => c (bottom53 i)
  let D : Fin 10 → ℂ := fun i => d (top53 i)
  let r : Fin 10 → ℂ := fun i => rho (C i) (D i)
  obtain ⟨hp0,_⟩ := probabilities p H
  obtain ⟨hr',hs,ht⟩ := MainTheory.OrderSixForcedParameters.orbit53 c d p H hc hd hs0 hs1 hkl
  have hC : ∀ i,C i ≠ 0 := by
    intro i hz
    have hn := hc i
    change Complex.normSq (C i)=p (Sum.inl i) at hn
    rw [hz,congrFun hp0 i,hr',hs,ht] at hn
    have hpos := MainTheory.OrderSixMomentPinning.positive53 i
    norm_num at hn
    linarith
  have hr : r 0 ≠ 0 := by
    have hn : ‖r 0‖=1 := unit_norm (C 0) (D 0) (hC 0) (by
      change Complex.normSq (c (bottom53 0))=Complex.normSq (d (top53 0))
      rw [hc,hd]
      exact equal_probabilities p H 0)
    intro hz
    simp [hz] at hn
  have h1 := relations _ (Orbit53X1.matrix_equation c d hs0 hs1 hkl)
  have h2 := relations _ (Orbit53X2.matrix_equation c d hs0 hs1 hkl)
  have h3 := relations _ (Orbit53X3.matrix_equation c d hs0 hs1 hkl)
  change star (C 9)*D 0=star (C 0)*D 9 ∧ star (C 6)*D 3=star (C 3)*D 6 ∧
    star (C 6)*D 3= -(star (C 9)*D 0) at h1
  change star (C 8)*D 0=star (C 0)*D 8 ∧ star (C 5)*D 3=star (C 3)*D 5 ∧
    star (C 5)*D 3= -(star (C 8)*D 0) at h2
  change star (C 7)*D 0=star (C 0)*D 7 ∧ star (C 4)*D 3=star (C 3)*D 4 ∧
    star (C 4)*D 3= -(star (C 7)*D 0) at h3
  have h09 : r 0=r 9 := symmetric _ _ _ _ (hC 9) (hC 0) (sub_eq_zero.mpr h1.1)
  have h36 : r 3=r 6 := symmetric _ _ _ _ (hC 6) (hC 3) (sub_eq_zero.mpr h1.2.1)
  have h08 : r 0=r 8 := symmetric _ _ _ _ (hC 8) (hC 0) (sub_eq_zero.mpr h2.1)
  have h35 : r 3=r 5 := symmetric _ _ _ _ (hC 5) (hC 3) (sub_eq_zero.mpr h2.2.1)
  have h07 : r 0=r 7 := symmetric _ _ _ _ (hC 7) (hC 0) (sub_eq_zero.mpr h3.1)
  have h34 : r 3=r 4 := symmetric _ _ _ _ (hC 4) (hC 3) (sub_eq_zero.mpr h3.2.1)
  have ha : r 0= -r 2 := antisymmetric _ _ _ _ (hC 2) (hC 0) (Orbit53_pair46a.equation c d hs0 hs1 hkl)
  have hb : r 2= -r 3 := antisymmetric _ _ _ _ (hC 3) (hC 2) (Orbit53_pair56b.equation c d hs0 hs1 hkl)
  have h03 : r 0=r 3 := by linear_combination ha-hb
  have hz (i j : Fin 10) (hj : r j=r 0) : star (C i)*D j=r 0*star (C i*C j) := by
    change MainTheory.ComplementPhaseRatios.z (C i) (D j)=_
    rw [factor _ _ _ (hC j)]
    change r j*star (C i*C j)=_
    rw [hj]
  have hp1 : C 5*C 3= -(C 8*C 0) := by
    apply MainTheory.OrderSeven58PhaseAlgebra.product_equation (r 0) _ _ _ _ hr
    simpa only [hz 5 3 h03.symm,hz 8 0 rfl] using h2.2.2
  have hp2 : C 4*C 3= -(C 7*C 0) := by
    apply MainTheory.OrderSeven58PhaseAlgebra.product_equation (r 0) _ _ _ _ hr
    simpa only [hz 4 3 h03.symm,hz 7 0 rfl] using h3.2.2
  have hf : C 8*C 4+C 7*C 5=0 := by
    apply MainTheory.OrderSeven58PhaseAlgebra.fatal_equation (r 0) _ _ _ _ hr
    have he := Orbit53_four16.equation c d hs0 hs1 hkl
    change star (C 8)*D 4+star (C 7)*D 5+star (C 5)*D 7+star (C 4)*D 8=0 at he
    simpa only [hz 8 4 (h34.symm.trans h03.symm),hz 7 5 (h35.symm.trans h03.symm),
      hz 5 7 h07.symm,hz 4 8 h08.symm] using he
  have hzero : 2*C 3*C 4*C 5=0 := by
    linear_combination C 4*hp1+C 5*hp2-C 0*hf
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (hC 3)) (hC 4)) (hC 5) hzero

end MainTheory.OrderSix53LiteralNoGo
