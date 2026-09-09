import MainTheory.OrderSeven58ForcedPoint
import MainTheory.OrderSeven58PhaseFlips
import MainTheory.OrderSeven58PhaseAlgebra

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.OrderSeven58LiteralNoGo

open MainTheory.OrderSevenSupportDisplays MainTheory.OrderSeven58Walsh
open MainTheory.OrderSevenWalshMatrix MainTheory.OrderSeven58PhaseFlips
open MainTheory.OrderSevenMoment58 MainTheory.MomentPolytope
open MainTheory.ComplementPhaseRatios MainTheory.OrderSeven58PhaseAlgebra
open SixQubit.Orbit58 (S0 S1)

theorem no_go (c d : SS.State 6 ℂ) (p : Sum (Fin 9) (Fin 9) → ℝ)
    (H : Feasible bottom58 top58 p)
    (hc : ∀ i,Complex.normSq (c (bottom58 i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (top58 i))=p (Sum.inr i))
    (hs0 : ∀ x,x ∉ S0 → c x=0) (hs1 : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  let C : Fin 9 → ℂ := fun i => c (bottom58 i)
  let D : Fin 9 → ℂ := fun i => d (top58 i)
  let r : Fin 9 → ℂ := fun i => rho (C i) (D i)
  obtain ⟨hp0,hp1⟩ := probabilities p H
  obtain ⟨hs,ht⟩ := MainTheory.OrderSeven58ForcedPoint.forced_parameters c d p H hc hd hs0 hs1 hkl
  have hC : ∀ i,C i ≠ 0 := by
    intro i hz
    have hn := hc i
    change Complex.normSq (C i)=p (Sum.inl i) at hn
    rw [hz,congrFun hp0 i,hs,ht] at hn
    have hpos := MainTheory.OrderSeven58MomentPoint.forced_positive i
    norm_num at hn
    linarith
  have hr : r 0 ≠ 0 := by
    have hn : ‖r 0‖=1 := unit_norm (C 0) (D 0) (hC 0) (by
      change Complex.normSq (c (bottom58 0))=Complex.normSq (d (top58 0))
      rw [hc,hd]
      exact equal_probabilities p H 0)
    intro hzero
    simp [hzero] at hn
  have h1 := relations _ (matrix1 c d hs0 hs1 hkl)
  have h2 := relations _ (matrix2 c d hs0 hs1 hkl)
  change star (C 0)*D 8=star (C 8)*D 0 ∧
    star (C 4)*D 6=star (C 6)*D 4 ∧
    star (C 4)*D 6= -(star (C 0)*D 8) at h1
  change star (C 0)*D 7=star (C 7)*D 0 ∧
    star (C 3)*D 6=star (C 6)*D 3 ∧
    star (C 3)*D 6= -(star (C 0)*D 7) at h2
  have h08 : r 8=r 0 := symmetric _ _ _ _ (hC 0) (hC 8) (sub_eq_zero.mpr h1.1)
  have h46 : r 6=r 4 := symmetric _ _ _ _ (hC 4) (hC 6) (sub_eq_zero.mpr h1.2.1)
  have h07 : r 7=r 0 := symmetric _ _ _ _ (hC 0) (hC 7) (sub_eq_zero.mpr h2.1)
  have h36 : r 6=r 3 := symmetric _ _ _ _ (hC 3) (hC 6) (sub_eq_zero.mpr h2.2.1)
  have h35 : r 5= -r 3 := antisymmetric _ _ _ _ (hC 3) (hC 5) (edge35 c d hs0 hs1 hkl)
  have h57 : r 7= -r 5 := antisymmetric _ _ _ _ (hC 5) (hC 7) (edge57 c d hs0 hs1 hkl)
  obtain ⟨h03,h04,h06,h07',h08'⟩ := common r h08 h46 h07 h36 h35 h57
  have hz (i j : Fin 9) (hj : r j=r 0) :
      star (C i)*D j=r 0*star (C i*C j) := by
    change MainTheory.ComplementPhaseRatios.z (C i) (D j)=_
    rw [factor _ _ _ (hC j)]
    change r j*star (C i*C j)=_
    rw [hj]
  have hp46 : C 4*C 6= -(C 0*C 8) := by
    apply product_equation (r 0) _ _ _ _ hr
    simpa only [hz 4 6 h06.symm,hz 0 8 h08'.symm] using h1.2.2
  have hp36 : C 3*C 6= -(C 0*C 7) := by
    apply product_equation (r 0) _ _ _ _ hr
    simpa only [hz 3 6 h06.symm,hz 0 7 h07'.symm] using h2.2.2
  have hf : C 3*C 8+C 4*C 7=0 := by
    apply fatal_equation (r 0) _ _ _ _ hr
    have he := four45 c d hs0 hs1 hkl
    change star (C 3)*D 8+star (C 4)*D 7+star (C 7)*D 4+star (C 8)*D 3=0 at he
    simpa only [hz 3 8 h08'.symm,hz 4 7 h07'.symm,hz 7 4 h04.symm,hz 8 3 h03.symm] using he
  rw [contradiction_value C (hC 0) hp46 hp36] at hf
  exact value_nonzero C (hC 0) (hC 3) (hC 4) (hC 6) hf

end MainTheory.OrderSeven58LiteralNoGo
