import MainTheory.OrderSixPhaseRows
import MainTheory.OrderSixWalshDisplays
import MainTheory.OrderSixMoment56
import MainTheory.ComplementPhaseRatios

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderSix56CommonPhase

open MainTheory.OrderSixSupportDisplays MainTheory.OrderSixPhaseRows
open MainTheory.OrderSixWalshDisplays MainTheory.OrderSevenWalshMatrix
open MainTheory.OrderSixMoment56 MainTheory.MomentPolytope MainTheory.ComplementPhaseRatios
open SixQubit.Orbit56 (S0 S1)

noncomputable def r (c d : SS.State 6 ℂ) (i : Fin 10) := rho (c (bottom56 i)) (d (top56 i))

theorem active_pair (c : SS.State 6 ℂ) (p : Sum (Fin 10) (Fin 10) → ℝ)
    (H : Feasible bottom56 top56 p)
    (hc : ∀ i,Complex.normSq (c (bottom56 i))=p (Sum.inl i)) :
    c (bottom56 2) ≠ 0 ∨ c (bottom56 5) ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨h2,h5⟩ := h
  have hp := (probabilities p H).1
  have hn2 := (hc 2).trans (congrFun hp 2)
  have hn5 := (hc 5).trans (congrFun hp 5)
  change Complex.normSq (c (bottom56 2))=p (Sum.inl 2) at hn2
  change Complex.normSq (c (bottom56 5))=1/6-p (Sum.inl 2) at hn5
  rw [h2] at hn2
  rw [h5] at hn5
  norm_num at hn2 hn5
  linarith

theorem first_relations (c d : SS.State 6 ℂ)
    (hn : ∀ i : Fin 10,i ∈ ({0,1,8,9} : Finset (Fin 10)) → c (bottom56 i) ≠ 0)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : r c d 0=r c d 9 ∧ r c d 1=r c d 8 := by
  have h := relations _ (Orbit56X1.matrix_equation c d hc hd hkl)
  change star (c (bottom56 9))*d (top56 0)=star (c (bottom56 0))*d (top56 9) ∧
    star (c (bottom56 8))*d (top56 1)=star (c (bottom56 1))*d (top56 8) ∧ _ at h
  exact ⟨symmetric _ _ _ _ (hn 9 (by decide)) (hn 0 (by decide)) (sub_eq_zero.mpr h.1),
    symmetric _ _ _ _ (hn 8 (by decide)) (hn 1 (by decide)) (sub_eq_zero.mpr h.2.1)⟩

theorem anchor_agreement (c d : SS.State 6 ℂ)
    (h1 : c (bottom56 1) ≠ 0) (h9 : c (bottom56 9) ≠ 0)
    (hp : c (bottom56 2) ≠ 0 ∨ c (bottom56 5) ≠ 0)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : r c d 1=r c d 9 := by
  rcases hp with h2 | h5
  · have ha : r c d 2= -r c d 1 := antisymmetric _ _ _ _ h1 h2 (Orbit56_edge1_2.equation c d hc hd hkl)
    have hb : r c d 9= -r c d 2 := antisymmetric _ _ _ _ h2 h9 (Orbit56_edge2_9.equation c d hc hd hkl)
    linear_combination ha-hb
  · have ha : r c d 5= -r c d 1 := antisymmetric _ _ _ _ h1 h5 (Orbit56_edge1_5.equation c d hc hd hkl)
    have hb : r c d 9= -r c d 5 := antisymmetric _ _ _ _ h5 h9 (Orbit56_edge5_9.equation c d hc hd hkl)
    linear_combination ha-hb

theorem common (c d : SS.State 6 ℂ)
    (hn : ∀ i : Fin 10,i ∈ ({0,1,8,9} : Finset (Fin 10)) → c (bottom56 i) ≠ 0)
    (hp : c (bottom56 2) ≠ 0 ∨ c (bottom56 5) ≠ 0)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    r c d 0=r c d 1 ∧ r c d 0=r c d 8 ∧ r c d 0=r c d 9 := by
  obtain ⟨h09,h18⟩ := first_relations c d hn hc hd hkl
  have h19 := anchor_agreement c d (hn 1 (by decide)) (hn 9 (by decide)) hp hc hd hkl
  exact ⟨h09.trans h19.symm,h09.trans (h19.symm.trans h18),h09⟩

end MainTheory.OrderSix56CommonPhase
