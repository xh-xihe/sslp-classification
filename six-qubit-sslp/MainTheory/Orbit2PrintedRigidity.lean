import MainTheory.Orbit2FullGramMatrix
import MainTheory.Orbit2GenericRigidity

/-! The SI proof of rigidity uses the very printed Q, including zero coefficient strata. -/

namespace MainTheory.Orbit2PrintedRigidity

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.Quartic MainTheory.Orbit2PrintedQuartic
  MainTheory.Orbit2PrintedJContractions MainTheory.Orbit2PrintedCContractions
  MainTheory.Orbit2GenericRigidity
open scoped BigOperators

set_option maxHeartbeats 8000000

theorem incidence_nonzero : ∀ k site ax u,
    incidence k site ax u=true → ax≠0 := by decide +kernel

theorem J_zero (t : Fin 32 → ℂ)
    (hR : ∀ site ax,ax≠0 →
      Defects.compressionDefect (expansion basis t) (operator (single site ax))=0)
    (k : Fin 5) : J t k=0 := by
  unfold J
  apply Finset.sum_eq_zero
  intro site _
  apply Finset.sum_eq_zero
  intro ax _
  apply Finset.sum_eq_zero
  intro u _
  by_cases hi : incidence k site ax u=true
  · have ha := incidence_nonzero k site ax u hi
    simp [hi,entry,hR site ax ha,tau]
  · simp [hi]

theorem f13_zero (t : Fin 32 → ℂ) (h : Label 4 → Prop) [DecidablePred h]
    (hh : ∀ p,h p → Forbidden p)
    (hf : ∀ p,Forbidden p → Defects.correlation (expansion basis t) (operator p)=0) :
    f13 t h=0 := by
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : h p
  · simp [hp,hf p (hh p hp)]
  · simp [hp]

theorem f33_zero (t : Fin 32 → ℂ) (h : Label 4 → Prop) [DecidablePred h]
    (hh : ∀ p,h p → Forbidden p)
    (hf : ∀ p,Forbidden p → Defects.correlation (expansion basis t) (operator p)=0) :
    f33 t h=0 := by
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : h p
  · simp [hp,hf p (hh p hp)]
  · simp [hp]

theorem constrained_Q (t : Fin 32 → ℂ)
    (hF : Defects.projectionDefect (expansion basis t)=0)
    (hR : ∀ site ax,ax≠0 →
      Defects.compressionDefect (expansion basis t) (operator (single site ax))=0)
    (hf : ∀ p,Forbidden p → Defects.correlation (expansion basis t) (operator p)=0) :
    Q t= -targetSquares t := by
  have h4 : ∀ p,F4 p → Forbidden p := by intro p hp; exact Or.inl hp
  have h3 : ∀ p,D3 p → Forbidden p := by intro p hp; exact Or.inr ⟨hp.2,Or.inl hp.1⟩
  have h2 : ∀ p,D2 p → Forbidden p := by intro p hp; exact Or.inr ⟨hp.2,Or.inr hp.1⟩
  simp [Q,J_zero t hR,f13_zero t F4 h4 hf,f33_zero t F4 h4 hf,
    f13_zero t D3 h3 hf,f33_zero t D2 h2 hf,g,hF,tau]

theorem printed_inequality (t : Fin 32 → ℂ)
    (hF : Defects.projectionDefect (expansion basis t)=0)
    (hR : ∀ site ax,ax≠0 →
      Defects.compressionDefect (expansion basis t) (operator (single site ax))=0)
    (hf : ∀ p,Forbidden p → Defects.correlation (expansion basis t) (operator p)=0) :
    (1/3 : ℝ)*(∑ r : Fin 528,if MainTheory.Orbit2RemainingCoordinates.Remaining r then
      Complex.normSq (t (monomials r).1*t (monomials r).2) else 0)≤ -targetSquares t := by
  rw [← constrained_Q t hF hR hf]
  exact MainTheory.Orbit2PrintedQuartic.coercivity t

end

end MainTheory.Orbit2PrintedRigidity
