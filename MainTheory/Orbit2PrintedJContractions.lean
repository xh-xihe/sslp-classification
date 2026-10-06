import MainTheory.Orbit2QuarticContractions

/-! Exact incidence conditions and weights of the five printed J sums. -/

namespace MainTheory.Orbit2PrintedJContractions

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.Quartic
open scoped BigOperators

set_option maxHeartbeats 8000000

def incidence (k : Fin 5) (site ax : Fin 4) (u : Fin 32) : Bool :=
  let p := basis u site
  ![decide (ax=1 ∨ ax=2) && isThree u && decide (p=3),
    decide (ax=3) && isThree u && decide (p=1 ∨ p=2),
    decide (ax=1 ∨ ax=2) && isThree u && decide ((p=1 ∨ p=2) ∧ p≠ax),
    decide (ax=1 ∨ ax=2) && !(isThree u) && decide ((p=1 ∨ p=2) ∧ p≠ax),
    decide (ax=3) && !(isThree u) && decide (p=1 ∨ p=2)] k

def weight (k : Fin 5) : ℤ := ![5,10,7,18,-18] k

def entry (t : Fin 32 → ℂ) (site ax : Fin 4) (u : Fin 32) : ℂ :=
  star (t u)*tau (operator (basis u)*operator (single site ax)*
    Defects.compressionDefect (expansion basis t) (operator (single site ax)))

def J (t : Fin 32 → ℂ) (k : Fin 5) : ℝ :=
  ∑ site,∑ ax,∑ u,if incidence k site ax u then (entry t site ax u).re else 0

theorem exact_incidence : ∀ site ax u,jWeight site ax u=
    ∑ k : Fin 5,if incidence k site ax u then weight k else 0 := by
  decide +kernel

theorem weighted_real (t : Fin 32 → ℂ) :
    (orderedPolynomial jCoeff t).re=
      (∑ k : Fin 5,(weight k : ℝ)*J t k) := by
  rw [← J_contraction_expansion]
  simp only [Complex.re_sum]
  have he (site ax : Fin 4) (u : Fin 32) :
      ((jWeight site ax u : ℂ)*star (t u)*tau (operator (basis u)*
        operator (single site ax)*Defects.compressionDefect (expansion basis t)
          (operator (single site ax)))).re=
        ∑ k : Fin 5,(weight k : ℝ)*(if incidence k site ax u then
          (entry t site ax u).re else 0) := by
    rw [exact_incidence]
    simp only [Int.cast_sum,Finset.sum_mul,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k _
    cases incidence k site ax u
    · simp
    · simp [entry,Complex.mul_re,Complex.mul_im]
      ring
  simp_rw [he]
  simp only [J,Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro site _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ax _
  rw [Finset.sum_comm]

theorem printed_J_weights (t : Fin 32 → ℂ) :
    (orderedPolynomial jCoeff t).re/12=
      (5/12 : ℝ)*J t 0+(5/6 : ℝ)*J t 1+(7/12 : ℝ)*J t 2+
        (3/2 : ℝ)*J t 3-(3/2 : ℝ)*J t 4 := by
  rw [weighted_real]
  norm_num [weight,Fin.sum_univ_succ,Fin.succ]
  change (5*J t 0+(10*J t 1+(7*J t 2+(18*J t 3+ -(18*J t 4)))))/12=_
  ring

end

end MainTheory.Orbit2PrintedJContractions
