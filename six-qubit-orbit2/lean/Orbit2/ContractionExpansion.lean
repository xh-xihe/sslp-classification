import Orbit2.FinalReduction
import Orbit2.PauliConjugation

namespace Orbit2.Quartic
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable def orderedPolynomial (k : Fin 32 → Fin 32 → Fin 32 → Fin 32 → ℤ)
    (t : Fin 32 → ℂ) : ℂ :=
  ∑ y, ∑ v, ∑ x, ∑ u, star (t u) * t x * star (t v) * t y * (k u v x y : ℂ)

noncomputable def threePart (t : Fin 32 → ℂ) : Defects.ActiveMatrix :=
  expansion basis (fun u => if isThree u then t u else 0)

theorem gaussian_cast_of_im_zero (a : GaussianInt) (h : a.im=0) :
    (a : ℂ) = (a.re : ℂ) := by
  rw [GaussianInt.toComplex_def,h]
  simp

theorem four_trace_cast (u v x y : Fin 32) :
    (wordTrace [basis u,basis x,basis v,basis y] : ℂ) =
      ((wordTrace [basis u,basis x,basis v,basis y]).re : ℂ) :=
  gaussian_cast_of_im_zero _ (wordTrace_four_real u x v y)

theorem basis_tau_pair (u v : Fin 32) :
    tau (operator (basis u) * operator (basis v)) = if u=v then 1 else 0 := by
  rw [tau_operator_pair]
  simp only [pauliBasis_injective.eq_iff]

theorem tau_expansion_basis_pair (a b : Fin 32 → ℂ) :
    tau (expansion basis a * expansion basis b)=∑ u, a u * b u := by
  unfold expansion
  simp only [Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    tau_sum,tau_smul,basis_tau_pair]
  simp [mul_ite,mul_comm]

theorem expansion_normMass (t : Fin 32 → ℂ) :
    Defects.normMass (expansion basis t)=∑ v, t v * star (t v) := by
  unfold Defects.normMass
  rw [expansion_conjTranspose,tau_expansion_basis_pair]

theorem three_pair_trace (t : Fin 32 → ℂ) :
    tau ((threePart t).conjTranspose * expansion basis t)=
      ∑ u, if isThree u then star (t u) * t u else 0 := by
  unfold threePart
  rw [expansion_conjTranspose,tau_expansion_basis_pair]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> simp

theorem three_four_trace (t : Fin 32 → ℂ) :
    tau ((threePart t).conjTranspose * expansion basis t *
      (expansion basis t).conjTranspose * expansion basis t) =
      ∑ y, ∑ v, ∑ x, ∑ u, if isThree u then
        star (t u) * t x * star (t v) * t y *
          ((wordTrace [basis u,basis x,basis v,basis y]).re : ℂ) else 0 := by
  unfold threePart
  rw [expansion_conjTranspose,expansion_conjTranspose,tau_expansion_four]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  rw [four_trace_cast]
  split_ifs <;> simp

theorem projection_delta_sum (t : Fin 32 → ℂ) :
    (∑ y, ∑ v, ∑ x, ∑ u : Fin 32, if u=x ∧ v=y then
      (if isThree u then 2 * (star (t u) * t x * star (t v) * t y) else 0) else 0) =
      2 * (∑ v, t v * star (t v)) * (∑ u, if isThree u then star (t u) * t u else 0) := by
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  conv_rhs =>
    rw [mul_assoc,Finset.sum_mul]
    simp only [Finset.mul_sum,mul_ite,mul_zero]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> ring

/-- The projection-defect contraction expands to the actual integer gCoeff.
No matrix-to-coefficient equality is assumed. -/
theorem projection_contraction_expansion (t : Fin 32 → ℂ) :
    tau ((threePart t).conjTranspose * Defects.projectionDefect (expansion basis t)) =
      orderedPolynomial gCoeff t := by
  have hc (u v x y : Fin 32) :
      star (t u) * t x * star (t v) * t y * (gCoeff u v x y : ℂ) =
      (if isThree u then star (t u) * t x * star (t v) * t y *
        ((wordTrace [basis u,basis x,basis v,basis y]).re : ℂ) else 0) -
      (if u=x ∧ v=y then (if isThree u then 2 * (star (t u) * t x * star (t v) * t y) else 0) else 0) := by
    unfold gCoeff
    split_ifs <;> simp_all <;> ring
  have hp : orderedPolynomial gCoeff t =
      tau ((threePart t).conjTranspose * expansion basis t *
        (expansion basis t).conjTranspose * expansion basis t) -
      2 * Defects.normMass (expansion basis t) * tau ((threePart t).conjTranspose * expansion basis t) := by
    unfold orderedPolynomial
    calc
      _ = ∑ y, ∑ v, ∑ x, ∑ u : Fin 32,
        ((if isThree u then star (t u) * t x * star (t v) * t y *
          ((wordTrace [basis u,basis x,basis v,basis y]).re : ℂ) else 0) -
        (if u=x ∧ v=y then (if isThree u then 2 * (star (t u) * t x * star (t v) * t y) else 0) else 0)) := by
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro v _
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro u _
          exact hc u v x y
      _ = _ := by
        simp only [Finset.sum_sub_distrib]
        rw [← three_four_trace,projection_delta_sum,expansion_normMass,three_pair_trace]
  rw [hp]
  unfold Defects.projectionDefect
  rw [Matrix.mul_sub,Matrix.mul_smul]
  have hs (A B : Defects.ActiveMatrix) : tau (A-B)=tau A-tau B := by
    simp [tau,Matrix.trace_sub,sub_div]
  rw [hs,tau_smul]
  simp only [Matrix.mul_assoc]

end Orbit2.Quartic
