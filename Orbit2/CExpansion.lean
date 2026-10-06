import Orbit2.JExpansion

-- Preserve upstream proofs; suppress only the recorded style linters.
set_option linter.unusedSimpArgs false

namespace Orbit2.Quartic
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def cMultiplier (p : Label 4) (v y : Fin 32) : ℤ :=
  (if pauliWeight p=3 ∧ transverseCount p=2 then -24 else 0) +
  (if pauliWeight p=4 ∧ transverseCount p=2 then
    (if isThree y != isThree v then 68 else 0) + (if isThree y && isThree v then 76 else 0) else 0) +
  (if pauliWeight p=3 ∧ transverseCount p=0 ∧ (isThree y != isThree v) then 100 else 0) +
  (if pauliWeight p=2 ∧ transverseCount p=0 ∧ (isThree y && isThree v) then 8 else 0)

noncomputable def pairKernel (p : Label 4) (x u : Fin 32) : ℂ :=
  if product (basis x) (basis u)=p then (phase (basis x) (basis u) : ℂ) else 0

noncomputable def weightedCorrelation (t : Fin 32 → ℂ)
    (m : Label 4 → Fin 32 → Fin 32 → ℤ) (p : Label 4) : ℂ :=
  ∑ v, ∑ y, t y * star (t v) * (m p v y : ℂ) * pairKernel p y v

theorem paired_kernel_sum (m : Label 4 → Fin 32 → Fin 32 → ℤ) (u v x y : Fin 32) :
    (∑ p : Label 4, (m p v y : ℂ) * pairKernel p x u * pairKernel p y v) =
      ((if product (basis x) (basis u)=product (basis y) (basis v) then
        m (product (basis x) (basis u)) v y *
          (phase (basis x) (basis u) * phase (basis y) (basis v)).re else 0 : ℤ) : ℂ) := by
  unfold pairKernel
  simp only [mul_ite,ite_mul,zero_mul,mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ,if_true]
  by_cases h : product (basis x) (basis u)=product (basis y) (basis v)
  · simp only [h,if_true,Int.cast_mul]
    have hr := gaussian_cast_of_im_zero _ (phase_product_im_zero x u y v h)
    rw [GaussianInt.toComplex_mul] at hr
    rw [← hr]
    ring
  · simp [h,eq_comm]

theorem correlation_product_expansion (t : Fin 32 → ℂ)
    (m : Label 4 → Fin 32 → Fin 32 → ℤ) :
    (∑ p : Label 4, Defects.correlation (expansion basis t) (operator p) *
      weightedCorrelation t m p) =
    orderedPolynomial (fun u v x y =>
      if product (basis x) (basis u)=product (basis y) (basis v) then
        m (product (basis x) (basis u)) v y *
          (phase (basis x) (basis u) * phase (basis y) (basis v)).re else 0) t := by
  simp only [correlation_expansion,weightedCorrelation,Finset.mul_sum,Finset.sum_mul]
  rw [sum_rotate_five,Finset.sum_comm]
  unfold orderedPolynomial
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  rw [← paired_kernel_sum m u v x y]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  unfold pairKernel
  ring

theorem c_contraction_expansion (t : Fin 32 → ℂ) :
    (∑ p : Label 4, Defects.correlation (expansion basis t) (operator p) *
      weightedCorrelation t cMultiplier p) = orderedPolynomial cCoeff t := by
  exact correlation_product_expansion t cMultiplier

end Orbit2.Quartic
