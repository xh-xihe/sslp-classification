import Orbit2.TensorPauli

namespace Orbit2.TensorPauli
open scoped BigOperators

theorem localG_completeness : ∀ x y z w : Fin 2,
    (∑ a : Fin 4, localG a x y * localG a z w) =
      if x=w ∧ y=z then 2 else 0 := by decide +kernel

theorem localC_completeness (x y z w : Fin 2) :
    (∑ a : Fin 4, localC a x y * localC a z w) =
      if x=w ∧ y=z then 2 else 0 := by
  have h := congrArg GaussianInt.toComplex (localG_completeness x y z w)
  have he : (∑ a : Fin 4, localC a x y * localC a z w) =
      ((if x=w ∧ y=z then 2 else 0 : GaussianInt) : ℂ) := by
    simpa only [localC,Matrix.map_apply,map_sum,GaussianInt.toComplex_mul] using h
  rw [he]
  split_ifs <;> norm_num [GaussianInt.toComplex_def]

/-- Completeness of the tensor-Pauli operator family, proved by factoring
the sum into its local four-element identities. -/
theorem operator_completeness {n : ℕ} (x y z w : Fin n → Fin 2) :
    (∑ p : Label n, operator p x y * operator p z w) =
      if x=w ∧ y=z then (2 : ℂ)^n else 0 := by
  simp only [operator,tensor,← Finset.prod_mul_distrib]
  have he := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 4)))
    (fun i a => localC a (x i) (y i) * localC a (z i) (w i))
  have he' : (∑ p : Label n, ∏ i, localC (p i) (x i) (y i) * localC (p i) (z i) (w i)) =
      ∏ i, ∑ a : Fin 4, localC a (x i) (y i) * localC a (z i) (w i) := by
    simpa using he.symm
  rw [he']
  simp_rw [localC_completeness]
  by_cases h : x=w ∧ y=z
  · rcases h with ⟨rfl,rfl⟩
    simp
  · simp only [h,if_false]
    have hi : ∃ i, ¬ (x i=w i ∧ y i=z i) := by
      by_contra hn
      push_neg at hn
      exact h ⟨funext fun i => (hn i).1,funext fun i => (hn i).2⟩
    obtain ⟨i,hi⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Every complex matrix has the actual normalized Pauli-trace expansion.
This proves spanning; it is not an assumption about code projectors. -/
theorem matrix_reconstruction {n : ℕ}
    (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    M = ∑ p : Label n, tau (operator p * M) • operator p := by
  ext x y
  symm
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,tau,Matrix.trace,Matrix.diag,
    Matrix.mul_apply]
  calc
    _ = (∑ z, ∑ w, M w z * ∑ p : Label n, operator p z w * operator p x y)/(2 : ℂ)^n := by
      simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
      rw [Finset.sum_comm (γ := Label n)]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = M x y := by
      simp_rw [operator_completeness]
      simp [mul_ite,ite_and,Finset.sum_ite_eq,Finset.sum_ite_eq',mul_comm]

end Orbit2.TensorPauli
