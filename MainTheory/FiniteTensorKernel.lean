import Mathlib

/-! # Tensor products of arbitrary finite physical subsystems -/

namespace MainTheory.FiniteTensorKernel

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] {A : S → Type*}
  [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]

set_option linter.unusedSectionVars false

def tensor (U : ∀ j, Matrix (A j) (A j) ℂ) : Matrix (∀ j, A j) (∀ j, A j) ℂ :=
  fun x y => ∏ j, U j (x j) (y j)

theorem tensor_mul (U V : ∀ j, Matrix (A j) (A j) ℂ) :
    tensor (fun j => U j * V j) = tensor U * tensor V := by
  ext x y
  simp only [tensor, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun j k => U j (x j) k * V j k (y j))

@[simp] theorem tensor_one : tensor (fun j => (1 : Matrix (A j) (A j) ℂ)) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensor]
  · rw [Matrix.one_apply_ne hxy]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.one_apply_ne hj

@[simp] theorem tensor_conjTranspose (U : ∀ j, Matrix (A j) (A j) ℂ) :
    tensor (fun j => (U j).conjTranspose) = (tensor U).conjTranspose := by
  ext x y
  simp [tensor, Matrix.conjTranspose_apply]

theorem tensor_unitary (U : ∀ j, Matrix (A j) (A j) ℂ)
    (hU : ∀ j, (U j).conjTranspose * U j = 1 ∧ U j * (U j).conjTranspose = 1) :
    (tensor U).conjTranspose * tensor U = 1 ∧ tensor U * (tensor U).conjTranspose = 1 := by
  constructor
  · rw [← tensor_conjTranspose, ← tensor_mul]
    simpa only [funext (fun j => (hU j).1)] using (tensor_one (A := A))
  · rw [← tensor_conjTranspose, ← tensor_mul]
    simpa only [funext (fun j => (hU j).2)] using (tensor_one (A := A))

theorem tensor_diagonal (u : ∀ j, A j → ℂ) :
    tensor (fun j => Matrix.diagonal (u j)) = Matrix.diagonal (fun x => ∏ j, u j (x j)) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensor]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.diagonal_apply_ne _ hj

def localKernel (j : S) (M : Matrix (A j) (A j) ℂ) : Matrix (∀ j, A j) (∀ j, A j) ℂ :=
  tensor (Function.update (fun k => (1 : Matrix (A k) (A k) ℂ)) j M)

theorem tensor_conjugate_local (U : ∀ j, Matrix (A j) (A j) ℂ)
    (hU : ∀ j, (U j).conjTranspose * U j = 1)
    (j : S) (M : Matrix (A j) (A j) ℂ) :
    (tensor U).conjTranspose * localKernel j M * tensor U =
      localKernel j ((U j).conjTranspose * M * U j) := by
  rw [localKernel, ← tensor_conjTranspose, ← tensor_mul, ← tensor_mul, localKernel]
  apply congrArg tensor
  funext k
  by_cases hkj : k = j
  · subst k
    simp
  · simp [Function.update_of_ne hkj, hU]

theorem localKernel_diagonal (j : S) (f : A j → ℂ) :
    localKernel j (Matrix.diagonal f) = Matrix.diagonal (fun x => f (x j)) := by
  let g : ∀ k, A k → ℂ := Function.update (fun k (_ : A k) => (1 : ℂ)) j f
  have hg : Function.update (fun k => (1 : Matrix (A k) (A k) ℂ)) j (Matrix.diagonal f) =
      fun k => Matrix.diagonal (g k) := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [g]
    · simp [g, Function.update_of_ne hkj]
  rw [localKernel, hg, tensor_diagonal]
  apply congrArg Matrix.diagonal
  funext x
  rw [Finset.prod_eq_single j]
  · simp [g]
  · intro k _ hkj
    simp [g, Function.update_of_ne hkj]
  · simp

end

end MainTheory.FiniteTensorKernel
