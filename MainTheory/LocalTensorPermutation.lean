import MainTheory.LocalTensorKernel

/-! # Products and inverses of local tensor gates with qubit permutations -/

namespace MainTheory.LocalTensorKernel

open ClassificationLevels SixQubit.CodeEquiv

noncomputable section

variable {n : ℕ}

theorem permutationKernel_mul_apply (sigma : Equiv.Perm (Fin n)) (A : OperatorKernel n)
    (x y : SS.BitString n) :
    (qubitPermutationKernel sigma * A) x y = A (permStr sigma.symm x) y := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (permStr sigma.symm x)]
  · have h : permStr sigma (permStr sigma.symm x) = x :=
      (permStrEquiv sigma).right_inv x
    simp [qubitPermutationKernel, h]
  · intro z _ hz
    have h : x ≠ permStr sigma z := by
      intro h
      have heq : permStr sigma.symm x = z := by
        rw [h]
        exact (permStrEquiv sigma).left_inv z
      exact hz heq.symm
    simp [qubitPermutationKernel, h]
  · simp

theorem mul_permutationKernel_apply (A : OperatorKernel n) (sigma : Equiv.Perm (Fin n))
    (x y : SS.BitString n) :
    (A * qubitPermutationKernel sigma) x y = A x (permStr sigma y) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (permStr sigma y)]
  · simp [qubitPermutationKernel]
  · intro z _ hz
    simp [qubitPermutationKernel, hz]
  · simp

@[simp] theorem permutationKernel_one : qubitPermutationKernel (1 : Equiv.Perm (Fin n)) = 1 := by
  ext x y
  change (if x = SixQubit.CodeEquiv.permStr 1 y then (1 : ℂ) else 0) = _
  have h : SixQubit.CodeEquiv.permStr (1 : Equiv.Perm (Fin n)) y = y := rfl
  rw [h]
  rfl

theorem permutationKernel_mul (sigma tau : Equiv.Perm (Fin n)) :
    qubitPermutationKernel sigma * qubitPermutationKernel tau =
      qubitPermutationKernel (tau * sigma) := by
  ext x y
  rw [permutationKernel_mul_apply]
  have h : permStr sigma.symm x = permStr tau y ↔ x = permStr (tau * sigma) y := by
    constructor
    · intro h
      have hh := congrArg (permStr sigma) h
      have hinv : permStr sigma (permStr sigma.symm x) = x :=
        (permStrEquiv sigma).right_inv x
      exact hinv.symm.trans hh
    · intro h
      rw [h]
      funext i
      simp [permStr]
  simp only [qubitPermutationKernel, h]

@[simp] theorem permutationKernel_star (sigma : Equiv.Perm (Fin n)) :
    star (qubitPermutationKernel sigma) = qubitPermutationKernel sigma.symm := by
  ext x y
  rw [Matrix.star_apply]
  have h : y = permStr sigma x ↔ x = permStr sigma.symm y := by
    constructor
    · intro h
      rw [h]
      exact ((permStrEquiv sigma).left_inv x).symm
    · intro h
      rw [h]
      exact ((permStrEquiv sigma).right_inv y).symm
  simp [qubitPermutationKernel, h]

theorem permutationKernel_unitary (sigma : Equiv.Perm (Fin n)) :
    star (qubitPermutationKernel sigma) * qubitPermutationKernel sigma = 1 ∧
      qubitPermutationKernel sigma * star (qubitPermutationKernel sigma) = 1 := by
  simp [permutationKernel_mul]

/-- Moving a tensor gate past a physical permutation just permutes its factors. -/
theorem permutationKernel_tensor (sigma : Equiv.Perm (Fin n))
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    qubitPermutationKernel sigma * tensorKernel U =
      tensorKernel (fun j => U (sigma j)) * qubitPermutationKernel sigma := by
  ext x y
  rw [permutationKernel_mul_apply, mul_permutationKernel_apply]
  unfold tensorKernel
  have h := Equiv.prod_comp sigma
    (fun j => U j (bitIndex (x (sigma.symm j))) (bitIndex (y j)))
  simpa only [permStr, Equiv.symm_apply_apply] using h.symm

/-- The physical operator in the manuscript's single tensor-times-permutation form. -/
def localPermutationKernel (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (sigma : Equiv.Perm (Fin n)) : OperatorKernel n :=
  tensorKernel U * qubitPermutationKernel sigma

theorem localPermutationKernel_mul (U V : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (sigma tau : Equiv.Perm (Fin n)) :
    localPermutationKernel U sigma * localPermutationKernel V tau =
      localPermutationKernel (fun j => U j * V (sigma j)) (tau * sigma) := by
  unfold localPermutationKernel
  calc (tensorKernel U * qubitPermutationKernel sigma) *
        (tensorKernel V * qubitPermutationKernel tau)
      = tensorKernel U * (qubitPermutationKernel sigma * tensorKernel V) *
          qubitPermutationKernel tau := by simp [Matrix.mul_assoc]
    _ = (tensorKernel U * tensorKernel (fun j => V (sigma j))) *
        (qubitPermutationKernel sigma * qubitPermutationKernel tau) := by
      rw [permutationKernel_tensor]; simp [Matrix.mul_assoc]
    _ = _ := by rw [← tensorKernel_mul, permutationKernel_mul]

theorem localPermutationKernel_star (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (sigma : Equiv.Perm (Fin n)) :
    star (localPermutationKernel U sigma) =
      localPermutationKernel (fun j => star (U (sigma.symm j))) sigma.symm := by
  simp only [localPermutationKernel, star_mul, permutationKernel_star,
    ← tensorKernel_star, permutationKernel_tensor]

theorem localPermutationKernel_unitary (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ j, IsOneQubitUnitary (U j)) (sigma : Equiv.Perm (Fin n)) :
    star (localPermutationKernel U sigma) * localPermutationKernel U sigma = 1 ∧
      localPermutationKernel U sigma * star (localPermutationKernel U sigma) = 1 := by
  obtain ⟨hT, hT'⟩ := tensorKernel_unitary U hU
  obtain ⟨hP, hP'⟩ := permutationKernel_unitary sigma
  constructor
  · change star (tensorKernel U * qubitPermutationKernel sigma) *
      (tensorKernel U * qubitPermutationKernel sigma) = 1
    rw [star_mul]
    calc _ = star (qubitPermutationKernel sigma) *
        (star (tensorKernel U) * tensorKernel U) * qubitPermutationKernel sigma := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [hT]; simpa using hP
  · change (tensorKernel U * qubitPermutationKernel sigma) *
      star (tensorKernel U * qubitPermutationKernel sigma) = 1
    rw [star_mul]
    calc _ = tensorKernel U *
        (qubitPermutationKernel sigma * star (qubitPermutationKernel sigma)) * star (tensorKernel U) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [hP']; simpa using hT'

end

end MainTheory.LocalTensorKernel
