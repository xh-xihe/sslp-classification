import MainTheory.ClassificationLevels

/-! # Genuine tensor products of arbitrary one-qubit matrices -/

namespace MainTheory.LocalTensorKernel

open ClassificationLevels

noncomputable section

variable {n : ℕ}

def tensorKernel (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : OperatorKernel n :=
  fun x y => ∏ j, U j (bitIndex (x j)) (bitIndex (y j))

theorem bitIndex_injective : Function.Injective bitIndex := by
  intro x y h
  cases x <;> cases y <;> simp_all [bitIndex]

theorem tensorKernel_mul (U V : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorKernel (fun j => U j * V j) = tensorKernel U * tensorKernel V := by
  ext x z
  simp only [Matrix.mul_apply, tensorKernel, ← Finset.prod_mul_distrib]
  calc (∏ i, ∑ j : Fin 2, U i (bitIndex (x i)) j * V i j (bitIndex (z i)))
      = ∏ i, ∑ b : Bool, U i (bitIndex (x i)) (bitIndex b) *
          V i (bitIndex b) (bitIndex (z i)) := by
        apply Finset.prod_congr rfl
        intro j _
        simp [Fin.sum_univ_two, bitIndex, add_comm]
    _ = _ := Fintype.prod_sum (fun i (b : Bool) =>
      U i (bitIndex (x i)) (bitIndex b) * V i (bitIndex b) (bitIndex (z i)))

@[simp] theorem tensorKernel_one : tensorKernel (fun _ : Fin n => 1) = 1 := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensorKernel]
  · rw [Matrix.one_apply_ne hxy]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.one_apply_ne (fun h => hj (bitIndex_injective h))

@[simp] theorem tensorKernel_star (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorKernel (fun j => star (U j)) = star (tensorKernel U) := by
  ext x y
  simp [tensorKernel, Matrix.star_apply]

theorem tensorKernel_unitary (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ j, IsOneQubitUnitary (U j)) :
    star (tensorKernel U) * tensorKernel U = 1 ∧
      tensorKernel U * star (tensorKernel U) = 1 := by
  constructor
  · rw [← tensorKernel_star, ← tensorKernel_mul]
    simpa only [funext (fun j => (hU j).1)] using (tensorKernel_one (n := n))
  · rw [← tensorKernel_star, ← tensorKernel_mul]
    simpa only [funext (fun j => (hU j).2)] using (tensorKernel_one (n := n))

/-- A single-site matrix is the literal tensor product with identities elsewhere. -/
theorem tensorKernel_single (j : Fin n) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorKernel (Function.update (fun _ => 1) j U) = oneQubitKernel j U := by
  classical
  ext x y
  by_cases hxy : ∀ k, k ≠ j → x k = y k
  · rw [oneQubitKernel, if_pos hxy]
    change (∏ k, Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) j U k
      (bitIndex (x k)) (bitIndex (y k))) = _
    rw [Finset.prod_eq_single j]
    · simp
    · intro k _ hkj
      simp [Function.update_of_ne hkj, hxy k hkj]
    · simp
  · rw [oneQubitKernel, if_neg hxy]
    push_neg at hxy
    obtain ⟨k, hkj, hk⟩ := hxy
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [Function.update_of_ne hkj]
    exact Matrix.one_apply_ne (fun h => hk (bitIndex_injective h))

/-- Conjugating an orthogonal projector by a unitary gives an orthogonal projector. -/
def conjugated (P : CodeProjector n) (W : OperatorKernel n)
    (hW : star W * W = 1) : CodeProjector n where
  kernel := W * P.kernel * star W
  hermitian := by simp [star_mul, P.hermitian, Matrix.mul_assoc]
  idempotent := by
    calc (W * P.kernel * star W) * (W * P.kernel * star W)
        = W * P.kernel * (star W * W) * P.kernel * star W := by simp [Matrix.mul_assoc]
      _ = W * P.kernel * star W := by rw [hW]; simp [Matrix.mul_assoc, P.idempotent]

end

end MainTheory.LocalTensorKernel
