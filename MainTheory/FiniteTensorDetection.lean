import MainTheory.FiniteTensorKernel
import MainTheory.UnitaryMatrixDiagonalization

/-! # Exact single-subsystem detection in arbitrary local dimensions -/

namespace MainTheory.FiniteTensorDetection

open FiniteTensorKernel UnitaryMatrixDiagonalization

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] {A : S → Type*}
  [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
  {L : Type*} [Fintype L] [DecidableEq L]

set_option linter.unusedSectionVars false

/-- Every operator acting on any one complete physical subsystem has scalar
compression.  Subsystems may have different arbitrary finite dimensions. -/
def DetectsLocal (V : Matrix (∀ j, A j) L ℂ) : Prop :=
  ∀ j (M : Matrix (A j) (A j) ℂ), ∃ c : ℂ,
    V.conjTranspose * localKernel j M * V = c • 1

theorem detectsLocal_change_basis (V : Matrix (∀ j, A j) L ℂ) (hV : DetectsLocal V)
    (W : ∀ j, Matrix (A j) (A j) ℂ)
    (hW : ∀ j, (W j).conjTranspose * W j = 1 ∧ W j * (W j).conjTranspose = 1) :
    DetectsLocal ((tensor W).conjTranspose * V) := by
  intro j M
  obtain ⟨c, hc⟩ := hV j (W j * M * (W j).conjTranspose)
  refine ⟨c, ?_⟩
  have hlocal : tensor W * localKernel j M * (tensor W).conjTranspose =
      localKernel j (W j * M * (W j).conjTranspose) := by
    simpa only [tensor_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      tensor_conjugate_local (fun j => (W j).conjTranspose) (fun j => by simpa using (hW j).2) j M
  calc
    _ = V.conjTranspose * (tensor W * localKernel j M * (tensor W).conjTranspose) * V := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = c • 1 := by rw [hlocal, hc]

/-- Diagonalize every genuine physical local unitary in its own subsystem,
transport the actual encoding, and preserve every single-subsystem KL
equation and the very same logical action. -/
theorem exists_diagonal_normal_form
    (V : Matrix (∀ j, A j) L ℂ) (hV : V.conjTranspose * V = 1) (hdet : DetectsLocal V)
    (U : ∀ j, Matrix (A j) (A j) ℂ)
    (hU : ∀ j, (U j).conjTranspose * U j = 1)
    (Q : Matrix L L ℂ) (hQ : tensor U * V = V * Q) :
    ∃ V' : Matrix (∀ j, A j) L ℂ, ∃ lambda : ∀ j, A j → ℂ,
      V'.conjTranspose * V' = 1 ∧ DetectsLocal V' ∧
      (∀ j a, star (lambda j a) * lambda j a = 1) ∧
      Matrix.diagonal (fun x => ∏ j, lambda j (x j)) * V' = V' * Q := by
  choose W lambda hW1 hW2 hlam hdiag using fun j => exists_unitary_diagonalization (U j) (hU j)
  have hW := tensor_unitary W (fun j => ⟨hW1 j, hW2 j⟩)
  let V' := (tensor W).conjTranspose * V
  have hV' : V'.conjTranspose * V' = 1 := by
    calc
      _ = V.conjTranspose * (tensor W * (tensor W).conjTranspose) * V := by
        simp [V', Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hW.2]; simpa using hV
  have hdiagonal : (tensor W).conjTranspose * tensor U * tensor W =
      Matrix.diagonal (fun x => ∏ j, lambda j (x j)) := by
    rw [← tensor_conjTranspose, ← tensor_mul, ← tensor_mul]
    simp only [hdiag, tensor_diagonal]
  refine ⟨V', lambda, hV', detectsLocal_change_basis V hdet W (fun j => ⟨hW1 j, hW2 j⟩), hlam, ?_⟩
  calc
    _ = (tensor W).conjTranspose * tensor U * V := by
      rw [← hdiagonal]
      change (tensor W).conjTranspose * tensor U * tensor W * ((tensor W).conjTranspose * V) = _
      calc
        _ = (tensor W).conjTranspose * tensor U * (tensor W * (tensor W).conjTranspose) * V := by
          simp [Matrix.mul_assoc]
        _ = _ := by rw [hW.2, Matrix.mul_one]
    _ = V' * Q := by rw [Matrix.mul_assoc, hQ]; simp [V', Matrix.mul_assoc]

end

end MainTheory.FiniteTensorDetection
