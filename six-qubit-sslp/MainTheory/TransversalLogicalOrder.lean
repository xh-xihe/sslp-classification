import MainTheory.OneHotZDetection
import MainTheory.DiagonalLogicalOrder
import MainTheory.UnitaryAdjointRepresentation

/-! # Uniform finite projective order for arbitrary-dimensional transversal gates

Each physical subsystem is diagonalized in its own eigenbasis, then encoded
isometrically using one-hot qubits.  Single-subsystem error detection gives
exactly the Z-detection equations needed by the existing binary finite-lift
theorem.  The original logical matrix is preserved throughout this chain.
-/

namespace MainTheory.TransversalLogicalOrder

open FiniteTensorKernel FiniteTensorDetection OneHotTensorEmbedding OneHotZDetection
open ClassificationLevels PauliKernelBTrace

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] {A : S → Type*}
  [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] {K : ℕ}

set_option linter.unusedSectionVars false

/-- Every actual transversal logical unitary has a scalar positive power,
uniformly bounded by `beta_(Σ_j dim(H_j)+K−1)`.  No finite-order or finite
generation hypothesis is imposed on the physical or logical gate. -/
theorem exists_bounded_scalar_power
    (V : Matrix (∀ j, A j) (Fin K) ℂ) (hV : V.conjTranspose * V = 1)
    (hK : 0 < K) (hdet : DetectsLocal V)
    (U : ∀ j, Matrix (A j) (A j) ℂ) (hU : ∀ j, (U j).conjTranspose * U j = 1)
    (Q : Matrix (Fin K) (Fin K) ℂ) (hQU : Q * Q.conjTranspose = 1)
    (hQ : tensor U * V = V * Q) :
    ∃ m : ℕ, 0 < m ∧ m ≤ BetaExists.betaOf (size A + K - 1) ∧
      ∃ c : ℂ, Q ^ m = c • 1 := by
  obtain ⟨V', lambda, hV', hdet', hlam, hQ'⟩ :=
    exists_diagonal_normal_form V hV hdet U hU Q hQ
  let u : ∀ j, A j → unitary ℂ := fun j a =>
    ⟨lambda j a, hlam j a, by simpa only [mul_comm] using hlam j a⟩
  let F := embeddedFrame V' hV'
  have hZ := zDetects_embeddedFrame V' hV' hdet'
  have hmat : diagonalKernel (localPhase u) * frameMatrix F = frameMatrix F * Q := by
    change diagonalKernel (localPhase u) * (embedding (A := A) * V') =
      (embedding (A := A) * V') * Q
    rw [← Matrix.mul_assoc, diagonalKernel_embedding, Matrix.mul_assoc]
    change embedding (A := A) *
      ((Matrix.diagonal (fun x : ∀ j, A j => ∏ j, lambda j (x j)) :
        Matrix (∀ j, A j) (∀ j, A j) ℂ) * V') = _
    rw [hQ', Matrix.mul_assoc]
  exact DiagonalLogicalOrder.exists_bounded_scalar_power F hK hZ (localPhase u) Q hQU hmat

/-- The subgroup of logical unitaries implemented by literal tensor products
of physical local unitaries on the fixed actual encoding `V`. -/
def transversalLogicalGroup (V : Matrix (∀ j, A j) (Fin K) ℂ) :
    Subgroup (Matrix.unitaryGroup (Fin K) ℂ) where
  carrier := {Q | ∃ U : ∀ j, Matrix (A j) (A j) ℂ,
    (∀ j, (U j).conjTranspose * U j = 1 ∧ U j * (U j).conjTranspose = 1) ∧
      tensor U * V = V * (Q : Matrix (Fin K) (Fin K) ℂ)}
  one_mem' := ⟨fun _ => 1, fun _ => by simp, by simp⟩
  mul_mem' := by
    rintro P Q ⟨U, hU, hP⟩ ⟨W, hW, hQ⟩
    refine ⟨fun j => U j * W j, ?_, ?_⟩
    · intro j
      constructor
      · calc
          _ = (W j).conjTranspose * ((U j).conjTranspose * U j) * W j := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = 1 := by rw [(hU j).1]; simpa using (hW j).1
      · calc
          _ = U j * (W j * (W j).conjTranspose) * (U j).conjTranspose := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = 1 := by rw [(hW j).2]; simpa using (hU j).2
    · rw [tensor_mul, Matrix.mul_assoc, hQ, ← Matrix.mul_assoc, hP, Matrix.mul_assoc]
      rfl
  inv_mem' := by
    rintro Q ⟨U, hU, hQ⟩
    refine ⟨fun j => (U j).conjTranspose, fun j => by simpa using ⟨(hU j).2, (hU j).1⟩, ?_⟩
    have hTU := (tensor_unitary U hU).1
    have hQU : (Q : Matrix (Fin K) (Fin K) ℂ) *
        (Q : Matrix (Fin K) (Fin K) ℂ).conjTranspose = 1 := Q.property.2
    rw [tensor_conjTranspose]
    change (tensor U).conjTranspose * V = V * (Q : Matrix (Fin K) (Fin K) ℂ).conjTranspose
    calc
      _ = (tensor U).conjTranspose * (V * (Q : Matrix (Fin K) (Fin K) ℂ)) *
          (Q : Matrix (Fin K) (Fin K) ℂ).conjTranspose := by
        simp [Matrix.mul_assoc, hQU]
      _ = _ := by rw [← hQ, ← Matrix.mul_assoc, hTU, Matrix.one_mul]

/-- The full physical transversal group has only finitely many distinct
logical actions modulo global phase, in arbitrary finite local dimensions. -/
theorem finite_projective_transversal_image
    (V : Matrix (∀ j, A j) (Fin K) ℂ) (hV : V.conjTranspose * V = 1)
    (hK : 0 < K) (hdet : DetectsLocal V) :
    Finite ((transversalLogicalGroup V).map UnitaryAdjointRepresentation.adjoint) := by
  apply UnitaryAdjointRepresentation.finite_adjoint_image_of_bounded_projective_order
    (transversalLogicalGroup V) (BetaExists.betaOf (size A + K - 1))
  intro Q
  obtain ⟨U, hU, hQ⟩ := Q.property
  obtain ⟨m, hm, hmB, c, hc⟩ := exists_bounded_scalar_power V hV hK hdet U (fun j => (hU j).1)
    Q.val.val Q.val.property.2 hQ
  exact ⟨m, hm, hmB, c, by simpa using hc⟩

end

end MainTheory.TransversalLogicalOrder
