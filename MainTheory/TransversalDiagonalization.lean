import MainTheory.LocalUnitaryKL
import MainTheory.LocalUnitaryClosure
import MainTheory.UnitaryMatrixDiagonalization
import MainTheory.DiagonalLocalKernel

/-! # Diagonalizing an actual transversal gate without changing code parameters -/

namespace MainTheory.TransversalDiagonalization

open scoped BigOperators
open CodeSpec ClassificationLevels LocalTensorKernel LocalUnitaryKL PauliKernelBTrace

noncomputable section

variable {n K d : ℕ}

theorem unitaryCode_luEquivalent (C : ExactCode n K d)
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j, IsOneQubitUnitary (U j)) :
    LUEquivalent (CodeProjector.ofFrame C.frame)
      (CodeProjector.ofFrame (unitaryCode C U hU).frame) := by
  apply LocalUnitaryClosure.luEquivalent_of_tensor _ _ U hU
  simp only [projector_eq_frame_mul_conjTranspose, unitaryCode, frameMatrix_unitaryFrame,
    Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

/-- The eigenbasis change preserves the entire KL distance and the logical matrix. -/
theorem exists_diagonal_tensor (C : ExactCode n K d)
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j, IsOneQubitUnitary (U j))
    (Q : Matrix (Fin K) (Fin K) ℂ)
    (hQ : tensorKernel U * frameMatrix C.frame = frameMatrix C.frame * Q) :
    ∃ C' : ExactCode n K d, ∃ lam : Fin n → Fin 2 → unitary ℂ,
      LUEquivalent (CodeProjector.ofFrame C.frame) (CodeProjector.ofFrame C'.frame) ∧
      tensorKernel (fun j => Matrix.diagonal (fun a => (lam j a : ℂ))) * frameMatrix C'.frame =
        frameMatrix C'.frame * Q := by
  choose W lambda hW1 hW2 hlam hdiag using
    fun j => UnitaryMatrixDiagonalization.exists_unitary_diagonalization (U j) (hU j).1
  let V := fun j => (W j).conjTranspose
  have hV : ∀ j, IsOneQubitUnitary (V j) := fun j => by
    exact ⟨by simpa [V, Matrix.star_eq_conjTranspose] using hW2 j,
      by simpa [V, Matrix.star_eq_conjTranspose] using hW1 j⟩
  let C' := unitaryCode C V hV
  let lam : Fin n → Fin 2 → unitary ℂ := fun j a =>
    ⟨lambda j a, hlam j a, by simpa only [mul_comm] using hlam j a⟩
  refine ⟨C', lam, unitaryCode_luEquivalent C V hV, ?_⟩
  have hW : ∀ j, IsOneQubitUnitary (W j) := fun j => ⟨hW1 j, hW2 j⟩
  have hdiag' : tensorKernel (fun j => Matrix.diagonal (fun a => (lam j a : ℂ))) =
      tensorKernel V * tensorKernel U * tensorKernel W := by
    rw [← tensorKernel_mul, ← tensorKernel_mul]
    congr 1
    exact (funext hdiag).symm
  have hcancel : tensorKernel W * tensorKernel V = 1 := by
    change tensorKernel W * tensorKernel (fun j => star (W j)) = 1
    rw [tensorKernel_star]
    exact (tensorKernel_unitary W hW).2
  change _ * (tensorKernel V * frameMatrix C.frame) = (tensorKernel V * frameMatrix C.frame) * Q
  rw [hdiag']
  calc
    _ = tensorKernel V * tensorKernel U * (tensorKernel W * tensorKernel V) * frameMatrix C.frame := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hcancel]; simp only [Matrix.mul_one, Matrix.mul_assoc, hQ]

def phaseRatios (lam : Fin n → Fin 2 → unitary ℂ) : LocalPhase n :=
  fun j => lam j 1 * (lam j 0)⁻¹

def basePhase (lam : Fin n → Fin 2 → unitary ℂ) : unitary ℂ := ∏ j, lam j 0

/-- Removing the local zero-state phases only removes one global unit scalar. -/
theorem diagonal_tensor_eq_scalar (lam : Fin n → Fin 2 → unitary ℂ) :
    tensorKernel (fun j => Matrix.diagonal (fun a => (lam j a : ℂ))) =
      (basePhase lam : ℂ) • diagonalKernel (phaseRatios lam) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [tensorKernel, Matrix.diagonal_apply_eq, Matrix.smul_apply, diagonalKernel,
      if_true, smul_eq_mul, basePhase, Submonoid.coe_finset_prod, diagonalValue,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    cases x j
    · simp [bitIndex]
    · change (lam j 1 : ℂ) = (lam j 0 : ℂ) * ((lam j 1 * (lam j 0)⁻¹ : unitary ℂ) : ℂ)
      rw [← Submonoid.coe_mul]
      congr 1
      simp [mul_comm]
  · rw [Matrix.smul_apply, diagonalKernel, if_neg hxy, smul_zero]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.diagonal_apply_ne _ (fun h => hj (bitIndex_injective h))

/-- A normalized diagonal product with the original code parameters and LU class. -/
theorem exists_diagonal_normal_form (C : ExactCode n K d)
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j, IsOneQubitUnitary (U j))
    (Q : Matrix (Fin K) (Fin K) ℂ)
    (hQ : tensorKernel U * frameMatrix C.frame = frameMatrix C.frame * Q) :
    ∃ C' : ExactCode n K d, ∃ u : LocalPhase n, ∃ c : unitary ℂ,
      LUEquivalent (CodeProjector.ofFrame C.frame) (CodeProjector.ofFrame C'.frame) ∧
      diagonalKernel u * frameMatrix C'.frame = frameMatrix C'.frame * ((c : ℂ) • Q) := by
  obtain ⟨C', lam, hlu, h⟩ := exists_diagonal_tensor C U hU Q hQ
  refine ⟨C', phaseRatios lam, (basePhase lam)⁻¹, hlu, ?_⟩
  rw [diagonal_tensor_eq_scalar, Matrix.smul_mul] at h
  have hh := congrArg (fun M => (((basePhase lam)⁻¹ : unitary ℂ) : ℂ) • M) h
  simpa only [smul_smul, ← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one,
    one_smul, Matrix.mul_smul] using hh

end

end MainTheory.TransversalDiagonalization
