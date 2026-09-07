import MainTheory.UnitarySpectral
import Mathlib

/-! # Unitary diagonalization in arbitrary finite matrix dimension -/

namespace MainTheory.UnitaryMatrixDiagonalization

open UnitarySpectral

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem isUnitaryOn_toEuclideanLin (U : Matrix H H ℂ) (hU : U.conjTranspose * U = 1) :
    IsUnitaryOn U.toEuclideanLin := by
  intro x y
  simp only [Matrix.toEuclideanLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.star_mulVec]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    hU, Matrix.vecMul_one, dotProduct_comm]

/-- Every finite complex unitary matrix has an orthonormal eigenbasis;
both unitary equations and all unit-circle eigenvalues are explicit. -/
theorem exists_unitary_diagonalization (U : Matrix H H ℂ)
    (hU : U.conjTranspose * U = 1) :
    ∃ W : Matrix H H ℂ, ∃ lambda : H → ℂ,
      W.conjTranspose * W = 1 ∧ W * W.conjTranspose = 1 ∧
      (∀ j, star (lambda j) * lambda j = 1) ∧
      W.conjTranspose * U * W = Matrix.diagonal lambda := by
  let T := U.toEuclideanLin
  have hT : IsUnitaryOn T := isUnitaryOn_toEuclideanLin U hU
  have horth := orthogonalFamily_eigenspaces' hT
  have hint := directSum_isInternal hT
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ H) = Fintype.card H := by simp
  let B0 := hint.subordinateOrthonormalBasis hdim horth
  let mu0 := fun j : Fin (Fintype.card H) => hint.subordinateOrthonormalBasisIndex hdim j horth
  let B : OrthonormalBasis H ℂ (EuclideanSpace ℂ H) := B0.reindex (Fintype.equivFin H).symm
  let lambda : H → ℂ := fun j => (mu0 ((Fintype.equivFin H) j) : ℂ)
  let W : Matrix H H ℂ := fun i j => B j i
  have hW : W ∈ Matrix.unitaryGroup H ℂ := by
    exact (EuclideanSpace.basisFun H ℂ).toMatrix_orthonormalBasis_mem_unitary B
  have hW1 : W.conjTranspose * W = 1 := hW.1
  have hcol (j : H) : T (B j) = lambda j • B j := by
    apply Module.End.mem_eigenspace_iff.1
    simpa only [B, OrthonormalBasis.reindex_apply, Equiv.symm_symm, B0, lambda, mu0] using
      hint.subordinateOrthonormalBasis_subordinate hdim ((Fintype.equivFin H) j) horth
  have hmul : U * W = W * Matrix.diagonal lambda := by
    ext i j
    rw [Matrix.mul_diagonal]
    have h := congrArg (fun x : EuclideanSpace ℂ H => x i) (hcol j)
    simpa only [T, Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp,
      PiLp.smul_apply, smul_eq_mul, W, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      mul_comm] using h
  refine ⟨W, lambda, hW.1, hW.2, ?_, ?_⟩
  · intro j
    exact conj_mul_eigenvalue hT (mu0 ((Fintype.equivFin H) j)).property
  · calc
      W.conjTranspose * U * W = W.conjTranspose * (U * W) := Matrix.mul_assoc _ _ _
      _ = Matrix.diagonal lambda := by rw [hmul, ← Matrix.mul_assoc, hW1, Matrix.one_mul]

end

end MainTheory.UnitaryMatrixDiagonalization
