import Mathlib

/-!
# Exact rational Gram certificates over complex vectors

A generator supplies a rational factorization and a rational inverse. The
kernel checks both identities and strict positivity of the diagonal. Soundness
then applies to all complex vectors, not only rational or sampled vectors.
-/

namespace MainTheory.RationalGramCertificate

open scoped Matrix ComplexOrder

noncomputable section

variable {n : ℕ}

def complexMatrix (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℂ :=
  A.map (algebraMap ℚ ℂ)

theorem complexMatrix_mul (A B : Matrix (Fin n) (Fin n) ℚ) :
    complexMatrix (A * B) = complexMatrix A * complexMatrix B :=
  Matrix.map_mul

theorem complexMatrix_transpose (A : Matrix (Fin n) (Fin n) ℚ) :
    complexMatrix A.transpose = (complexMatrix A).conjTranspose := by
  ext i j
  simp [complexMatrix, Matrix.conjTranspose_apply]

theorem complexMatrix_diagonal (d : Fin n → ℚ) :
    complexMatrix (Matrix.diagonal d) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases hij : i = j <;> simp [complexMatrix, Matrix.diagonal, hij]

/-- Exact `LDL^T` data; a left inverse suffices over the finite-dimensional field. -/
structure Certificate (A : Matrix (Fin n) (Fin n) ℚ) where
  factor : Matrix (Fin n) (Fin n) ℚ
  inverse : Matrix (Fin n) (Fin n) ℚ
  diagonal : Fin n → ℚ
  factorization : A = factor * Matrix.diagonal diagonal * factor.transpose
  inverse_identity : inverse * factor = 1
  diagonal_positive : ∀ i, 0 < diagonal i

theorem factorization_of_entries (A L : Matrix (Fin n) (Fin n) ℚ)
    (d : Fin n → ℚ)
    (h : ∀ i j, A i j = ∑ k, L i k * d k * L j k) :
    A = L * Matrix.diagonal d * L.transpose := by
  ext i j
  rw [h]
  simp [Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply]

/-- Kernel-checked rational identities prove strict positivity on every complex
vector. No floating-point eigensolver is part of the statement or proof. -/
theorem Certificate.posDef {A : Matrix (Fin n) (Fin n) ℚ} (W : Certificate A) :
    (complexMatrix A).PosDef := by
  have hi : IsUnit (complexMatrix W.factor) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨complexMatrix W.inverse, ?_⟩
    rw [← complexMatrix_mul, mul_eq_one_comm.mpr W.inverse_identity]
    simp [complexMatrix]
  have hd : (Matrix.diagonal (fun i => (W.diagonal i : ℂ))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    rw [Complex.pos_iff]
    constructor
    · simpa using (Rat.cast_pos.mpr (W.diagonal_positive i) : (0 : ℝ) < W.diagonal i)
    · simp
  rw [W.factorization, complexMatrix_mul, complexMatrix_mul,
    complexMatrix_diagonal, complexMatrix_transpose]
  exact hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hi)

end

end MainTheory.RationalGramCertificate
