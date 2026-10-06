import Mathlib

/-! Soundness of exact rational LDL certificates. No floating point or external oracle. -/
namespace Orbit2
open scoped BigOperators
open Matrix

/-- A rational matrix with an explicit sum-of-squares factorization. -/
structure LDLCertificate (n r : ℕ) where
  A : Matrix (Fin n) (Fin n) ℚ
  L : Matrix (Fin n) (Fin r) ℚ
  d : Fin r → ℚ
  positive : ∀ k, 0 < d k
  factorization : ∀ i j, A i j = ∑ k, L i k * d k * L j k

def realMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => A i j

/-- A checked rational factorization proves positivity for ALL real vectors. -/
theorem LDLCertificate.real_posSemidef {n r : ℕ} (C : LDLCertificate n r) :
    (realMatrix C.A).PosSemidef := by
  let L : Matrix (Fin n) (Fin r) ℝ := fun i k => C.L i k
  let d : Fin r → ℝ := fun k => C.d k
  have hd : 0 ≤ d := by
    intro k
    change (0 : ℝ) ≤ (C.d k : ℝ)
    exact_mod_cast le_of_lt (C.positive k)
  have heq : realMatrix C.A = L * Matrix.diagonal d * L.conjTranspose := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      star_trivial]
    change (C.A i j : ℝ) = ∑ k, (C.L i k : ℝ) * (C.d k : ℝ) * (C.L j k : ℝ)
    exact_mod_cast C.factorization i j
  rw [heq]
  exact (Matrix.PosSemidef.diagonal hd).mul_mul_conjTranspose_same L

/-- Real and imaginary quadratic forms; for real symmetric A this is Re(zᴴAz). -/
def complexEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (z : Fin n → ℂ) : ℝ :=
  (fun i => (z i).re) ⬝ᵥ (realMatrix A *ᵥ fun i => (z i).re) +
  (fun i => (z i).im) ⬝ᵥ (realMatrix A *ᵥ fun i => (z i).im)


/-- The real/imaginary definition is the usual Hermitian quadratic form. -/
theorem complexEnergy_eq_re {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (z : Fin n → ℂ) :
    complexEnergy A z =
      (star z ⬝ᵥ ((fun i j => (A i j : ℂ)) *ᵥ z)).re := by
  simp [complexEnergy, dotProduct, Matrix.mulVec, realMatrix,
    Complex.mul_re, Complex.mul_im, Complex.re_sum,
    Finset.mul_sum, Finset.sum_add_distrib, Rat.cast_def]

theorem LDLCertificate.complexEnergy_nonneg {n r : ℕ} (C : LDLCertificate n r)
    (z : Fin n → ℂ) : 0 ≤ complexEnergy C.A z := by
  have h := C.real_posSemidef
  exact add_nonneg (by simpa using h.dotProduct_mulVec_nonneg (fun i => (z i).re))
    (by simpa using h.dotProduct_mulVec_nonneg (fun i => (z i).im))

/-- M - 4I = LDLᵀ implies the manuscript's coercive estimate. -/
theorem shifted_coercivity {n r : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (C : LDLCertificate n r) (hshift : ∀ i j, C.A i j = M i j - if i = j then 4 else 0)
    (z : Fin n → ℂ) :
    4 * ∑ i, Complex.normSq (z i) ≤ complexEnergy M z := by
  have heq : realMatrix M = realMatrix C.A + (4 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    have hij := hshift i j
    simp only [realMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply]
    have hc : (C.A i j : ℝ) = (M i j : ℝ) - if i = j then 4 else 0 := by
      split_ifs at * <;> exact_mod_cast hij
    split_ifs at * <;> linarith
  have h := C.complexEnergy_nonneg z
  have hn : complexEnergy M z = complexEnergy C.A z + 4 * ∑ i, Complex.normSq (z i) := by
    unfold complexEnergy
    rw [heq]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [dotProduct, Complex.normSq_apply, Finset.sum_add_distrib]
    ring
  linarith

end Orbit2
