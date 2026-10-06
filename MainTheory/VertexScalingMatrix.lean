import Mathlib

set_option autoImplicit false

namespace MainTheory.VertexScalingMatrix

noncomputable def scale {n : ℕ} (d : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => d i*d j*A i j

theorem diagonal_factorization {n : ℕ} (d : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    scale d A=Matrix.diagonal d*A*Matrix.diagonal d := by
  ext i j
  simp [scale,Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring

theorem determinant {n : ℕ} (d : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (scale d A).det=(∏ i,d i)^2*A.det := by
  rw [diagonal_factorization,Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal]
  ring

theorem singular_iff {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i,d i ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℂ) : (scale d A).det=0 ↔ A.det=0 := by
  rw [determinant,mul_eq_zero]
  have hn : (∏ i,d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  simp [hn]

end MainTheory.VertexScalingMatrix
