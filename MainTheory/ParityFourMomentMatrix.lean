import Mathlib

/-! Integer inverse certificate for the complete parity-four moment system. -/

namespace MainTheory.ParityFourMatrix

open scoped Matrix BigOperators

def matrixZ : Matrix (Fin 16) (Fin 16) ℤ := ![![1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1],
  ![0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0],
  ![1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1],
  ![1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1],
  ![1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1],
  ![1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1],
  ![1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1],
  ![1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1],
  ![1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1],
  ![1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1],
  ![1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1],
  ![1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1],
  ![1, 0, 0, -1, 0, -1, 1, 0, 0, -1, 1, 0, 1, 0, 0, -1],
  ![1, 0, 0, -1, 0, 1, -1, 0, 0, 1, -1, 0, 1, 0, 0, -1],
  ![1, 0, 0, 1, 0, -1, -1, 0, 0, 1, 1, 0, -1, 0, 0, -1],
  ![1, 0, 0, 1, 0, 1, 1, 0, 0, -1, -1, 0, -1, 0, 0, -1]]

def inverseZ : Matrix (Fin 16) (Fin 16) ℤ := ![![2, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2],
  ![0, 2, 2, -2, -2, -2, 1, 1, 1, -1, -1, -1, -2, 2, 2, 2],
  ![0, 2, -2, 2, -2, -2, 1, -1, -1, 1, 1, -1, 2, -2, 2, 2],
  ![2, 0, 0, 0, 0, 0, 1, -1, -1, -1, -1, 1, -2, -2, 2, 2],
  ![0, 2, -2, -2, 2, -2, -1, 1, -1, 1, -1, 1, 2, 2, -2, 2],
  ![2, 0, 0, 0, 0, 0, -1, 1, -1, -1, 1, -1, -2, 2, -2, 2],
  ![2, 0, 0, 0, 0, 0, -1, -1, 1, 1, -1, -1, 2, -2, -2, 2],
  ![0, 2, 2, 2, 2, -2, -1, -1, 1, -1, 1, 1, -2, -2, -2, 2],
  ![0, 2, -2, -2, -2, 2, -1, -1, 1, -1, 1, 1, 2, 2, 2, -2],
  ![2, 0, 0, 0, 0, 0, -1, -1, 1, 1, -1, -1, -2, 2, 2, -2],
  ![2, 0, 0, 0, 0, 0, -1, 1, -1, -1, 1, -1, 2, -2, 2, -2],
  ![0, 2, 2, 2, -2, 2, -1, 1, -1, 1, -1, 1, -2, -2, 2, -2],
  ![2, 0, 0, 0, 0, 0, 1, -1, -1, -1, -1, 1, 2, 2, -2, -2],
  ![0, 2, 2, -2, 2, 2, 1, -1, -1, 1, 1, -1, -2, 2, -2, -2],
  ![0, 2, -2, 2, 2, 2, 1, 1, 1, -1, -1, -1, 2, -2, -2, -2],
  ![2, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, -2, -2, -2, -2]]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem inverseZ_mul_matrixZ : inverseZ * matrixZ = 16 • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem matrixZ_mul_inverseZ : matrixZ * inverseZ = 16 • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  decide

noncomputable def matrix : Matrix (Fin 16) (Fin 16) ℝ := matrixZ.map (Int.castRingHom ℝ)

noncomputable def inverse : Matrix (Fin 16) (Fin 16) ℝ := inverseZ.map (Int.castRingHom ℝ)

theorem inverse_mul_matrix : inverse * matrix = 16 • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  have h := congrArg (fun A : Matrix (Fin 16) (Fin 16) ℤ => A.map (Int.castRingHom ℝ)) inverseZ_mul_matrixZ
  change (inverseZ * matrixZ).map (Int.castRingHom ℝ) =
    (16 • (1 : Matrix (Fin 16) (Fin 16) ℤ)).map (Int.castRingHom ℝ) at h
  rw [Matrix.map_mul] at h
  convert h using 1
  ext i j
  simp [Matrix.ofNat_apply, Matrix.one_apply]

theorem inverse_reconstruct (v w : Fin 16 → ℝ) (h : matrix.mulVec v = w) :
    inverse.mulVec w = (16 : ℝ) • v := by
  rw [← h, Matrix.mulVec_mulVec, inverse_mul_matrix]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem matrix_mul_inverse : matrix * inverse = 16 • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  have h := congrArg (fun A : Matrix (Fin 16) (Fin 16) ℤ => A.map (Int.castRingHom ℝ)) matrixZ_mul_inverseZ
  change (matrixZ * inverseZ).map (Int.castRingHom ℝ) =
    (16 • (1 : Matrix (Fin 16) (Fin 16) ℤ)).map (Int.castRingHom ℝ) at h
  rw [Matrix.map_mul] at h
  convert h using 1
  ext i j
  simp [Matrix.ofNat_apply, Matrix.one_apply]

theorem forward_reconstruct (v w : Fin 16 → ℝ)
    (h : inverse.mulVec w = (16 : ℝ) • v) : matrix.mulVec v = w := by
  have hi := congrArg matrix.mulVec h
  rw [Matrix.mulVec_mulVec, matrix_mul_inverse] at hi
  funext i
  have hk := congrFun hi i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply] at hk
  have he : (∑ x, matrix i x * (16 * v x)) = 16 * (matrix.mulVec v) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he] at hk
  linarith

end MainTheory.ParityFourMatrix
