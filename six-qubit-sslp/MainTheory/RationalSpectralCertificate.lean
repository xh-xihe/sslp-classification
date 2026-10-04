import Mathlib

/-! Exact similarity certificates for characteristic polynomials. -/
namespace MainTheory.RationalSpectralCertificate

open Polynomial
noncomputable section

def linearBlock (r : ℚ) : Matrix (Fin 1) (Fin 1) ℚ := !![r]

def quadraticBlock (p q : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![0, -q; 1, p]

def join {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (B : Matrix (Fin m) (Fin m) ℚ) : Matrix (Fin (n + m)) (Fin (n + m)) ℚ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

theorem linearBlock_charpoly (r : ℚ) : (linearBlock r).charpoly = X - C r := by
  simp [linearBlock, Matrix.charpoly, Matrix.charmatrix]

theorem quadraticBlock_charpoly (p q : ℚ) :
    (quadraticBlock p q).charpoly = X ^ 2 - C p * X + C q := by
  rw [Matrix.charpoly_fin_two]
  simp [quadraticBlock, Matrix.trace, Matrix.det_fin_two]

theorem join_charpoly {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (B : Matrix (Fin m) (Fin m) ℚ) : (join A B).charpoly = A.charpoly * B.charpoly := by
  rw [join, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁]

theorem charpoly_of_similarity {n : ℕ} (A B S T : Matrix (Fin n) (Fin n) ℚ)
    (hTS : T * S = 1) (hAS : A * S = S * B) : A.charpoly = B.charpoly := by
  have hST : S * T = 1 := mul_eq_one_comm.mp hTS
  have h : T * (A * S) = B := by rw [hAS, ← Matrix.mul_assoc, hTS, Matrix.one_mul]
  calc
    A.charpoly = ((A * S) * T).charpoly := by rw [Matrix.mul_assoc, hST, Matrix.mul_one]
    _ = (T * (A * S)).charpoly := Matrix.charpoly_mul_comm _ _
    _ = B.charpoly := congrArg Matrix.charpoly h

end
end MainTheory.RationalSpectralCertificate
