import MainTheory.SignQuadraticMinimum
import MainTheory.SignDagFastCertificate

namespace MainTheory.SignQuadraticPrune

open scoped BigOperators
open Matrix MainTheory.SignQuadraticMinimum MainTheory.SignPrefixCertificate
open MainTheory.GramSchurCertificate

theorem quadratic_eq_dotProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) : quadratic 0 0 A v = v ⬝ᵥ (A *ᵥ v) := by
  simp only [quadratic, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_pullback {k N : ℕ} (P : Matrix (Fin k) (Fin N) ℤ)
    (J : Matrix (Fin k) (Fin k) ℤ) (v : Fin N → ℤ) :
    quadratic 0 0 (P.transpose * J * P) v = quadratic 0 0 J (cross P v) := by
  simp only [quadratic_eq_dotProduct, Matrix.mul_assoc, ← mulVec_mulVec]
  rw [dotProduct_mulVec, vecMul_transpose]
  rfl

theorem gram_snoc_eq_quadratic {k N : ℕ} (P : Matrix (Fin k) (Fin N) ℤ)
    (v : Fin N → ℤ) (hv : ∀ j, v j = 1 ∨ v j = -1)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ) (ha : a ≠ 0)
    (hdet : (gram P).det = a) (hAJ : gram P * J = a • 1)
    (K : Matrix (Fin N) (Fin N) ℤ) (hK : K = P.transpose * J * P) :
    (gram (Fin.snoc P v)).det = (N : ℤ) * a - quadratic 0 0 K v := by
  rw [det_gram_snoc P v hv J a ha hdet hAJ, hK, quadratic_pullback]
  congr 1
  simp only [quadratic, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A single exhaustive integer quadratic minimum can discharge every child
of this prefix, without separate repeated Gram products for each signed row. -/
theorem prefixGood_of_quadratic_minimum {k N : ℕ} {T : ℤ} {B : ℕ}
    (hk : k+1 ≤ N) (P : Matrix (Fin k) (Fin N) ℤ)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ) (ha : a ≠ 0)
    (hdet : (gram P).det = a) (hAJ : gram P * J = a • 1) (hT : 0 ≤ T)
    (K : Matrix (Fin N) (Fin N) ℤ) (hK : K = P.transpose * J * P)
    (hbound : ((N : ℤ) * a - minimum N 0 0 K) * (N : ℤ) ^ (N-(k+1)) < T^2) :
    PrefixGood T B (by omega : k ≤ N) P := by
  apply prefixGood_step hk P
  intro v hv
  apply prefixGood_prune hk _ hT
  change (gram (Fin.snoc P v)).det * (N : ℤ) ^ (N-(k+1)) < T^2
  rw [gram_snoc_eq_quadratic P v hv J a ha hdet hAJ K hK]
  have hm := minimum_le N 0 0 K v hv
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (sub_le_sub_left hm _)
    (pow_nonneg (by omega) _)) hbound

end MainTheory.SignQuadraticPrune
