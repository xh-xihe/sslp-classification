import MainTheory.SignBinaryBridge
import MainTheory.IntegerInverseBound
import MainTheory.GramPrefixBound

/-! A semantic target for finite signed-matrix certificates.  A leaf either
has a small determinant, or supplies an actual integral cleared inverse. -/

namespace MainTheory.SignMatrixCertificate

open Matrix SharpClearing BinaryBeta SignBinaryBridge IntegerInverseBound
open scoped BigOperators

def Good {s : Type*} [Fintype s] [DecidableEq s]
    (T : ℤ) (B : ℕ) (A : Matrix s s ℤ) : Prop :=
  |A.det| < T ∨ ∃ q : ℕ, 0 < q ∧ q ≤ B ∧
    ∃ J : Matrix s s ℤ, A * J = (2 * (q : ℤ)) • 1

theorem good_of_cleared_inverse {s : Type*} [Fintype s] [DecidableEq s]
    {T : ℤ} {B q : ℕ} {A J : Matrix s s ℤ}
    (hq : 0 < q) (hB : q ≤ B) (hJ : A * J = (2 * (q : ℤ)) • 1) :
    Good T B A := Or.inr ⟨q, hq, hB, J, hJ⟩

theorem inverseDenominator_le_of_good {n B : ℕ}
    (C : Matrix (Fin n) (Fin n) ℤ) (hC : C.det ≠ 0)
    (h : Good ((2 : ℤ)^n * (B+1)) B (signLift C)) :
    inverseDenominator C ≤ B := by
  rcases h with h | ⟨q, hq, hqB, J, hJ⟩
  · rw [det_signLift, abs_mul, abs_pow] at h
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)] at h
    have hp : (0 : ℤ) < 2^n := by positivity
    have hd : |C.det| < (B : ℤ) + 1 := by nlinarith
    have hn : C.det.natAbs ≤ B := by
      have he := Int.natCast_natAbs C.det
      omega
    exact (inverseDenominator_le_detNatAbs C hC).trans hn
  · obtain ⟨J', hJ'⟩ := cleared_binary_of_signLift C J (q : ℤ) hJ
    exact (inverseDenominator_le_of_integer_inverse C J' hC q hq hJ').trans hqB

theorem betaBound_of_good {n B : ℕ}
    (h : ∀ C : Matrix (Fin n) (Fin n) ℤ, IsZeroOne C →
      Good ((2 : ℤ)^n * (B+1)) B (signLift C)) : BetaBound n B := by
  apply betaBound_of_fixedSize_inverseDenominator_bound
  intro C hbinary hdet
  exact inverseDenominator_le_of_good C hdet (h C hbinary)

theorem good_reindex {s t : Type*} [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t] {T : ℤ} {B : ℕ}
    {A : Matrix s s ℤ} (h : Good T B A) (er ec : t ≃ s) :
    Good T B (A.submatrix er ec) := by
  rcases h with h | ⟨q, hq, hB, J, hJ⟩
  · exact Or.inl (by simpa only [Matrix.abs_det_submatrix_equiv_equiv] using h)
  · refine Or.inr ⟨q, hq, hB, J.submatrix ec er, ?_⟩
    rw [Matrix.submatrix_mul_equiv, hJ]
    ext i j
    change (2 * (q : ℤ)) * (if er i = er j then 1 else 0) =
      (2 * (q : ℤ)) * (if i = j then 1 else 0)
    simp only [er.injective.eq_iff]

theorem good_mul {s : Type*} [Fintype s] [DecidableEq s]
    {T : ℤ} {B : ℕ} {A U V Ui Vi : Matrix s s ℤ}
    (h : Good T B A) (hU : U * Ui = 1) (hV : V * Vi = 1)
    (hdU : |U.det| = 1) (hdV : |V.det| = 1) : Good T B (U * A * V) := by
  rcases h with h | ⟨q, hq, hB, J, hJ⟩
  · left
    simpa only [Matrix.det_mul, abs_mul, hdU, hdV, one_mul, mul_one] using h
  · refine Or.inr ⟨q, hq, hB, Vi * J * Ui, ?_⟩
    calc
      U * A * V * (Vi * J * Ui) = U * (A * J) * Ui := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc V Vi, hV, Matrix.one_mul]
      _ = (2 * (q : ℤ)) • 1 := by
        rw [hJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

theorem sign_abs {z : ℤ} (h : z = 1 ∨ z = -1) : |z| = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem diagonal_sign_sq {s : Type*} [Fintype s] [DecidableEq s]
    (u : s → ℤ) (hu : ∀ i, u i = 1 ∨ u i = -1) :
    Matrix.diagonal u * Matrix.diagonal u = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have he : (fun i => u i * u i) = fun _ => (1 : ℤ) := by
    funext i
    rcases hu i with h | h <;> rw [h] <;> norm_num
  rw [he, Matrix.diagonal_one]

theorem abs_det_diagonal_sign {s : Type*} [Fintype s] [DecidableEq s]
    (u : s → ℤ) (hu : ∀ i, u i = 1 ∨ u i = -1) :
    |(Matrix.diagonal u).det| = 1 := by
  rw [Matrix.det_diagonal, Finset.abs_prod]
  simp only [sign_abs (hu _), Finset.prod_const_one]

theorem good_signed {s : Type*} [Fintype s] [DecidableEq s]
    {T : ℤ} {B : ℕ} {A : Matrix s s ℤ} (h : Good T B A)
    (er ec : Equiv.Perm s) (u v : s → ℤ)
    (hu : ∀ i, u i = 1 ∨ u i = -1) (hv : ∀ i, v i = 1 ∨ v i = -1) :
    Good T B (fun i j => u i * A (er i) (ec j) * v j) := by
  have ht := good_mul (good_reindex h er ec)
    (diagonal_sign_sq u hu) (diagonal_sign_sq v hv)
    (abs_det_diagonal_sign u hu) (abs_det_diagonal_sign v hv)
  have he : Matrix.diagonal u * A.submatrix er ec * Matrix.diagonal v =
      (fun i j => u i * A (er i) (ec j) * v j) := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply]
  rw [he] at ht
  exact ht

end MainTheory.SignMatrixCertificate
