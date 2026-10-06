import MainTheory.IntegerInverseBound

/-! Exact integral Schur steps.  A proposed adjugate is accepted only through
an integer matrix identity; the determinant is propagated from the parent. -/

namespace MainTheory.GramSchurCertificate

open Matrix SharpClearing IntegerInverseBound
open scoped BigOperators

theorem det_border_field {s F : Type*} [Fintype s] [DecidableEq s] [Field F]
    (A J : Matrix s s F) (b : Matrix s (Fin 1) F) (c : Matrix (Fin 1) s F)
    (d a : F) (ha : a ≠ 0) (hdet : A.det = a) (hAJ : A * J = a • 1) :
    (Matrix.fromBlocks A b c (fun _ _ => d)).det = a*d - (c*J*b) 0 0 := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr (by rwa [hdet])
  letI := Matrix.invertibleOfIsUnitDet A hu
  have hJ := congrArg (fun M => A⁻¹ * M) hAJ
  dsimp only at hJ
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one] at hJ
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
    Matrix.det_fin_one, hdet]
  change a * (d - (c * A⁻¹ * b) 0 0) = a*d - (c*J*b) 0 0
  rw [hJ, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem det_border_int {s : Type*} [Fintype s] [DecidableEq s]
    (A J : Matrix s s ℤ) (b : Matrix s (Fin 1) ℤ) (c : Matrix (Fin 1) s ℤ)
    (d a : ℤ) (ha : a ≠ 0) (hdet : A.det = a) (hAJ : A * J = a • 1) :
    (Matrix.fromBlocks A b c (fun _ _ => d)).det = a*d - (c*J*b) 0 0 := by
  let f := Int.castRingHom ℚ
  have hdet' : (A.map f).det = (a : ℚ) := by
    change (A.map (fun z : ℤ => (z : ℚ))).det = _
    rw [← Int.cast_det, hdet]
  have hAJ' : A.map f * J.map f = (a : ℚ) • 1 := by
    rw [← Matrix.map_mul, hAJ]
    exact rat_smul_one a
  have h := det_border_field (A.map f) (J.map f) (b.map f) (c.map f)
    (d : ℚ) (a : ℚ) (by exact_mod_cast ha) hdet' hAJ'
  have he : Matrix.fromBlocks (A.map f) (b.map f) (c.map f) (fun _ _ => (d : ℚ)) =
      (Matrix.fromBlocks A b c (fun _ _ => d)).map f := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  have hp : c.map f * J.map f * b.map f = (c*J*b).map f := by
    rw [Matrix.map_mul, Matrix.map_mul]
  rw [he, hp] at h
  change ((Matrix.fromBlocks A b c (fun _ _ => d)).map (fun z : ℤ => (z : ℚ))).det =
    (a : ℚ) * (d : ℚ) - ((c*J*b) 0 0 : ℚ) at h
  rw [← Int.cast_det] at h
  exact_mod_cast h

def gram {k N : ℕ} (P : Matrix (Fin k) (Fin N) ℤ) : Matrix (Fin k) (Fin k) ℤ :=
  P * P.transpose

def cross {k N : ℕ} (P : Matrix (Fin k) (Fin N) ℤ) (v : Fin N → ℤ) : Fin k → ℤ :=
  fun i => ∑ j, P i j * v j

theorem det_gram_snoc {k N : ℕ} (P : Matrix (Fin k) (Fin N) ℤ)
    (v : Fin N → ℤ) (hv : ∀ j, v j = 1 ∨ v j = -1)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ) (ha : a ≠ 0)
    (hdet : (gram P).det = a) (hAJ : gram P * J = a • 1) :
    (gram (Fin.snoc P v)).det = (N : ℤ)*a -
      ∑ i, ∑ j, cross P v i * J i j * cross P v j := by
  let e : Fin k ⊕ Fin 1 ≃ Fin (k+1) := finSumFinEquiv
  let b : Matrix (Fin k) (Fin 1) ℤ := fun i _ => cross P v i
  let c : Matrix (Fin 1) (Fin k) ℤ := fun _ j => cross P v j
  have hs : ∀ j, v j * v j = 1 := by
    intro j
    rcases hv j with h | h <;> rw [h] <;> norm_num
  have hcast : ∀ i : Fin k, Fin.castAdd 1 i = i.castSucc := fun _ => rfl
  have hlast : Fin.natAdd k (0 : Fin 1) = Fin.last k := rfl
  have he : (gram (Fin.snoc P v)).submatrix e e =
      Matrix.fromBlocks (gram P) b c (fun _ _ => (N : ℤ)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [gram, Matrix.mul_apply, e, hcast]
    · fin_cases j
      simp [gram, Matrix.mul_apply, e, b, cross, hcast, hlast]
    · fin_cases i
      simp [gram, Matrix.mul_apply, e, c, cross, mul_comm, hcast, hlast]
    · fin_cases i; fin_cases j
      simp [gram, Matrix.mul_apply, e, hs, hlast]
  have h := det_border_int (gram P) J b c (N : ℤ) a ha hdet hAJ
  rw [← he, Matrix.det_submatrix_equiv_self] at h
  rw [h]
  simp only [Matrix.mul_apply, c, b, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

end MainTheory.GramSchurCertificate
