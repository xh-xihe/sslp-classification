import Mathlib

/-!
Kernel-friendly exact rank certificates.  Integer identities certify a selected
row basis, its right inverse and the expression of every original row in that
basis.  This avoids expanding determinants of the 23-row moment matrices.
-/

namespace MainTheory.IntegerMatrixRankCertificate

open scoped Matrix

theorem rank_eq_of_row_factorization {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (rows : Fin r → Fin m)
    (R : Matrix (Fin n) (Fin r) ℝ) (E : Matrix (Fin m) (Fin r) ℝ)
    (hR : A.submatrix rows id * R = 1)
    (hE : E * A.submatrix rows id = A) : A.rank = r := by
  have hl := Matrix.rank_mul_le_left (A.submatrix rows id) R
  rw [hR, Matrix.rank_one] at hl
  have hs := Matrix.rank_submatrix_le rows (Equiv.refl (Fin n)) A
  have hu := Matrix.rank_mul_le_right E (A.submatrix rows id)
  rw [hE] at hu
  have hb := Matrix.rank_le_height (A.submatrix rows id)
  norm_num at hl hb
  have hs' : (A.submatrix rows id).rank ≤ A.rank := hs
  omega

theorem map_scaled_product {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (B : Matrix (Fin n) (Fin r) ℤ)
    (C : Matrix (Fin m) (Fin r) ℤ) (d : ℕ) (h : A * B = d • C) :
    A.map (Int.castRingHom ℝ) * B.map (Int.castRingHom ℝ) =
      (d : ℝ) • C.map (Int.castRingHom ℝ) := by
  rw [← Matrix.map_mul, h]
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

theorem rank_eq_of_integer_identities {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (rows : Fin r → Fin m)
    (R : Matrix (Fin n) (Fin r) ℤ) (E : Matrix (Fin m) (Fin r) ℤ)
    (s d : ℕ) (hs : 0 < s) (hd : 0 < d)
    (hR : A.submatrix rows id * R = s • (1 : Matrix (Fin r) (Fin r) ℤ))
    (hE : E * A.submatrix rows id = d • A) :
    (A.map (Int.castRingHom ℝ)).rank = r := by
  let AR := A.map (Int.castRingHom ℝ)
  let RR := (1 / (s : ℝ)) • R.map (Int.castRingHom ℝ)
  let ER := (1 / (d : ℝ)) • E.map (Int.castRingHom ℝ)
  apply rank_eq_of_row_factorization AR rows RR ER
  · have hmap := map_scaled_product _ _ _ s hR
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
    change AR.submatrix rows id * ((1 / (s : ℝ)) • R.map (Int.castRingHom ℝ)) = 1
    rw [Matrix.mul_smul]
    change (1 / (s : ℝ)) •
      ((A.submatrix rows id).map (Int.castRingHom ℝ) * R.map (Int.castRingHom ℝ)) = 1
    rw [hmap]
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.smul_apply, Matrix.one_apply, hij, hsR]
  · have hmap := map_scaled_product _ _ _ d hE
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
    change ((1 / (d : ℝ)) • E.map (Int.castRingHom ℝ)) * AR.submatrix rows id = AR
    rw [Matrix.smul_mul]
    change (1 / (d : ℝ)) •
      (E.map (Int.castRingHom ℝ) * (A.submatrix rows id).map (Int.castRingHom ℝ)) = AR
    rw [hmap]
    ext i j
    simp [AR, Matrix.smul_apply, Matrix.map_apply, hdR]

theorem rank_submatrix_le_any {m n r s : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (rows : Fin r → Fin m) (cols : Fin s → Fin n) :
    (A.submatrix rows cols).rank ≤ A.rank := by
  have hr := Matrix.rank_submatrix_le rows (Equiv.refl (Fin n)) A
  have hc := Matrix.rank_submatrix_le cols (Equiv.refl (Fin r)) (A.submatrix rows id).transpose
  have he : ((A.submatrix rows id).transpose.submatrix cols (Equiv.refl (Fin r))) =
      (A.submatrix rows cols).transpose := rfl
  rw [he, Matrix.rank_transpose, Matrix.rank_transpose] at hc
  exact hc.trans hr

theorem rank_eq_of_integer_minor_and_expansion {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (rows : Fin r → Fin m) (cols : Fin r → Fin n)
    (R : Matrix (Fin r) (Fin r) ℤ) (E : Matrix (Fin m) (Fin r) ℤ)
    (s d : ℕ) (hs : 0 < s) (hd : 0 < d)
    (hR : A.submatrix rows cols * R = s • (1 : Matrix (Fin r) (Fin r) ℤ))
    (hE : E * A.submatrix rows id = d • A) :
    (A.map (Int.castRingHom ℝ)).rank = r := by
  let AR := A.map (Int.castRingHom ℝ)
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hminor : AR.submatrix rows cols * ((1 / (s : ℝ)) • R.map (Int.castRingHom ℝ)) = 1 := by
    rw [Matrix.mul_smul]
    change (1 / (s : ℝ)) •
      ((A.submatrix rows cols).map (Int.castRingHom ℝ) * R.map (Int.castRingHom ℝ)) = 1
    rw [map_scaled_product _ _ _ s hR]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.smul_apply, Matrix.one_apply, hij, hsR]
  have he : ((1 / (d : ℝ)) • E.map (Int.castRingHom ℝ)) * AR.submatrix rows id = AR := by
    rw [Matrix.smul_mul]
    change (1 / (d : ℝ)) •
      (E.map (Int.castRingHom ℝ) * (A.submatrix rows id).map (Int.castRingHom ℝ)) = AR
    rw [map_scaled_product _ _ _ d hE]
    ext i j
    simp [AR, Matrix.smul_apply, Matrix.map_apply, hdR]
  have hl := Matrix.rank_mul_le_left (AR.submatrix rows cols)
    ((1 / (s : ℝ)) • R.map (Int.castRingHom ℝ))
  rw [hminor, Matrix.rank_one] at hl
  have hsub := rank_submatrix_le_any AR rows cols
  have hu := Matrix.rank_mul_le_right ((1 / (d : ℝ)) • E.map (Int.castRingHom ℝ))
    (AR.submatrix rows id)
  rw [he] at hu
  have hb := Matrix.rank_le_height (AR.submatrix rows id)
  norm_num at hl hb
  change AR.rank = r
  omega

end MainTheory.IntegerMatrixRankCertificate
