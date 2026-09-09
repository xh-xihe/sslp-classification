import MainTheory.BinaryBeta

namespace MainTheory.IntegerInverseBound

open Matrix SharpClearing
open scoped BigOperators

variable {s : Type*} [Fintype s] [DecidableEq s]

theorem rat_det_ne_zero (C : Matrix s s ℤ) (hC : C.det ≠ 0) :
    (ratMatrix C).det ≠ 0 := by
  have h : (ratMatrix C).det = (C.det : ℚ) := (Int.cast_det C).symm
  rw [h]
  exact_mod_cast hC

omit [DecidableEq s] in
theorem rat_mul (A B : Matrix s s ℤ) : ratMatrix (A * B) = ratMatrix A * ratMatrix B :=
  Matrix.map_mul

omit [Fintype s] in
theorem rat_smul_one (q : ℤ) : ratMatrix (q • (1 : Matrix s s ℤ)) =
    (q : ℚ) • (1 : Matrix s s ℚ) := by
  ext i j
  change ((q * (if i = j then 1 else 0) : ℤ) : ℚ) =
    (q : ℚ) * (if i = j then 1 else 0)
  by_cases h : i = j <;> simp [h]

theorem universallyClears_of_integer_inverse (C B : Matrix s s ℤ)
    (hC : C.det ≠ 0) (q : ℕ) (hB : C * B = (q : ℤ) • 1) :
    UniversallyClears C q := by
  have hm : ratMatrix C * ratMatrix B = (q : ℚ) • 1 := by
    rw [← rat_mul, hB, rat_smul_one]
    norm_cast
  have hi := congrArg (fun M => (ratMatrix C)⁻¹ * M) hm
  dsimp only at hi
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (rat_det_ne_zero C hC)), Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one] at hi
  intro h
  refine ⟨B.mulVec h, fun i => ?_⟩
  have he := congrArg (fun M => M.mulVec (fun j => (h j : ℚ)) i) hi
  dsimp only at he
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul] at he
  rw [← he]
  change (∑ j, (B i j : ℚ) * (h j : ℚ)) = ((∑ j, B i j * h j : ℤ) : ℚ)
  push_cast
  rfl

theorem inverseDenominator_dvd_of_integer_inverse (C B : Matrix s s ℤ)
    (hC : C.det ≠ 0) (q : ℕ) (hq : 0 < q) (hB : C * B = (q : ℤ) • 1) :
    inverseDenominator C ∣ q :=
  inverseDenominator_dvd_of_universallyClears C q hq
    (universallyClears_of_integer_inverse C B hC q hB)

theorem inverseDenominator_le_of_integer_inverse (C B : Matrix s s ℤ)
    (hC : C.det ≠ 0) (q : ℕ) (hq : 0 < q) (hB : C * B = (q : ℤ) • 1) :
    inverseDenominator C ≤ q :=
  Nat.le_of_dvd hq (inverseDenominator_dvd_of_integer_inverse C B hC q hq hB)

noncomputable def sharpInverse (C : Matrix s s ℤ) : Matrix s s ℤ :=
  fun i j => clearedInverseEntry C i j

theorem rat_sharpInverse (C : Matrix s s ℤ) :
    ratMatrix (sharpInverse C) = (inverseDenominator C : ℚ) • (ratMatrix C)⁻¹ := by
  ext i j
  exact (clearedInverseEntry_spec C i j).symm

theorem mul_sharpInverse (C : Matrix s s ℤ) (hC : C.det ≠ 0) :
    C * sharpInverse C = (inverseDenominator C : ℤ) • 1 := by
  have h : ratMatrix (C * sharpInverse C) =
      ratMatrix ((inverseDenominator C : ℤ) • 1) := by
    rw [rat_mul, rat_sharpInverse, Matrix.mul_smul, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (rat_det_ne_zero C hC)), rat_smul_one]
    norm_cast
  ext i j
  have he := congrArg (fun M => M i j) h
  change (((C * sharpInverse C) i j : ℤ) : ℚ) =
    ((((inverseDenominator C : ℤ) • (1 : Matrix s s ℤ)) i j : ℤ) : ℚ) at he
  exact_mod_cast he

theorem pullback_inverse {t : Type*} [Fintype t] [DecidableEq t]
    (C B : Matrix s s ℤ) (q : ℤ) (hB : C * B = q • 1) (e : t ≃ s) :
    C.submatrix e e * B.submatrix e e = q • (1 : Matrix t t ℤ) := by
  rw [Matrix.submatrix_mul_equiv, hB]
  ext i j
  change q * (if e i = e j then 1 else 0) = q * (if i = j then 1 else 0)
  simp only [e.injective.eq_iff]

theorem inverseDenominator_le_pad {s N : ℕ} (hsN : s ≤ N)
    (C : Matrix (Fin s) (Fin s) ℤ) (hC : C.det ≠ 0) :
    inverseDenominator C ≤ inverseDenominator (BinaryBeta.padMatrix hsN C) := by
  let D := BinaryBeta.padMatrix hsN C
  have hD : D.det ≠ 0 := by simpa [D, BinaryBeta.padMatrix_det] using hC
  let e := BinaryBeta.padEquiv hsN
  let J := (sharpInverse D).submatrix e e
  have h := pullback_inverse D (sharpInverse D) (inverseDenominator D)
    (mul_sharpInverse D hD) e
  have he : D.submatrix e e = Matrix.fromBlocks C 0 0 1 := by
    change ((Matrix.fromBlocks C 0 0 1).submatrix e.symm e.symm).submatrix e e = _
    simp only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
  rw [he] at h
  have hb : C * J.submatrix Sum.inl Sum.inl = (inverseDenominator D : ℤ) • 1 := by
    ext i j
    have hij := congrArg (fun M => M (Sum.inl i) (Sum.inl j)) h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, J, Matrix.one_apply] using hij
  exact inverseDenominator_le_of_integer_inverse C _ hC _ (inverseDenominator_pos D) hb

theorem betaBound_of_fixedSize_inverseDenominator_bound {N B : ℕ}
    (hbound : ∀ C : Matrix (Fin N) (Fin N) ℤ,
      BinaryBeta.IsZeroOne C → C.det ≠ 0 → inverseDenominator C ≤ B) :
    BinaryBeta.BetaBound N B := by
  intro s _ hsN C hbinary hdet
  exact (inverseDenominator_le_pad hsN C hdet).trans
    (hbound _ (BinaryBeta.padMatrix_isZeroOne hsN C hbinary)
      (by simpa [BinaryBeta.padMatrix_det] using hdet))

end MainTheory.IntegerInverseBound
