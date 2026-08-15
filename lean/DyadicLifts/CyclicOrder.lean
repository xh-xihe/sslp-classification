import DyadicLifts.SSResidue
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The induced cyclic diagonal and the binary-dihedral relations

This module formalizes `dyadic_theorem_lean.tex`, Sections 3–4:

* `Definition (Projective and determinant-one cyclic orders)` — `D_m`, `R_m`.
* `Lemma (Order of the induced cyclic diagonal)` — `D_m^m = I`, `R_m^{2m} = I`,
  and `R_m^m = -I`.
* `Definition / Lemma (Binary-dihedral matrix relations)` — with `J = iX`,
  `J² = R_m^m = -I` and `J R_m J⁻¹ = R_m⁻¹`.
-/

open scoped BigOperators
open ComplexConjugate Matrix

namespace DyadicLifts

/-- The projective logical diagonal `D_m = diag(1, e^{-2πi/m})`. -/
noncomputable def Dm (m : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / m))]

/-- The determinant-one representative `R_m = diag(e^{πi/m}, e^{-πi/m})`. -/
noncomputable def Rm (m : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![Complex.exp ((Real.pi : ℂ) * Complex.I / m),
                    Complex.exp (-((Real.pi : ℂ) * Complex.I / m))]

/-- `R_m⁻¹ = diag(e^{-πi/m}, e^{πi/m})`. -/
noncomputable def Rminv (m : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![Complex.exp (-((Real.pi : ℂ) * Complex.I / m)),
                    Complex.exp ((Real.pi : ℂ) * Complex.I / m)]

/-- The order-four lift of the logical bit flip, `J = iX`. -/
noncomputable def Jmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]

/-! ### Root-of-unity facts for the half-angle `πi/m` -/

lemma exp_half_pow_m {m : ℕ} (hm : m ≠ 0) :
    (Complex.exp ((Real.pi : ℂ) * Complex.I / m)) ^ m = -1 := by
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [← Complex.exp_nat_mul,
    show (m : ℂ) * ((Real.pi : ℂ) * Complex.I / m) = (Real.pi : ℂ) * Complex.I from by field_simp]
  exact Complex.exp_pi_mul_I

lemma exp_neg_half_pow_m {m : ℕ} (hm : m ≠ 0) :
    (Complex.exp (-((Real.pi : ℂ) * Complex.I / m))) ^ m = -1 := by
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [← Complex.exp_nat_mul,
    show (m : ℂ) * (-((Real.pi : ℂ) * Complex.I / m)) = -((Real.pi : ℂ) * Complex.I) from by
      field_simp]
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

lemma exp_half_pow_2m {m : ℕ} (hm : m ≠ 0) :
    (Complex.exp ((Real.pi : ℂ) * Complex.I / m)) ^ (2 * m) = 1 := by
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [← Complex.exp_nat_mul,
    show ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / m) = 2 * (Real.pi : ℂ) * Complex.I from by
      push_cast; field_simp]
  exact Complex.exp_two_pi_mul_I

lemma exp_neg_half_pow_2m {m : ℕ} (hm : m ≠ 0) :
    (Complex.exp (-((Real.pi : ℂ) * Complex.I / m))) ^ (2 * m) = 1 := by
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [← Complex.exp_nat_mul,
    show ((2 * m : ℕ) : ℂ) * (-((Real.pi : ℂ) * Complex.I / m)) = -(2 * (Real.pi : ℂ) * Complex.I)
      from by push_cast; field_simp]
  rw [Complex.exp_neg, Complex.exp_two_pi_mul_I]; norm_num

lemma exp_half_mul_neg {m : ℕ} :
    Complex.exp ((Real.pi : ℂ) * Complex.I / m) * Complex.exp (-((Real.pi : ℂ) * Complex.I / m))
      = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

lemma exp_neg_half_mul {m : ℕ} :
    Complex.exp (-((Real.pi : ℂ) * Complex.I / m)) * Complex.exp ((Real.pi : ℂ) * Complex.I / m)
      = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-! ### Orders -/

/-- Pointwise power of a length-two vector. -/
lemma vec2_pow (a b : ℂ) (k : ℕ) : (![a, b] : Fin 2 → ℂ) ^ k = ![a ^ k, b ^ k] := by
  funext i; fin_cases i <;> simp

/-- `diag(1,1) = 1` and similar: identify a constant-one diagonal with the identity. -/
lemma diagonal_one_one : Matrix.diagonal (![1, 1] : Fin 2 → ℂ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

/-- **`D_m^m = I`:** the projective diagonal order divides `m`. -/
lemma Dm_pow_m {m : ℕ} (hm : m ≠ 0) : Dm m ^ m = 1 := by
  have h : (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / m))) ^ m = 1 := by
    have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    rw [← Complex.exp_nat_mul,
      show (m : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I / m)) = -(2 * (Real.pi : ℂ) * Complex.I) from by
        field_simp]
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I]; norm_num
  rw [Dm, Matrix.diagonal_pow, vec2_pow, one_pow, h, diagonal_one_one]

/-- **`R_m^{2m} = I`:** the determinant-one cyclic order divides `2m`. -/
lemma Rm_pow_two_m {m : ℕ} (hm : m ≠ 0) : Rm m ^ (2 * m) = 1 := by
  rw [Rm, Matrix.diagonal_pow, vec2_pow, exp_half_pow_2m hm, exp_neg_half_pow_2m hm,
    diagonal_one_one]

/-- **`R_m^m = -I`:** in particular `R_m^m ≠ I`, so the order does not divide `m`. -/
lemma Rm_pow_m {m : ℕ} (hm : m ≠ 0) : Rm m ^ m = -1 := by
  rw [Rm, Matrix.diagonal_pow, vec2_pow, exp_half_pow_m hm, exp_neg_half_pow_m hm]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

/-! ### Exact orders (minimality)

The lemmas above give `Dm^m = 1`, `Rm^{2m} = 1`, `Rm^m = -1`, i.e. the orders
*divide* `m` / `2m`.  Here we pin the **exact** orders (`lem:cyclic-order`):
`e^{πi/m} = e^{2πi/(2m)}` is a *primitive* `2m`-th root of unity and `e^{-2πi/m}`
a *primitive* `m`-th root, so the diagonals first return to the identity exactly
at `m` (projectively) / `2m`.  These are the facts that make "each dyadic lift
doubles the diagonal order" a genuine statement rather than only an upper bound. -/

/-- `e^{πi/m} = e^{2πi/(2m)}` is a primitive `2m`-th root of unity. -/
lemma isPrimitiveRoot_exp_half {m : ℕ} (hm : 0 < m) :
    IsPrimitiveRoot (Complex.exp ((Real.pi : ℂ) * Complex.I / m)) (2 * m) := by
  have h := Complex.isPrimitiveRoot_exp (2 * m) (by positivity)
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have he : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 * m : ℕ) : ℂ))
      = Complex.exp ((Real.pi : ℂ) * Complex.I / m) := by
    congr 1
    have h2m : ((2 * m : ℕ) : ℂ) = 2 * (m : ℂ) := by push_cast; ring
    rw [h2m]; field_simp
  rwa [he] at h

/-- `e^{-2πi/m}` is a primitive `m`-th root of unity. -/
lemma isPrimitiveRoot_exp_neg_two {m : ℕ} (hm : 0 < m) :
    IsPrimitiveRoot (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / m))) m := by
  have h := (Complex.isPrimitiveRoot_exp m hm.ne').inv
  have he : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / m))⁻¹
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / m)) := by
    rw [← Complex.exp_neg]
  rwa [he] at h

/-- Scalar root-of-unity power test for the half-angle `πi/m`. -/
lemma exp_half_pow_eq_one_iff {m : ℕ} (hm : 0 < m) (d : ℕ) :
    (Complex.exp ((Real.pi : ℂ) * Complex.I / m)) ^ d = 1 ↔ 2 * m ∣ d :=
  (isPrimitiveRoot_exp_half hm).pow_eq_one_iff_dvd d

/-- **`R_m^d = I ↔ 2m ∣ d`:** the determinant-one diagonal `R_m` has *exact* order `2m`. -/
lemma Rm_pow_eq_one_iff {m : ℕ} (hm : 0 < m) (d : ℕ) : Rm m ^ d = 1 ↔ 2 * m ∣ d := by
  rw [Rm, Matrix.diagonal_pow, vec2_pow]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.one_apply_eq] at h00
    exact (exp_half_pow_eq_one_iff hm d).mp h00
  · intro h
    have h1 : (Complex.exp ((Real.pi : ℂ) * Complex.I / m)) ^ d = 1 :=
      (exp_half_pow_eq_one_iff hm d).mpr h
    have h2 : (Complex.exp (-((Real.pi : ℂ) * Complex.I / m))) ^ d = 1 := by
      rw [Complex.exp_neg, inv_pow, h1, inv_one]
    rw [h1, h2, diagonal_one_one]

/-- **`orderOf (R_m) = 2m`.** -/
theorem orderOf_Rm {m : ℕ} (hm : 0 < m) : orderOf (Rm m) = 2 * m := by
  have hdvd1 : orderOf (Rm m) ∣ 2 * m := orderOf_dvd_of_pow_eq_one (Rm_pow_two_m hm.ne')
  have hdvd2 : 2 * m ∣ orderOf (Rm m) :=
    (Rm_pow_eq_one_iff hm _).mp (pow_orderOf_eq_one (Rm m))
  exact Nat.dvd_antisymm hdvd1 hdvd2

/-- **`D_m^t = I ↔ m ∣ t`:** the projective diagonal returns to the identity exactly
at multiples of `m`. -/
lemma Dm_pow_eq_one_iff {m : ℕ} (hm : 0 < m) (t : ℕ) : Dm m ^ t = 1 ↔ m ∣ t := by
  rw [Dm, Matrix.diagonal_pow, vec2_pow]
  constructor
  · intro h
    have h11 := congrFun (congrFun h 1) 1
    simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply_eq] at h11
    exact ((isPrimitiveRoot_exp_neg_two hm).pow_eq_one_iff_dvd t).mp h11
  · intro h
    have hω : (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / m))) ^ t = 1 :=
      ((isPrimitiveRoot_exp_neg_two hm).pow_eq_one_iff_dvd t).mpr h
    rw [one_pow, hω, diagonal_one_one]

/-- **Projective (mod-scalar) order of `D_m` is exactly `m`:** `D_m^t` is a scalar
matrix iff `m ∣ t`.  This is the faithful "exact order `m` modulo scalars" claim. -/
lemma Dm_pow_smul_one_iff {m : ℕ} (hm : 0 < m) (t : ℕ) :
    (∃ c : ℂ, Dm m ^ t = c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ↔ m ∣ t := by
  constructor
  · rintro ⟨c, hc⟩
    rw [Dm, Matrix.diagonal_pow, vec2_pow] at hc
    have h00 := congrFun (congrFun hc 0) 0
    have h11 := congrFun (congrFun hc 1) 1
    simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      one_pow] at h00 h11
    have hω : (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / m))) ^ t = 1 := by
      rw [h11, ← h00]
    exact ((isPrimitiveRoot_exp_neg_two hm).pow_eq_one_iff_dvd t).mp hω
  · intro h
    exact ⟨1, by rw [(Dm_pow_eq_one_iff hm t).mpr h, one_smul]⟩

/-! ### Binary-dihedral relations -/

/-- **`J² = -I`.** -/
lemma Jmat_sq : Jmat * Jmat = -1 := by
  rw [Jmat]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Complex.I_mul_I]

/-- `R_m · R_m⁻¹ = I`. -/
lemma Rm_mul_Rminv {m : ℕ} : Rm m * Rminv m = 1 := by
  rw [Rm, Rminv, Matrix.diagonal_mul_diagonal]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, Pi.mul_apply,
      exp_half_mul_neg, exp_neg_half_mul]

/-- `J · R_m = R_m⁻¹ · J`: conjugation by `J` inverts the diagonal. -/
lemma Jmat_Rm_eq {m : ℕ} : Jmat * Rm m = Rminv m * Jmat := by
  rw [Jmat, Rm, Rminv]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;> ring

/-- **`J R_m J⁻¹ = R_m⁻¹`** (the binary-dihedral conjugation relation). -/
lemma Jmat_conj_Rm {m : ℕ} : Jmat * Rm m * Jmat⁻¹ = Rminv m := by
  have hJinv : Jmat⁻¹ = -Jmat := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_neg, Jmat_sq, neg_neg]
  calc Jmat * Rm m * Jmat⁻¹
      = Jmat * Rm m * (-Jmat) := by rw [hJinv]
    _ = -(Jmat * Rm m * Jmat) := by rw [Matrix.mul_neg]
    _ = -(Rminv m * Jmat * Jmat) := by rw [Jmat_Rm_eq]
    _ = -(Rminv m * (Jmat * Jmat)) := by rw [Matrix.mul_assoc]
    _ = -(Rminv m * (-1)) := by rw [Jmat_sq]
    _ = Rminv m := by rw [Matrix.mul_neg, Matrix.mul_one, neg_neg]

end DyadicLifts
