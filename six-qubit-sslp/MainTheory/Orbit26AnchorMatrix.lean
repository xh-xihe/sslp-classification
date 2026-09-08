import MainTheory.Orbit26AnchorSingular

/-!
# `lem:q4o26anchorsingular`: the matrix layer

`MainTheory.Orbit26AnchorSingular` proves the two scalar cores of the
manuscript's orbit-26 anchor argument.  This file supplies the `2 x 2` matrix
algebra between the manuscript's displayed equations and those cores, and
concludes the lemma.
-/

namespace MainTheory.Orbit26

open scoped Matrix BigOperators
open SixQubit.Block26
open ComplexConjugate

/-- The `2 x 2` blocks of the manuscript. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The manuscript's `J`: the symmetric antidiagonal form. -/
noncomputable def Jmat : M2 := !![0, 1; 1, 0]

/-- Entrywise conjugation, the manuscript's overline. -/
noncomputable def cj (A : M2) : M2 := Aᴴᵀ

@[simp] theorem cj_apply (A : M2) (i j : Fin 2) : cj A i j = conj (A i j) := rfl

@[simp] theorem cj_transpose (A : M2) : (cj A)ᵀ = Aᴴ := rfl

/-- The manuscript's `F_{gh}`. -/
noncomputable def Fmat (A B : M2) : M2 := A * Jmat * Bᵀ + B * Jmat * Aᵀ

/-! ## The quadratic form of `F`

`w^T F_{gh} w = 2 J(w^T A, w^T B)`, which is how `F_{gh} = 0` and
`F_{gh} d = 0` both feed `lem:q4o26Jorth`. -/

theorem jform_of_qform_zero (A B : M2) (w : Fin 2 → ℂ)
    (h : w ⬝ᵥ (Fmat A B) *ᵥ w = 0) :
    Jform ((w ᵥ* A) 0) ((w ᵥ* A) 1) ((w ᵥ* B) 0) ((w ᵥ* B) 1) = 0 := by
  simp only [Fmat, Jmat, Jform, Matrix.mulVec, Matrix.vecMul, dotProduct,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.of_apply] at h ⊢
  linear_combination h / 2

theorem jform_of_F_eq_zero (A B : M2) (hF : Fmat A B = 0) (w : Fin 2 → ℂ) :
    Jform ((w ᵥ* A) 0) ((w ᵥ* A) 1) ((w ᵥ* B) 0) ((w ᵥ* B) 1) = 0 :=
  jform_of_qform_zero A B w (by rw [hF]; simp)

theorem jform_of_F_mulVec_zero (A B : M2) (w : Fin 2 → ℂ)
    (hF : (Fmat A B) *ᵥ w = 0) :
    Jform ((w ᵥ* A) 0) ((w ᵥ* A) 1) ((w ᵥ* B) 0) ((w ᵥ* B) 1) = 0 :=
  jform_of_qform_zero A B w (by rw [hF]; simp)

/-! ## Solving the anchor equation -/

/-- **`eq:q4o26commonM`.**  When `C_3` is invertible, `eq:q4o26anchormatrix`
solves for the top block: `D_g = -M conj(C_g)` with `M = (C_3^dagger)^{-1}
D_3^T`, one and the same `M` for every group. -/
theorem anchor_solve {C3 D3 Cg Dg : M2} (h3 : IsUnit C3.det)
    (h : C3ᴴ * Dg + (Cgᴴ * D3)ᵀ = 0) :
    Dg = -(((C3ᴴ)⁻¹ * D3ᵀ) * cj Cg) := by
  have h3' : IsUnit (C3ᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact h3.star
  have hmul : C3ᴴ * Dg = -(D3ᵀ * cj Cg) := by
    have := congrArg (fun X => X - (Cgᴴ * D3)ᵀ) h
    simp only [add_sub_cancel_right, zero_sub] at this
    rw [this, Matrix.transpose_mul]
    rfl
  calc Dg = ((C3ᴴ)⁻¹ * C3ᴴ) * Dg := by rw [Matrix.nonsing_inv_mul _ h3', Matrix.one_mul]
    _ = (C3ᴴ)⁻¹ * (C3ᴴ * Dg) := by rw [Matrix.mul_assoc]
    _ = -(((C3ᴴ)⁻¹ * D3ᵀ) * cj Cg) := by rw [hmul, Matrix.mul_neg, Matrix.mul_assoc]

/-- **`eq:q4o26FM`.**  Substituting `eq:q4o26commonM` into
`eq:q4o26outermatrix` cancels the top blocks and leaves `F_{gh} M^T = 0`. -/
theorem F_mul_transpose {M Cg Ch Dg Dh : M2}
    (hg : Dg = -(M * cj Cg)) (hh : Dh = -(M * cj Ch))
    (houter : cj Cg * Jmat * Dhᵀ + cj Ch * Jmat * Dgᵀ = 0) :
    Fmat (cj Cg) (cj Ch) * Mᵀ = 0 := by
  have hgT : Dgᵀ = -((cj Cg)ᵀ * Mᵀ) := by
    rw [hg, Matrix.transpose_neg, Matrix.transpose_mul]
  have hhT : Dhᵀ = -((cj Ch)ᵀ * Mᵀ) := by
    rw [hh, Matrix.transpose_neg, Matrix.transpose_mul]
  rw [hgT, hhT] at houter
  have : -(Fmat (cj Cg) (cj Ch) * Mᵀ) = 0 := by
    rw [← houter, Fmat]
    simp only [Matrix.mul_neg, Matrix.add_mul, Matrix.mul_assoc, neg_add]
  simpa using this


/-! ## Cancelling `M^T`

Two ways, matching the manuscript's two branches: when `D_3` is invertible so
is `M`, and `F_{gh}` itself vanishes; when `D_3` has rank one, `M^T` has image
the line spanned by `d`, and `F_{gh}` kills `d`. -/

/-- `M = (C_3^dagger)^{-1} D_3^T` is invertible when both anchor blocks are. -/
theorem isUnit_det_M {C3 D3 : M2} (h3 : IsUnit C3.det) (hD : IsUnit D3.det) :
    IsUnit (((C3ᴴ)⁻¹ * D3ᵀ).det) := by
  have h3' : IsUnit (C3ᴴ).det := by rw [Matrix.det_conjTranspose]; exact h3.star
  rw [Matrix.det_mul]
  exact (Matrix.isUnit_nonsing_inv_det _ h3').mul (by rwa [Matrix.det_transpose])

/-- **The invertible branch.**  `F_{gh} M^T = 0` with `M` invertible gives
`F_{gh} = 0`. -/
theorem F_eq_zero_of_isUnit {A B M : M2} (hM : IsUnit M.det)
    (h : Fmat A B * Mᵀ = 0) : Fmat A B = 0 := by
  have hMT : IsUnit (Mᵀ).det := by rwa [Matrix.det_transpose]
  calc Fmat A B = Fmat A B * (Mᵀ * (Mᵀ)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ hMT, Matrix.mul_one]
    _ = (Fmat A B * Mᵀ) * (Mᵀ)⁻¹ := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.zero_mul]

/-- Multiplying a matrix into a rank-one outer product. -/
theorem mul_vecMulVec (A : M2) (v w : Fin 2 → ℂ) :
    A * Matrix.vecMulVec v w = Matrix.vecMulVec (A *ᵥ v) w := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- An outer product with a nonzero right factor vanishes only if the left
factor does. -/
theorem eq_zero_of_vecMulVec_eq_zero {u w : Fin 2 → ℂ} (hw : w ≠ 0)
    (h : Matrix.vecMulVec u w = 0) : u = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hw (funext hc)
  funext i
  have := congrFun (congrFun h i) j
  simp only [Matrix.vecMulVec_apply, Matrix.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_right hj

/-- **The rank-one branch.**  With `C_3` invertible and
`D_3 D_3^dagger = (1/4)|d><d|` -- the manuscript's `eq:q4o26D3rankone` -- the
image of `M^T` is the line spanned by `d`, so `F_{gh} M^T = 0` gives
`F_{gh} d = 0`. -/
theorem F_mulVec_eq_zero_of_rankOne {A B C3 D3 : M2} {d : Fin 2 → ℂ}
    (h3 : IsUnit C3.det) (hd : d ≠ 0)
    (hD3 : D3 * D3ᴴ = (1/4 : ℂ) • Matrix.vecMulVec d (star d))
    (h : Fmat A B * ((C3ᴴ)⁻¹ * D3ᵀ)ᵀ = 0) :
    (Fmat A B) *ᵥ d = 0 := by
  have h3' : IsUnit (C3ᴴ).det := by rw [Matrix.det_conjTranspose]; exact h3.star
  have hX : IsUnit ((((C3ᴴ)⁻¹)ᵀ).det) := by
    rw [Matrix.det_transpose]; exact Matrix.isUnit_nonsing_inv_det _ h3'
  -- `M^T = D_3 X` with `X` invertible, so `F D_3 = 0`
  have hMT : ((C3ᴴ)⁻¹ * D3ᵀ)ᵀ = D3 * ((C3ᴴ)⁻¹)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hMT, ← Matrix.mul_assoc] at h
  have hFD : Fmat A B * D3 = 0 := by
    calc Fmat A B * D3 = (Fmat A B * D3) * (((C3ᴴ)⁻¹)ᵀ * (((C3ᴴ)⁻¹)ᵀ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]
      _ = (Fmat A B * D3 * ((C3ᴴ)⁻¹)ᵀ) * (((C3ᴴ)⁻¹)ᵀ)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.zero_mul]
  -- push through `D_3 D_3^dagger`
  have hstar : star d ≠ 0 := by
    intro hc
    exact hd (by simpa using congrArg star hc)
  refine eq_zero_of_vecMulVec_eq_zero hstar ?_
  rw [← mul_vecMulVec]
  have : Fmat A B * (D3 * D3ᴴ) = 0 := by rw [← Matrix.mul_assoc, hFD, Matrix.zero_mul]
  rw [hD3, Matrix.mul_smul] at this
  have h4 : (1/4 : ℂ) ≠ 0 := by norm_num
  exact (smul_eq_zero.1 this).resolve_left h4


/-! ## The norm bookkeeping of `eq:q4o26rnormlarge` -/

/-- The squared norm of the manuscript's row `r = d^T conj(A)` is the
quadratic form of `A A^dagger` at `d`. -/
theorem rowNormSq_eq (A : M2) (d : Fin 2 → ℂ) :
    ((Complex.normSq ((d ᵥ* cj A) 0) + Complex.normSq ((d ᵥ* cj A) 1) : ℝ) : ℂ)
      = star d ⬝ᵥ (A * Aᴴ) *ᵥ d := by
  simp only [Complex.ofReal_add, Complex.normSq_eq_conj_mul_self, Matrix.vecMul,
    dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply,
    cj_apply, Pi.star_apply, Fin.sum_univ_two, map_add, map_mul, Complex.conj_conj,
    RCLike.star_def]
  ring

/-- For a unit vector, the quadratic form of `|d><d|` at `d` is one. -/
theorem qform_outer (d : Fin 2 → ℂ) (h : (∑ i, Complex.normSq (d i)) = 1) :
    star d ⬝ᵥ (Matrix.vecMulVec d (star d)) *ᵥ d = 1 := by
  rw [Fin.sum_univ_two] at h
  have h' : (Complex.normSq (d 0) : ℂ) + (Complex.normSq (d 1) : ℂ) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self] at h'
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Pi.star_apply,
    Fin.sum_univ_two, RCLike.star_def]
  linear_combination (conj (d 0) * d 0 + conj (d 1) * d 1 + 1) * h'

/-- With `A` invertible and `d` nonzero the row `d^T conj(A)` is nonzero, so
its squared norm is strictly positive.  This is what makes
`eq:q4o26rnormlarge` a strict inequality. -/
theorem rowNormSq_pos {A : M2} (hA : IsUnit A.det) {d : Fin 2 → ℂ} (hd : d ≠ 0) :
    0 < Complex.normSq ((d ᵥ* cj A) 0) + Complex.normSq ((d ᵥ* cj A) 1) := by
  have hA' : IsUnit (Aᴴ).det := by rw [Matrix.det_conjTranspose]; exact hA.star
  have hrow : d ᵥ* cj A = Aᴴ *ᵥ d := Matrix.vecMul_transpose Aᴴ d
  have hne : Aᴴ *ᵥ d ≠ 0 := by
    intro hc
    apply hd
    calc d = (1 : M2) *ᵥ d := by rw [Matrix.one_mulVec]
      _ = ((Aᴴ)⁻¹ * Aᴴ) *ᵥ d := by rw [Matrix.nonsing_inv_mul _ hA']
      _ = (Aᴴ)⁻¹ *ᵥ (Aᴴ *ᵥ d) := (Matrix.mulVec_mulVec d _ _).symm
      _ = 0 := by rw [hc, Matrix.mulVec_zero]
  rw [hrow]
  obtain ⟨j, hj⟩ : ∃ j, (Aᴴ *ᵥ d) j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  fin_cases j
  · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.2 hj) (Complex.normSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Complex.normSq_pos.2 hj)

/-- **`eq:q4o26rnormlarge`.**  The anchor group's moment identity makes the
three rows carry total squared norm strictly above `1/2`. -/
theorem sum_rowNormSq_gt {C : Fin 3 → M2} {C3 D3 : M2} {d : Fin 2 → ℂ}
    (h3 : IsUnit C3.det) (hd1 : (∑ i, Complex.normSq (d i)) = 1)
    (hD3 : D3 * D3ᴴ = (1/4 : ℂ) • Matrix.vecMulVec d (star d))
    (hmom : ∑ g, C g * (C g)ᴴ = C3 * C3ᴴ + (2 : ℂ) • (D3 * D3ᴴ)) :
    1 / 2 < (Complex.normSq ((d ᵥ* cj (C 0)) 0) + Complex.normSq ((d ᵥ* cj (C 0)) 1))
        + (Complex.normSq ((d ᵥ* cj (C 1)) 0) + Complex.normSq ((d ᵥ* cj (C 1)) 1))
        + (Complex.normSq ((d ᵥ* cj (C 2)) 0) + Complex.normSq ((d ᵥ* cj (C 2)) 1)) := by
  have hd : d ≠ 0 := by
    intro h
    rw [h] at hd1
    simp at hd1
  have hTpos := rowNormSq_pos h3 hd
  -- both sides of the moment identity, as quadratic forms at `d`
  have hleft : star d ⬝ᵥ (∑ g, C g * (C g)ᴴ) *ᵥ d
      = star d ⬝ᵥ (C 0 * (C 0)ᴴ) *ᵥ d + star d ⬝ᵥ (C 1 * (C 1)ᴴ) *ᵥ d
        + star d ⬝ᵥ (C 2 * (C 2)ᴴ) *ᵥ d := by
    rw [Fin.sum_univ_three, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add,
      dotProduct_add]
  have hright : star d ⬝ᵥ (C3 * C3ᴴ + (2 : ℂ) • (D3 * D3ᴴ)) *ᵥ d
      = star d ⬝ᵥ (C3 * C3ᴴ) *ᵥ d + 1 / 2 := by
    rw [Matrix.add_mulVec, dotProduct_add, hD3, smul_smul, Matrix.smul_mulVec,
      dotProduct_smul, qform_outer d hd1]
    norm_num
  have key : ((Complex.normSq ((d ᵥ* cj (C 0)) 0) + Complex.normSq ((d ᵥ* cj (C 0)) 1) : ℝ) : ℂ)
      + ((Complex.normSq ((d ᵥ* cj (C 1)) 0) + Complex.normSq ((d ᵥ* cj (C 1)) 1) : ℝ) : ℂ)
      + ((Complex.normSq ((d ᵥ* cj (C 2)) 0) + Complex.normSq ((d ᵥ* cj (C 2)) 1) : ℝ) : ℂ)
      = ((Complex.normSq ((d ᵥ* cj C3) 0) + Complex.normSq ((d ᵥ* cj C3) 1) : ℝ) : ℂ)
        + 1 / 2 := by
    rw [rowNormSq_eq, rowNormSq_eq, rowNormSq_eq, rowNormSq_eq, ← hleft, hmom, hright]
  have keyR : (Complex.normSq ((d ᵥ* cj (C 0)) 0) + Complex.normSq ((d ᵥ* cj (C 0)) 1))
      + (Complex.normSq ((d ᵥ* cj (C 1)) 0) + Complex.normSq ((d ᵥ* cj (C 1)) 1))
      + (Complex.normSq ((d ᵥ* cj (C 2)) 0) + Complex.normSq ((d ᵥ* cj (C 2)) 1))
      = (Complex.normSq ((d ᵥ* cj C3) 0) + Complex.normSq ((d ᵥ* cj C3) 1)) + 1 / 2 := by
    apply Complex.ofReal_inj.mp
    push_cast
    push_cast at key
    linear_combination key
  rw [keyR]
  linarith


/-! ## The state-interchange symmetry

The manuscript closes with "the equations are symmetric under interchanging
the two logical states, so the same argument proves that `D_3` is singular".
For `eq:q4o26anchormatrix` and `eq:q4o26outermatrix` that symmetry is a
theorem, not an assumption: conjugate-transposing each display returns the
same display with `C` and `D` exchanged.  Only the probability data has to be
supplied again on the other side. -/

theorem conjTranspose_transpose_comm (M : M2) : Mᵀᴴ = Mᴴᵀ := by
  rw [Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose]

/-- `eq:q4o26anchormatrix` is carried to itself by the state interchange. -/
theorem anchor_swap {C3 D3 Cg Dg : M2} (h : C3ᴴ * Dg + (Cgᴴ * D3)ᵀ = 0) :
    D3ᴴ * Cg + (Dgᴴ * C3)ᵀ = 0 := by
  have h1 := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, conjTranspose_transpose_comm,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] at h1
  have h2 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_add, Matrix.transpose_transpose, Matrix.transpose_zero] at h2
  rw [add_comm]
  exact h2

@[simp] theorem conjTranspose_cj (M : M2) : (cj M)ᴴ = Mᵀ := by
  ext i j
  simp [cj, Matrix.conjTranspose_apply, Matrix.transpose_apply]

@[simp] theorem conjTranspose_transpose_eq_cj (M : M2) : (Mᵀ)ᴴ = cj M := by
  ext i j
  simp [cj, Matrix.conjTranspose_apply, Matrix.transpose_apply]

@[simp] theorem conjTranspose_Jmat : Jmatᴴ = Jmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jmat]

/-- `eq:q4o26outermatrix` is carried to itself by the state interchange. -/
theorem outer_swap {Cg Ch Dg Dh : M2}
    (h : cj Cg * Jmat * Dhᵀ + cj Ch * Jmat * Dgᵀ = 0) :
    cj Dg * Jmat * Chᵀ + cj Dh * Jmat * Cgᵀ = 0 := by
  have h1 := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_zero,
    conjTranspose_cj, conjTranspose_cj, conjTranspose_transpose_eq_cj,
    conjTranspose_transpose_eq_cj, conjTranspose_Jmat] at h1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at h1
  rw [add_comm]
  exact h1

/-! ## The lemma -/

/-- The row `(1, t)` applied to a block, in the entrywise form `core` wants. -/
theorem jform_pair_of_F_eq_zero (A B : M2) (hF : Fmat A B = 0) (t : ℂ) :
    Jform (A 0 0 + t * A 1 0) (A 0 1 + t * A 1 1)
      (B 0 0 + t * B 1 0) (B 0 1 + t * B 1 1) = 0 := by
  have h := jform_of_F_eq_zero A B hF ![1, t]
  simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h

/-- **`lem:q4o26anchorsingular`, the `C_3` half.**

The manuscript's displayed equations for orbit 26 -- `eq:q4o26anchormatrix`,
`eq:q4o26outermatrix`, the anchor form of `eq:q4o26matrixmoment`,
`eq:q4o26D3rankone`, and the trace and hexagon data -- force the bottom anchor
block to be singular. -/
theorem C3_not_isUnit
    {C D : Fin 3 → M2} {C3 D3 : M2}
    (anchor : ∀ g, C3ᴴ * D g + ((C g)ᴴ * D3)ᵀ = 0)
    (outer : ∀ g h : Fin 3, g ≠ h →
      cj (C g) * Jmat * (D h)ᵀ + cj (C h) * Jmat * (D g)ᵀ = 0)
    (hmom : ∑ g, C g * (C g)ᴴ = C3 * C3ᴴ + (2 : ℂ) • (D3 * D3ᴴ))
    (Cne : ∀ g, C g ≠ 0)
    (Ccols : ∃ g : Fin 3, ¬(C g 0 0 = 0 ∧ C g 1 0 = 0) ∧ ¬(C g 0 1 = 0 ∧ C g 1 1 = 0))
    (rankOne : ¬ IsUnit D3.det → ∃ d : Fin 2 → ℂ,
      (∑ i, Complex.normSq (d i)) = 1 ∧
        D3 * D3ᴴ = (1 / 4 : ℂ) • Matrix.vecMulVec d (star d))
    (rowBound : ∀ w : Fin 2 → ℂ, (∑ i, Complex.normSq (w i)) = 1 → ∀ g : Fin 3,
      Complex.normSq ((w ᵥ* cj (C g)) 0) + Complex.normSq ((w ᵥ* cj (C g)) 1) ≤ 1 / 4)
    (axisBound : ∀ w : Fin 2 → ℂ, (∑ i, Complex.normSq (w i)) = 1 → ∀ j : Fin 2,
      Complex.normSq ((w ᵥ* cj (C 0)) j) + Complex.normSq ((w ᵥ* cj (C 1)) j)
        + Complex.normSq ((w ᵥ* cj (C 2)) j) ≤ 3 / 8) :
    ¬ IsUnit C3.det := by
  intro h3
  have hDg : ∀ g, D g = -(((C3ᴴ)⁻¹ * D3ᵀ) * cj (C g)) := fun g => anchor_solve h3 (anchor g)
  have hFM : ∀ g h : Fin 3, g ≠ h →
      Fmat (cj (C g)) (cj (C h)) * ((C3ᴴ)⁻¹ * D3ᵀ)ᵀ = 0 :=
    fun g h hgh => F_mul_transpose (hDg g) (hDg h) (outer g h hgh)
  by_cases hD3 : IsUnit D3.det
  · -- `M` is invertible, `F_{gh} = 0`, and a generic row meets `core`
    have hF : ∀ g h : Fin 3, g ≠ h → Fmat (cj (C g)) (cj (C h)) = 0 :=
      fun g h hgh => F_eq_zero_of_isUnit (isUnit_det_M h3 hD3) (hFM g h hgh)
    have hz : ∀ g : Fin 3, ¬(cj (C g) 0 0 = 0 ∧ cj (C g) 0 1 = 0 ∧
        cj (C g) 1 0 = 0 ∧ cj (C g) 1 1 = 0) := by
      rintro g ⟨e00, e01, e10, e11⟩
      simp only [cj_apply, starRingEnd_apply, star_eq_zero] at e00 e01 e10 e11
      refine Cne g ?_
      ext i j
      fin_cases i <;> fin_cases j
      · simpa using e00
      · simpa using e01
      · simpa using e10
      · simpa using e11
    have final : ∀ g0 g1 g2 : Fin 3, g0 ≠ g1 → g0 ≠ g2 → g1 ≠ g2 →
        ¬(C g0 0 0 = 0 ∧ C g0 1 0 = 0) → ¬(C g0 0 1 = 0 ∧ C g0 1 1 = 0) → False := by
      intro g0 g1 g2 h01 h02 h12 hc0 hc1
      refine core (a0 := cj (C g0) 0 0) (b0 := cj (C g0) 0 1) (c0 := cj (C g0) 1 0)
        (d0 := cj (C g0) 1 1) ?_ ?_ (hz g1) (hz g2)
        (fun t => jform_pair_of_F_eq_zero _ _ (hF g0 g1 h01) t)
        (fun t => jform_pair_of_F_eq_zero _ _ (hF g0 g2 h02) t)
        (fun t => jform_pair_of_F_eq_zero _ _ (hF g1 g2 h12) t)
      · rintro ⟨u, v⟩
        simp only [cj_apply, starRingEnd_apply, star_eq_zero] at u v
        exact hc0 ⟨u, v⟩
      · rintro ⟨u, v⟩
        simp only [cj_apply, starRingEnd_apply, star_eq_zero] at u v
        exact hc1 ⟨u, v⟩
    obtain ⟨g, hc0, hc1⟩ := Ccols
    fin_cases g
    · exact final 0 1 2 (by decide) (by decide) (by decide) hc0 hc1
    · exact final 1 0 2 (by decide) (by decide) (by decide) hc0 hc1
    · exact final 2 0 1 (by decide) (by decide) (by decide) hc0 hc1
  · -- `D_3` has rank one; the row is the unit vector spanning its columns
    obtain ⟨d, hd1, hD3'⟩ := rankOne hD3
    have hd : d ≠ 0 := by
      intro h
      rw [h] at hd1
      simp at hd1
    have ejf : ∀ g h : Fin 3, g ≠ h →
        Jform ((d ᵥ* cj (C g)) 0) ((d ᵥ* cj (C g)) 1)
          ((d ᵥ* cj (C h)) 0) ((d ᵥ* cj (C h)) 1) = 0 := fun g h hgh =>
      jform_of_F_mulVec_zero _ _ d
        (F_mulVec_eq_zero_of_rankOne h3 hd hD3' (hFM g h hgh))
    exact core_rank_one (ejf 0 1 (by decide)) (ejf 0 2 (by decide)) (ejf 1 2 (by decide))
      (rowBound d hd1 0) (rowBound d hd1 1) (rowBound d hd1 2)
      (sum_rowNormSq_gt h3 hd1 hD3' hmom) (axisBound d hd1 0) (axisBound d hd1 1)

/-- **`lem:q4o26anchorsingular`, the `D_3` half**, by the state interchange.

`eq:q4o26anchormatrix` and `eq:q4o26outermatrix` are carried to themselves,
which `anchor_swap` and `outer_swap` prove; the remaining hypotheses are the
same data read on the other logical state. -/
theorem D3_not_isUnit
    {C D : Fin 3 → M2} {C3 D3 : M2}
    (anchor : ∀ g, C3ᴴ * D g + ((C g)ᴴ * D3)ᵀ = 0)
    (outer : ∀ g h : Fin 3, g ≠ h →
      cj (C g) * Jmat * (D h)ᵀ + cj (C h) * Jmat * (D g)ᵀ = 0)
    (hmom : ∑ g, D g * (D g)ᴴ = D3 * D3ᴴ + (2 : ℂ) • (C3 * C3ᴴ))
    (Dne : ∀ g, D g ≠ 0)
    (Dcols : ∃ g : Fin 3, ¬(D g 0 0 = 0 ∧ D g 1 0 = 0) ∧ ¬(D g 0 1 = 0 ∧ D g 1 1 = 0))
    (rankOne : ¬ IsUnit C3.det → ∃ d : Fin 2 → ℂ,
      (∑ i, Complex.normSq (d i)) = 1 ∧
        C3 * C3ᴴ = (1 / 4 : ℂ) • Matrix.vecMulVec d (star d))
    (rowBound : ∀ w : Fin 2 → ℂ, (∑ i, Complex.normSq (w i)) = 1 → ∀ g : Fin 3,
      Complex.normSq ((w ᵥ* cj (D g)) 0) + Complex.normSq ((w ᵥ* cj (D g)) 1) ≤ 1 / 4)
    (axisBound : ∀ w : Fin 2 → ℂ, (∑ i, Complex.normSq (w i)) = 1 → ∀ j : Fin 2,
      Complex.normSq ((w ᵥ* cj (D 0)) j) + Complex.normSq ((w ᵥ* cj (D 1)) j)
        + Complex.normSq ((w ᵥ* cj (D 2)) j) ≤ 3 / 8) :
    ¬ IsUnit D3.det :=
  C3_not_isUnit (C := D) (D := C) (C3 := D3) (D3 := C3)
    (fun g => anchor_swap (anchor g))
    (fun g h hgh => outer_swap (outer g h hgh))
    hmom Dne Dcols rankOne rowBound axisBound


/-- **`lem:q4o26anchorsingular`.**  Both anchor blocks are singular.

The hypotheses are the manuscript's own displayed equations for orbit 26 read
on both logical states: `eq:q4o26anchormatrix`, `eq:q4o26outermatrix`, the
anchor form of `eq:q4o26matrixmoment`, `eq:q4o26D3rankone`, and the trace and
hexagon data.  Everything the proof does with them -- the reduction
`eq:q4o26commonM`, the cancellation `eq:q4o26FM`, the norm bookkeeping
`eq:q4o26rnormlarge`, and the state interchange -- is proved here. -/
theorem anchor_singular
    {C D : Fin 3 → M2} {C3 D3 : M2}
    (anchor : ∀ g, C3ᴴ * D g + ((C g)ᴴ * D3)ᵀ = 0)
    (outer : ∀ g h : Fin 3, g ≠ h →
      cj (C g) * Jmat * (D h)ᵀ + cj (C h) * Jmat * (D g)ᵀ = 0)
    (hmomC : ∑ g, C g * (C g)ᴴ = C3 * C3ᴴ + (2 : ℂ) • (D3 * D3ᴴ))
    (hmomD : ∑ g, D g * (D g)ᴴ = D3 * D3ᴴ + (2 : ℂ) • (C3 * C3ᴴ))
    (Cne : ∀ g, C g ≠ 0) (Dne : ∀ g, D g ≠ 0)
    (Ccols : ∃ g : Fin 3, ¬(C g 0 0 = 0 ∧ C g 1 0 = 0) ∧ ¬(C g 0 1 = 0 ∧ C g 1 1 = 0))
    (Dcols : ∃ g : Fin 3, ¬(D g 0 0 = 0 ∧ D g 1 0 = 0) ∧ ¬(D g 0 1 = 0 ∧ D g 1 1 = 0))
    (rankOneD : ¬ IsUnit D3.det → ∃ d : Fin 2 → ℂ,
      (∑ i, Complex.normSq (d i)) = 1 ∧
        D3 * D3ᴴ = (1 / 4 : ℂ) • Matrix.vecMulVec d (star d))
    (rankOneC : ¬ IsUnit C3.det → ∃ d : Fin 2 → ℂ,
      (∑ i, Complex.normSq (d i)) = 1 ∧
        C3 * C3ᴴ = (1 / 4 : ℂ) • Matrix.vecMulVec d (star d))
    (rowBoundC : ∀ w : Fin 2 → ℂ, (∑ i, Complex.normSq (w i)) = 1 → ∀ g : Fin 3,
      Complex.normSq ((w ᵥ* cj (C g)) 0) + Complex.normSq ((w ᵥ* cj (C g)) 1) ≤ 1 / 4)
    (rowBoundD : ∀ w : Fin 2 → ℂ, (∑ i, Complex.normSq (w i)) = 1 → ∀ g : Fin 3,
      Complex.normSq ((w ᵥ* cj (D g)) 0) + Complex.normSq ((w ᵥ* cj (D g)) 1) ≤ 1 / 4)
    (axisBoundC : ∀ w : Fin 2 → ℂ, (∑ i, Complex.normSq (w i)) = 1 → ∀ j : Fin 2,
      Complex.normSq ((w ᵥ* cj (C 0)) j) + Complex.normSq ((w ᵥ* cj (C 1)) j)
        + Complex.normSq ((w ᵥ* cj (C 2)) j) ≤ 3 / 8)
    (axisBoundD : ∀ w : Fin 2 → ℂ, (∑ i, Complex.normSq (w i)) = 1 → ∀ j : Fin 2,
      Complex.normSq ((w ᵥ* cj (D 0)) j) + Complex.normSq ((w ᵥ* cj (D 1)) j)
        + Complex.normSq ((w ᵥ* cj (D 2)) j) ≤ 3 / 8) :
    ¬ IsUnit C3.det ∧ ¬ IsUnit D3.det :=
  ⟨C3_not_isUnit anchor outer hmomC Cne Ccols rankOneD rowBoundC axisBoundC,
    D3_not_isUnit anchor outer hmomD Dne Dcols rankOneC rowBoundD axisBoundD⟩

end MainTheory.Orbit26
