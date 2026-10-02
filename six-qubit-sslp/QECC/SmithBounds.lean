import Mathlib

namespace QECC

open Matrix

noncomputable section

/-- A square integer matrix all of whose entries are zero or one and whose
determinant is nonzero.  Nonsingularity is over `ℤ` (equivalently over `ℚ`
or `ℝ`), rather than over the field with two elements. -/
structure NonsingularBinaryMatrix (s : ℕ) where
  matrix : Matrix (Fin s) (Fin s) ℤ
  entry_eq_zero_or_one : ∀ i j, matrix i j = 0 ∨ matrix i j = 1
  det_ne_zero : matrix.det ≠ 0

namespace NonsingularBinaryMatrix

variable {s : ℕ} (C : NonsingularBinaryMatrix s)

@[ext] theorem ext {A B : NonsingularBinaryMatrix s}
    (h : A.matrix = B.matrix) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- Encode a binary integer matrix as a Boolean matrix. -/
def toBoolMatrix (A : NonsingularBinaryMatrix s) :
    Matrix (Fin s) (Fin s) Bool :=
  fun i j => decide (A.matrix i j = 1)

theorem toBoolMatrix_injective :
    Function.Injective (toBoolMatrix : NonsingularBinaryMatrix s →
      Matrix (Fin s) (Fin s) Bool) := by
  intro A B h
  apply ext
  funext i j
  have hij := congrFun (congrFun h i) j
  rcases A.entry_eq_zero_or_one i j with ha | ha <;>
    rcases B.entry_eq_zero_or_one i j with hb | hb
  · exact ha.trans hb.symm
  · simp [toBoolMatrix, ha, hb] at hij
  · simp [toBoolMatrix, ha, hb] at hij
  · exact ha.trans hb.symm

instance finite (s : ℕ) : Finite (NonsingularBinaryMatrix s) :=
  Finite.of_injective toBoolMatrix toBoolMatrix_injective

noncomputable instance fintype (s : ℕ) : Fintype (NonsingularBinaryMatrix s) :=
  Fintype.ofFinite _

/-- The integral linear map represented by `C`. -/
def intLinearMap : (Fin s → ℤ) →ₗ[ℤ] (Fin s → ℤ) :=
  C.matrix.mulVecLin

/-- The image lattice of the integral matrix `C`. -/
def imageLattice : Submodule ℤ (Fin s → ℤ) :=
  LinearMap.range C.intLinearMap

/-- The finite-rank integer cokernel of `C`. -/
abbrev Cokernel := (Fin s → ℤ) ⧸ C.imageLattice

/-- Nonsingularity makes the integer cokernel finite. -/
noncomputable instance cokernelFinite : Finite C.Cokernel := by
  have hinj : Function.Injective C.intLinearMap := by
    change Function.Injective C.matrix.mulVec
    rw [Matrix.mulVec_injective_iff]
    exact Matrix.linearIndependent_cols_of_det_ne_zero C.det_ne_zero
  have hequiv : Nonempty (C.imageLattice ≃ₗ[ℤ] (Fin s → ℤ)) :=
    ⟨(LinearEquiv.ofInjective C.intLinearMap hinj).symm⟩
  have hindex : C.imageLattice.toAddSubgroup.index ≠ 0 :=
    Int.submodule_toAddSubgroup_index_ne_zero_iff.mpr hequiv
  exact AddSubgroup.index_ne_zero_iff_finite.mp hindex

/-- The final Smith invariant of `C`, characterized invariantly as the
additive exponent of its integer cokernel. -/
def finalSmithInvariant : ℕ :=
  AddMonoid.exponent C.Cokernel

/-- The absolute determinant is a positive annihilator of the integer
cokernel.  This supplies exponent existence without choosing a Smith basis. -/
theorem detNatAbs_nsmul_eq_zero (x : C.Cokernel) :
    C.matrix.det.natAbs • x = 0 := by
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective C.imageLattice x
  rw [← Submodule.Quotient.mk_smul C.imageLattice,
    Submodule.Quotient.mk_eq_zero]
  change C.matrix.det.natAbs • h ∈ LinearMap.range C.intLinearMap
  refine ⟨C.matrix.det.sign • C.matrix.adjugate.mulVec h, ?_⟩
  change C.matrix.mulVec
      (C.matrix.det.sign • C.matrix.adjugate.mulVec h) =
    C.matrix.det.natAbs • h
  calc
    C.matrix.mulVec
        (C.matrix.det.sign • C.matrix.adjugate.mulVec h) =
        C.matrix.det.sign •
          C.matrix.mulVec (C.matrix.adjugate.mulVec h) := by
            exact LinearMap.map_smul C.matrix.mulVecLin _ _
    _ = C.matrix.det.sign •
        ((C.matrix * C.matrix.adjugate).mulVec h) := by
          rw [Matrix.mulVec_mulVec]
    _ = C.matrix.det.sign •
        ((C.matrix.det • (1 : Matrix (Fin s) (Fin s) ℤ)).mulVec h) := by
          rw [Matrix.mul_adjugate]
    _ = C.matrix.det.sign • (C.matrix.det • h) := by simp
    _ = C.matrix.det.natAbs • h := by
      rw [smul_smul, Int.sign_mul_self_eq_natAbs]
      rfl

/-- The integer cokernel has a positive additive exponent. -/
theorem finalSmithInvariant_pos : 0 < C.finalSmithInvariant := by
  apply AddMonoid.ExponentExists.exponent_pos
  refine ⟨C.matrix.det.natAbs, Int.natAbs_pos.mpr C.det_ne_zero, ?_⟩
  exact C.detNatAbs_nsmul_eq_zero

/-- The final Smith invariant divides the absolute determinant. -/
theorem finalSmithInvariant_dvd_detNatAbs :
    C.finalSmithInvariant ∣ C.matrix.det.natAbs := by
  apply AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero
  exact C.detNatAbs_nsmul_eq_zero

/-- Cast the matrix to the rationals. -/
def ratMatrix : Matrix (Fin s) (Fin s) ℚ :=
  C.matrix.map (Int.castRingHom ℚ)

theorem det_ratMatrix_ne_zero : C.ratMatrix.det ≠ 0 := by
  intro hzero
  apply C.det_ne_zero
  have hcast : ((C.matrix.det : ℤ) : ℚ) = 0 := by
    exact (RingHom.map_det (Int.castRingHom ℚ) C.matrix).trans hzero
  exact_mod_cast hcast

theorem ratMatrix_mulVec_injective : Function.Injective C.ratMatrix.mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr C.det_ratMatrix_ne_zero

/-- **Elementary denominator clearing.**  If `C z = h` with rational `z`
and integral `h`, multiplication by the final Smith invariant makes every
coordinate of `z` integral. -/
theorem exists_integral_finalSmithInvariant_smul
    (z : Fin s → ℚ) (h : Fin s → ℤ)
    (hz : C.ratMatrix.mulVec z = fun i => (h i : ℚ)) :
    ∃ k : Fin s → ℤ,
      (fun i => (k i : ℚ)) = C.finalSmithInvariant • z := by
  let d := C.finalSmithInvariant
  have hzero : d • (Submodule.Quotient.mk h : C.Cokernel) = 0 := by
    exact AddMonoid.exponent_nsmul_eq_zero _
  have hmem : d • h ∈ C.imageLattice := by
    rw [← Submodule.Quotient.mk_eq_zero]
    rw [Submodule.Quotient.mk_smul]
    exact hzero
  rcases hmem with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  apply C.ratMatrix_mulVec_injective
  have hkq :
      C.ratMatrix.mulVec (fun i => (k i : ℚ)) =
        fun i => ((d • h) i : ℚ) := by
    funext i
    have hi := congrFun hk i
    calc
      C.ratMatrix.mulVec (fun i => (k i : ℚ)) i =
          (C.matrix.mulVec k i : ℚ) := by
            exact (RingHom.map_mulVec (Int.castRingHom ℚ) C.matrix k i).symm
      _ = ((d • h) i : ℚ) := by exact_mod_cast hi
  calc
    C.ratMatrix.mulVec (fun i => (k i : ℚ)) =
        (fun i => ((d • h) i : ℚ)) := hkq
    _ = d • (fun i => (h i : ℚ)) := by
      funext i
      simp
    _ = d • C.ratMatrix.mulVec z := by rw [hz]
    _ = C.ratMatrix.mulVec (d • z) := by
      exact (LinearMap.map_smul C.ratMatrix.mulVecLin (d : ℚ) z).symm

/-- Real form of elementary denominator clearing.  Although the supplied
solution is allowed to be real, nonsingularity forces its multiple by the
final Smith invariant to be an integral vector. -/
theorem exists_integral_finalSmithInvariant_smul_real
    (z : Fin s → ℝ) (h : Fin s → ℤ)
    (hz : (C.matrix.map (Int.castRingHom ℝ)).mulVec z =
      fun i => (h i : ℝ)) :
    ∃ k : Fin s → ℤ,
      (fun i => (k i : ℝ)) = C.finalSmithInvariant • z := by
  let d := C.finalSmithInvariant
  have hzero : d • (Submodule.Quotient.mk h : C.Cokernel) = 0 := by
    exact AddMonoid.exponent_nsmul_eq_zero _
  have hmem : d • h ∈ C.imageLattice := by
    rw [← Submodule.Quotient.mk_eq_zero]
    rw [Submodule.Quotient.mk_smul]
    exact hzero
  rcases hmem with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  let A : Matrix (Fin s) (Fin s) ℝ :=
    C.matrix.map (Int.castRingHom ℝ)
  have hdetA : A.det ≠ 0 := by
    intro hdet
    apply C.det_ne_zero
    have hcast : ((C.matrix.det : ℤ) : ℝ) = 0 :=
      (RingHom.map_det (Int.castRingHom ℝ) C.matrix).trans hdet
    exact_mod_cast hcast
  have hinj : Function.Injective A.mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdetA
  apply hinj
  have hkR :
      A.mulVec (fun i => (k i : ℝ)) =
        fun i => ((d • h) i : ℝ) := by
    funext i
    have hi := congrFun hk i
    calc
      A.mulVec (fun i => (k i : ℝ)) i =
          (C.matrix.mulVec k i : ℝ) := by
            exact (RingHom.map_mulVec (Int.castRingHom ℝ) C.matrix k i).symm
      _ = ((d • h) i : ℝ) := by exact_mod_cast hi
  calc
    A.mulVec (fun i => (k i : ℝ)) =
        (fun i => ((d • h) i : ℝ)) := hkR
    _ = d • (fun i => (h i : ℝ)) := by
      funext i
      simp
    _ = d • A.mulVec z := by rw [hz]
    _ = A.mulVec (d • z) := by
      simpa only [Nat.cast_smul_eq_nsmul] using
        (LinearMap.map_smul A.mulVecLin (d : ℝ) z).symm

end NonsingularBinaryMatrix

/-- All nonsingular binary square matrices of sizes from one through `nu`. -/
def boundedNonsingularBinaryMatrices (nu : ℕ) :=
  (s : {s : Fin (nu + 1) // 1 ≤ s.1}) ×
    NonsingularBinaryMatrix s.1.1

noncomputable instance boundedNonsingularBinaryMatricesFintype (nu : ℕ) :
    Fintype (boundedNonsingularBinaryMatrices nu) := by
  classical
  unfold boundedNonsingularBinaryMatrices
  letI : (s : {s : Fin (nu + 1) // 1 ≤ s.1}) →
      Fintype (NonsingularBinaryMatrix s.1.1) :=
    fun s => NonsingularBinaryMatrix.fintype s.1.1
  infer_instance

/-- The universal final-Smith-invariant bound for nonsingular binary matrices
of positive size at most `nu`.  For `nu = 0`, the indexing type is empty and
the finite supremum is zero. -/
def smithBeta (nu : ℕ) : ℕ :=
  Finset.univ.sup fun C : boundedNonsingularBinaryMatrices nu =>
    C.2.finalSmithInvariant

theorem finalSmithInvariant_le_smithBeta {nu s : ℕ}
    (hspos : 1 ≤ s) (hsnu : s ≤ nu) (C : NonsingularBinaryMatrix s) :
    C.finalSmithInvariant ≤ smithBeta nu := by
  classical
  let C' : boundedNonsingularBinaryMatrices nu :=
    ⟨⟨⟨s, Nat.lt_succ_iff.mpr hsnu⟩, hspos⟩, C⟩
  exact Finset.le_sup (s := Finset.univ) (f := fun D => D.2.finalSmithInvariant)
    (Finset.mem_univ C')

theorem smithBeta_mono : Monotone smithBeta := by
  intro mu nu hmunu
  classical
  unfold smithBeta
  apply Finset.sup_le
  intro C hC
  exact finalSmithInvariant_le_smithBeta C.1.2
    ((Nat.le_of_lt_succ C.1.1.2).trans hmunu) C.2

/-- The one-by-one identity is a nonsingular binary matrix. -/
def binaryIdentityOne : NonsingularBinaryMatrix 1 where
  matrix := 1
  entry_eq_zero_or_one := by
    intro i j
    fin_cases i
    fin_cases j
    simp
  det_ne_zero := by simp

theorem smithBeta_pos {nu : ℕ} (hnu : 1 ≤ nu) : 0 < smithBeta nu := by
  have hle := finalSmithInvariant_le_smithBeta (nu := nu) (s := 1)
    (by omega) hnu binaryIdentityOne
  exact (binaryIdentityOne.finalSmithInvariant_pos).trans_le hle

@[simp] theorem smithBeta_zero : smithBeta 0 = 0 := by
  classical
  letI : IsEmpty {s : Fin (0 + 1) // 1 ≤ s.1} :=
    ⟨fun s => by omega⟩
  simp [smithBeta, boundedNonsingularBinaryMatrices]

end

end QECC
