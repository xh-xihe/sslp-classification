import QECC.DistanceThreeAffineDimension

namespace QECC

open Matrix

noncomputable section

namespace CodeProjector.NormalizedDistanceThreePhaseSystem

variable {n K q : ℕ} {C : CodeProjector n K} [NeZero q]
  {hq : 0 < q} {a : Fin n → ZMod q}
  {b0 b1 : C.ActiveResidue a}

/-- The basis matrix used in the distance-three argument: its rows are the
actual-support rows selected by Gaussian pivoting, before any coordinate
columns are discarded. -/
def supportBasisMatrix
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    Matrix (Fin D.pivot.size) (Fin n) ℤ :=
  (C.anchorActualSupportMatrix a b0).submatrix D.pivot.row id

@[simp] theorem supportBasisMatrix_apply
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1)
    (i : Fin D.pivot.size) (j : Fin n) :
    D.supportBasisMatrix i j = bitInt ((D.pivot.row i).1 j) := by
  rfl

/-- The selected rows are rows of the normalized actual-support matrix and
span exactly the same rational row space as all actual-support rows. -/
theorem selectedSupportRows_span_rat
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    Submodule.span ℚ (Set.range fun i ↦
        ((C.anchorActualSupportMatrix a b0).map
          (Int.castRingHom ℚ)).row (D.pivot.row i)) =
      C.anchorActualSupportSpan a b0 := by
  exact D.pivot.rows_span

/-- The actual-support rows selected by Gaussian pivoting are linearly
independent over the rationals. -/
theorem selectedSupportRows_independent_rat
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    LinearIndependent ℚ (fun i ↦
      ((C.anchorActualSupportMatrix a b0).map
        (Int.castRingHom ℚ)).row (D.pivot.row i)) :=
  D.pivot.selectedRows_independent

/-- The rows of `supportBasisMatrix` are the selected rows of the full
actual-support matrix after casting to the rationals. -/
@[simp] theorem supportBasisMatrix_row_rat
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1)
    (i : Fin D.pivot.size) :
    ((D.supportBasisMatrix.map (Int.castRingHom ℚ)).row i) =
      ((C.anchorActualSupportMatrix a b0).map
        (Int.castRingHom ℚ)).row (D.pivot.row i) := by
  rfl

/-- Thus `supportBasisMatrix` is a row basis of the rational row span of the
normalized actual-support matrix. -/
theorem supportBasisMatrix_rows_independent_rat
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    LinearIndependent ℚ
      ((D.supportBasisMatrix.map (Int.castRingHom ℚ)).row) := by
  simpa only [D.supportBasisMatrix_row_rat] using
    D.selectedSupportRows_independent_rat

theorem supportBasisMatrix_rows_span_rat
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    Submodule.span ℚ
        (Set.range ((D.supportBasisMatrix.map
          (Int.castRingHom ℚ)).row)) =
      C.anchorActualSupportSpan a b0 := by
  simpa only [D.supportBasisMatrix_row_rat] using
    D.selectedSupportRows_span_rat

/-- The selected actual-support vectors remain linearly independent after
extension of scalars from `ℚ` to `ℝ`. -/
theorem selectedSupportVectors_independent_real
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    LinearIndependent ℝ
      (fun i ↦ bitVector (D.pivot.row i).1) := by
  let A := C.anchorActualSupportMatrix a b0
  let minorR : Matrix (Fin D.pivot.size) (Fin D.pivot.size) ℝ :=
    (A.submatrix D.pivot.row D.pivot.column).map (Int.castRingHom ℝ)
  have hminorDet : minorR.det ≠ 0 := by
    intro hzero
    apply D.pivot.minor_det_ne_zero
    have hcast :
        (((A.submatrix D.pivot.row D.pivot.column).det : ℤ) : ℝ) = 0 := by
      exact (RingHom.map_det (Int.castRingHom ℝ)
        (A.submatrix D.pivot.row D.pivot.column)).trans hzero
    exact_mod_cast hcast
  have hminorLI : LinearIndependent ℝ minorR.row :=
    Matrix.linearIndependent_rows_of_det_ne_zero hminorDet
  let restrict : (Fin n → ℝ) →ₗ[ℝ] (Fin D.pivot.size → ℝ) :=
    LinearMap.funLeft ℝ ℝ D.pivot.column
  apply LinearIndependent.of_comp restrict
  have hrows :
      (restrict ∘ fun i ↦ bitVector (D.pivot.row i).1) = minorR.row := by
    funext i j
    change bitVector (D.pivot.row i).1 (D.pivot.column j) =
      minorR i j
    simpa [minorR, A] using
      (congrFun (C.anchorActualSupportMatrix_row_real a b0
        (D.pivot.row i)) (D.pivot.column j)).symm
  rw [hrows]
  exact hminorLI

/-- The chosen actual-support vectors span the real row span of the complete
normalized actual-support matrix. -/
theorem selectedSupportVectors_span_real
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    Submodule.span ℝ
        (Set.range fun i ↦ bitVector (D.pivot.row i).1) =
      Submodule.span ℝ (Set.range
        (((C.anchorActualSupportMatrix a b0).map
          (Int.castRingHom ℝ)).row)) := by
  let selected : Submodule ℝ (Fin n → ℝ) :=
    Submodule.span ℝ (Set.range fun i ↦ bitVector (D.pivot.row i).1)
  let full : Submodule ℝ (Fin n → ℝ) :=
    Submodule.span ℝ (Set.range
      (((C.anchorActualSupportMatrix a b0).map
        (Int.castRingHom ℝ)).row))
  have hle : selected ≤ full := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨D.pivot.row i, ?_⟩
    exact C.anchorActualSupportMatrix_row_real a b0
      (D.pivot.row i)
  have hselectedDim : Module.finrank ℝ selected = D.pivot.size := by
    exact (linearIndependent_iff_card_eq_finrank_span.mp
      D.selectedSupportVectors_independent_real).symm.trans
        (Fintype.card_fin D.pivot.size)
  have hfullDim : Module.finrank ℝ full = D.pivot.size := by
    rw [← Matrix.rank_eq_finrank_span_row]
    exact D.pivot.realRank_eq_size
  exact Submodule.eq_of_le_of_finrank_eq hle
    (hselectedDim.trans hfullDim.symm)

/-- Once the normalization point `0` is known to lie in the anchor support,
the selected support vectors are a basis of its affine direction. -/
theorem selectedSupportVectors_span_affineDirection
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b0) :
    Submodule.span ℝ
        (Set.range fun i ↦ bitVector (D.pivot.row i).1) =
      (C.actualSectorAffineSpan a b0).direction := by
  rw [D.selectedSupportVectors_span_real]
  exact (C.direction_actualSectorAffineSpan_eq_anchorRowSpan
    a b0 hzero).symm

/-- The same selected support vectors span the affine direction of the
second support, since the distance-three certificate identifies the two
affine spans. -/
theorem selectedSupportVectors_span_secondAffineDirection
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b0) :
    Submodule.span ℝ
        (Set.range fun i ↦ bitVector (D.pivot.row i).1) =
      (C.actualSectorAffineSpan a b1).direction := by
  rw [D.selectedSupportVectors_span_affineDirection hzero,
    D.affineSpan_eq]

/-- The Smith matrix is exactly the coordinate minor obtained from the
support basis matrix by retaining the pivot columns. -/
theorem binaryPivotMinor_matrix_eq_coordinateMinor
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    D.binaryPivotMinor.matrix =
      D.supportBasisMatrix.submatrix id D.pivot.column := by
  ext i j
  rfl

/-- The number of selected actual-support rows and selected coordinate
columns is the common affine dimension `r`. -/
theorem supportBasisMatrix_size_eq_r
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    D.pivot.size = D.r :=
  D.pivot_size_eq

end CodeProjector.NormalizedDistanceThreePhaseSystem

end

end QECC
