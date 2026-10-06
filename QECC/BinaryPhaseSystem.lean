import QECC.RationalSection
import QECC.SmithBounds

namespace QECC

open scoped BigOperators
open Matrix

noncomputable section

/-- An integral matrix all of whose entries are zero or one. -/
def Matrix.IsZeroOne {m n : Type*} (A : Matrix m n ℤ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- Extend a vector along an embedding, putting zero outside the image.  The
finite-sum definition makes matrix multiplication with this vector easy to
rewrite. -/
def scatter {s N : ℕ} (e : Fin s ↪ Fin N) (z : Fin s → ℚ) : Fin N → ℚ :=
  fun j ↦ ∑ i : Fin s, if e i = j then z i else 0

/-- The integral analogue of `scatter`. -/
def integralScatter {s N : ℕ} (e : Fin s ↪ Fin N) (z : Fin s → ℤ) : Fin N → ℤ :=
  fun j ↦ ∑ i : Fin s, if e i = j then z i else 0

@[simp] theorem scatter_apply_image {s N : ℕ} (e : Fin s ↪ Fin N)
    (z : Fin s → ℚ) (i : Fin s) :
    scatter e z (e i) = z i := by
  classical
  simp [scatter, e.injective.eq_iff]

theorem scatter_apply_of_not_mem_range {s N : ℕ} (e : Fin s ↪ Fin N)
    (z : Fin s → ℚ) {j : Fin N} (hj : j ∉ Set.range e) :
    scatter e z j = 0 := by
  classical
  simp only [scatter]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  intro hij
  exact hj ⟨i, hij⟩

theorem dotProduct_scatter {s N : ℕ} (e : Fin s ↪ Fin N)
    (row : Fin N → ℚ) (z : Fin s → ℚ) :
    dotProduct row (scatter e z) = dotProduct (row ∘ e) z := by
  classical
  simp only [dotProduct, scatter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (e i)]
  · simp
  · intro j _ hji
    rw [if_neg (fun hij : e i = j ↦ hji hij.symm), mul_zero]
  · simp

theorem cast_integralScatter {s N : ℕ} (e : Fin s ↪ Fin N)
    (z : Fin s → ℤ) :
    (fun j ↦ (integralScatter e z j : ℚ)) =
      scatter e (fun i ↦ (z i : ℚ)) := by
  classical
  funext j
  simp only [integralScatter, scatter]
  push_cast
  rfl

theorem scatter_nsmul {s N : ℕ} (e : Fin s ↪ Fin N)
    (d : ℕ) (z : Fin s → ℚ) :
    scatter e (d • z) = d • scatter e z := by
  classical
  funext j
  simp only [scatter, Pi.smul_apply, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : e i = j <;> simp [hij]

/-- Data produced by pivoting a consistent integral system.  `row` selects
rank-many independent equations, `column` selects a nonsingular coordinate
minor, and `solution` is zero away from those selected coordinates. -/
structure BinaryPivotSolution {rows : Type*} [Fintype rows]
    (N : ℕ) (A : Matrix rows (Fin N) ℤ) (h : rows → ℤ) where
  size : ℕ
  size_le : size ≤ N
  size_eq_rank : size = (A.map (Int.castRingHom ℚ)).rank
  row : Fin size ↪ rows
  column : Fin size ↪ Fin N
  rows_span :
    Submodule.span ℚ (Set.range fun i ↦ (A.map (Int.castRingHom ℚ)).row (row i)) =
      Submodule.span ℚ (Set.range (A.map (Int.castRingHom ℚ)).row)
  selectedRows_independent :
    LinearIndependent ℚ (fun i ↦ (A.map (Int.castRingHom ℚ)).row (row i))
  minor_zeroOne : Matrix.IsZeroOne (A.submatrix row column)
  minor_det_ne_zero : (A.submatrix row column).det ≠ 0
  selectedSolution : Fin size → ℚ
  selectedSystem :
    (A.submatrix row column).map (Int.castRingHom ℚ) *ᵥ selectedSolution =
      fun i ↦ (h (row i) : ℚ)
  solution : Fin N → ℚ
  solution_eq_scatter : solution = scatter column selectedSolution
  solves :
    A.map (Int.castRingHom ℚ) *ᵥ solution = fun i ↦ (h i : ℚ)

namespace BinaryPivotSolution

variable {rows : Type*} [Fintype rows] {N : ℕ}
  {A : Matrix rows (Fin N) ℤ} {h : rows → ℤ}

@[simp] theorem solution_apply_column (S : BinaryPivotSolution N A h)
    (i : Fin S.size) : S.solution (S.column i) = S.selectedSolution i := by
  rw [S.solution_eq_scatter, scatter_apply_image]

theorem solution_apply_of_not_mem_range (S : BinaryPivotSolution N A h)
    {j : Fin N} (hj : j ∉ Set.range S.column) : S.solution j = 0 := by
  rw [S.solution_eq_scatter]
  exact scatter_apply_of_not_mem_range S.column S.selectedSolution hj

/-- The square pivot minor packaged for the Smith-bound API. -/
def pivotMinor (S : BinaryPivotSolution N A h) :
    NonsingularBinaryMatrix S.size where
  matrix := A.submatrix S.row S.column
  entry_eq_zero_or_one := S.minor_zeroOne
  det_ne_zero := S.minor_det_ne_zero

@[simp] theorem pivotMinor_matrix (S : BinaryPivotSolution N A h) :
    S.pivotMinor.matrix = A.submatrix S.row S.column := rfl

/-- The final Smith invariant of the pivot minor clears all denominators in
the selected solution. -/
theorem exists_integral_finalSmithInvariant_smul_selectedSolution
    (S : BinaryPivotSolution N A h) :
    ∃ k : Fin S.size → ℤ,
      (fun i ↦ (k i : ℚ)) =
        S.pivotMinor.finalSmithInvariant • S.selectedSolution := by
  apply S.pivotMinor.exists_integral_finalSmithInvariant_smul
    S.selectedSolution (fun i ↦ h (S.row i))
  simpa [pivotMinor, NonsingularBinaryMatrix.ratMatrix] using S.selectedSystem

/-- The same Smith invariant clears the full solution obtained by inserting
zeros outside the pivot coordinates. -/
theorem exists_integral_finalSmithInvariant_smul_solution
    (S : BinaryPivotSolution N A h) :
    ∃ k : Fin N → ℤ,
      (fun j ↦ (k j : ℚ)) =
        S.pivotMinor.finalSmithInvariant • S.solution := by
  obtain ⟨k, hk⟩ :=
    S.exists_integral_finalSmithInvariant_smul_selectedSolution
  refine ⟨integralScatter S.column k, ?_⟩
  calc
    (fun j ↦ (integralScatter S.column k j : ℚ)) =
        scatter S.column (fun i ↦ (k i : ℚ)) :=
      cast_integralScatter S.column k
    _ = scatter S.column
        (S.pivotMinor.finalSmithInvariant • S.selectedSolution) := by rw [hk]
    _ = S.pivotMinor.finalSmithInvariant •
        scatter S.column S.selectedSolution :=
      scatter_nsmul S.column S.pivotMinor.finalSmithInvariant S.selectedSolution
    _ = S.pivotMinor.finalSmithInvariant • S.solution := by
      rw [S.solution_eq_scatter]

/-- The pivot denominator is universally bounded in terms of the number of
columns.  The `max 1` accounts for the empty rank-zero minor. -/
theorem pivotMinor_finalSmithInvariant_le (S : BinaryPivotSolution N A h) :
    S.pivotMinor.finalSmithInvariant ≤ max 1 (smithBeta N) := by
  by_cases hsize : S.size = 0
  · haveI : Subsingleton (Fin S.size → ℤ) := by
      constructor
      intro u v
      funext i
      exact Fin.elim0 (hsize ▸ i)
    haveI : Subsingleton S.pivotMinor.Cokernel := inferInstance
    change AddMonoid.exponent S.pivotMinor.Cokernel ≤ max 1 (smithBeta N)
    rw [AddMonoid.exp_eq_one_of_subsingleton]
    exact le_max_left _ _
  · exact (finalSmithInvariant_le_smithBeta
      (Nat.one_le_iff_ne_zero.mpr hsize) S.size_le S.pivotMinor).trans
        (le_max_right _ _)

end BinaryPivotSolution

/-- A consistent rational system with an integral coefficient matrix admits a
solution supported on at most `rank A` coordinates.  If the matrix is binary,
the coordinates can be chosen so that the corresponding square integral minor
is binary and nonsingular.

The proof is ordinary Gaussian pivoting, phrased invariantly: first choose a
basis among the rows, then a basis among the coordinate columns of the
resulting full-row-rank matrix. -/
theorem exists_binaryPivotSolution_of_rational
    {rows : Type*} [Fintype rows] {N : ℕ}
    (A : Matrix rows (Fin N) ℤ) (h : rows → ℤ)
    (hA : Matrix.IsZeroOne A)
    (hconsistent : ∃ x : Fin N → ℚ,
      A.map (Int.castRingHom ℚ) *ᵥ x = fun i ↦ (h i : ℚ)) :
    Nonempty (BinaryPivotSolution N A h) := by
  classical
  let Aq : Matrix rows (Fin N) ℚ := A.map (Int.castRingHom ℚ)
  obtain ⟨x, hx⟩ := hconsistent

  -- Choose a basis of the row space, retaining the original row indices.
  have rowData :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range Aq.row)
  rw [← Aq.rank_eq_finrank_span_row] at rowData
  obtain ⟨f, hf_mem, hf_span, hf_independent⟩ := rowData
  choose rowIndex hrowIndex using hf_mem
  let row : Fin Aq.rank ↪ rows :=
    ⟨rowIndex, fun i j hij ↦ hf_independent.injective <| by
      rw [← hrowIndex i, ← hrowIndex j, hij]⟩
  have hrow (i : Fin Aq.rank) : Aq.row (row i) = f i := hrowIndex i
  have hrow_independent :
      LinearIndependent ℚ (fun i ↦ Aq.row (row i)) := by
    simpa only [hrow] using hf_independent
  have hrow_span :
      Submodule.span ℚ (Set.range fun i ↦ Aq.row (row i)) =
        Submodule.span ℚ (Set.range Aq.row) := by
    simpa only [hrow] using hf_span

  -- The selected-row matrix has full row rank.  Choose a basis among its
  -- coordinate columns; these are the pivot coordinates.
  let B : Matrix (Fin Aq.rank) (Fin N) ℚ := Aq.submatrix row id
  have hB_independent : LinearIndependent ℚ B.row := by
    simpa only [B, Matrix.row_submatrix_eq_comp, Function.comp_id] using
      hrow_independent
  have hB_rank : B.rank = Aq.rank := by
    simpa using hB_independent.rank_matrix
  have hcol_finrank :
      Module.finrank ℚ (Submodule.span ℚ (Set.range B.col)) = Aq.rank := by
    rw [← B.rank_eq_finrank_span_cols, hB_rank]
  have columnData :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range B.col)
  rw [hcol_finrank] at columnData
  obtain ⟨g, hg_mem, _hg_span, hg_independent⟩ := columnData
  choose columnIndex hcolumnIndex using hg_mem
  let column : Fin Aq.rank ↪ Fin N :=
    ⟨columnIndex, fun i j hij ↦ hg_independent.injective <| by
      rw [← hcolumnIndex i, ← hcolumnIndex j, hij]⟩

  let C : Matrix (Fin Aq.rank) (Fin Aq.rank) ℚ :=
    B.submatrix id column
  have hCcol (i : Fin Aq.rank) : C.col i = g i := by
    simpa only [C, Matrix.col_submatrix_eq_comp, Function.comp_id] using
      hcolumnIndex i
  have hC_independent : LinearIndependent ℚ C.col := by
    rw [show C.col = g by funext i; exact hCcol i]
    exact hg_independent
  have hC_unit : IsUnit C :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hC_independent

  -- Solve the square pivot system and extend the solution by zero.
  obtain ⟨z, hz⟩ :=
    (Matrix.mulVec_surjective_iff_isUnit.mpr hC_unit)
      (fun i ↦ (h (row i) : ℚ))
  let solution : Fin N → ℚ := scatter column z

  have hselected (i : Fin Aq.rank) :
      dotProduct (Aq.row (row i)) solution = (h (row i) : ℚ) := by
    have hi := congrFun hz i
    rw [dotProduct_scatter]
    exact hi

  -- Agreement on a spanning set of rows implies agreement on every row.
  let annihilator : (Fin N → ℚ) →ₗ[ℚ] ℚ :=
    (dotProductBilin ℚ ℚ) (solution - x)
  have hselected_ker (i : Fin Aq.rank) :
      Aq.row (row i) ∈ LinearMap.ker annihilator := by
    rw [LinearMap.mem_ker]
    change dotProduct (solution - x) (Aq.row (row i)) = 0
    rw [dotProduct_comm, dotProduct_sub]
    rw [hselected i]
    have hxi := congrFun hx (row i)
    change dotProduct (Aq.row (row i)) x = (h (row i) : ℚ) at hxi
    rw [hxi, sub_self]
  have hspan_ker :
      Submodule.span ℚ (Set.range fun i ↦ Aq.row (row i)) ≤
        LinearMap.ker annihilator := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hselected_ker i
  have hall_ker (i : rows) : Aq.row i ∈ LinearMap.ker annihilator := by
    apply hspan_ker
    rw [hrow_span]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hsolution : Aq *ᵥ solution = fun i ↦ (h i : ℚ) := by
    funext i
    have hi := hall_ker i
    rw [LinearMap.mem_ker] at hi
    change dotProduct (solution - x) (Aq.row i) = 0 at hi
    rw [dotProduct_comm, dotProduct_sub] at hi
    have hxi := congrFun hx i
    change dotProduct (Aq.row i) x = (h i : ℚ) at hxi
    change dotProduct (Aq.row i) solution = (h i : ℚ)
    exact sub_eq_zero.mp hi |>.trans hxi

  have hminor_cast :
      (A.submatrix row column).map (Int.castRingHom ℚ) = C := by
    ext i j
    rfl
  have hminor_det : (A.submatrix row column).det ≠ 0 := by
    intro hzero
    have hC_det : C.det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det C).mp hC_unit)
    apply hC_det
    rw [← hminor_cast]
    calc
      ((A.submatrix row column).map (Int.castRingHom ℚ)).det =
          ((A.submatrix row column).det : ℚ) := by
            exact (RingHom.map_det (Int.castRingHom ℚ)
              (A.submatrix row column)).symm
      _ = 0 := by rw [hzero]; norm_num

  refine ⟨{
    size := Aq.rank
    size_le := ?_
    size_eq_rank := rfl
    row := row
    column := column
    rows_span := hrow_span
    selectedRows_independent := hrow_independent
    minor_zeroOne := fun i j ↦ hA (row i) (column j)
    minor_det_ne_zero := hminor_det
    selectedSolution := z
    selectedSystem := ?_
    solution := solution
    solution_eq_scatter := rfl
    solves := ?_ }⟩
  · exact Aq.rank_le_card_width.trans_eq (Fintype.card_fin N)
  · rw [hminor_cast]
    exact hz
  · exact hsolution

/-- Real consistency is enough for `exists_binaryPivotSolution`: because the
matrix and right hand side are integral, `integerMatrix_uniform_rational_lift`
first replaces a real solution by a rational one. -/
theorem exists_binaryPivotSolution
    {rows : Type*} [Fintype rows] {N : ℕ}
    (A : Matrix rows (Fin N) ℤ) (h : rows → ℤ)
    (hA : Matrix.IsZeroOne A)
    (hconsistent : ∃ x : Fin N → ℝ,
      A.map (Int.castRingHom ℝ) *ᵥ x = fun i ↦ (h i : ℝ)) :
    Nonempty (BinaryPivotSolution N A h) := by
  classical
  obtain ⟨x, hx⟩ := hconsistent
  obtain ⟨Q, hQ, hQ_lift⟩ := integerMatrix_uniform_rational_lift A
  obtain ⟨a, ha⟩ := hQ_lift x h hx
  let y : Fin N → ℚ := fun j ↦ (a j : ℚ) / (Q : ℚ)
  have hy_real :
      A.map (Int.castRingHom ℝ) *ᵥ
          (fun j ↦ (a j : ℝ) / (Q : ℝ)) =
        fun i ↦ (h i : ℝ) := by
    have ha' := ha
    rw [Matrix.mulVec_sub, hx] at ha'
    exact (sub_eq_zero.mp ha').symm
  have hy :
      A.map (Int.castRingHom ℚ) *ᵥ y = fun i ↦ (h i : ℚ) := by
    funext i
    have hi := congrFun hy_real i
    simp only [Matrix.mulVec, dotProduct] at hi ⊢
    apply Rat.cast_injective (α := ℝ)
    push_cast
    simpa [y] using hi
  exact exists_binaryPivotSolution_of_rational A h hA ⟨y, hy⟩

end

end QECC
