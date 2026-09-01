import MainTheory.FiniteLift
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import MainTheory.DeterminantalRank

/-!
# The pivot size bound

`thm:qualitative-finite-lift` states the pivot size as

  s = rank R <= n + t - 1.

The bound half is recorded here.  It needs nothing beyond the fact already in
`PivotData`: the selected columns are an *embedding* into
`Fin n ⊕ Color D`, and there are `n + (t - 1)` of those, one colour for every
sector other than the base one.
-/

namespace MainTheory.PivotSize

open MainTheory.FiniteLift
open MainTheory.PhaseSectorFull

variable {n t : ℕ} {theta : Fin n → ℝ}

/-- There is one colour for every sector but the base one. -/
theorem card_color (D : SectorDecomposition n t theta) :
    Fintype.card (Color D) = t - 1 := by
  classical
  rw [Fintype.card_subtype_compl]
  simp

/-- **The pivot size is at most `n + t - 1`** -- the paper's
`eq:qualitative-pivot-size`. -/
theorem card_le (D : SectorDecomposition n t theta) {s : Type*} [Fintype s]
    (P : PivotData D s) : Fintype.card s ≤ n + t - 1 := by
  classical
  have h := Fintype.card_le_of_embedding P.column
  rw [Fintype.card_sum, Fintype.card_fin, card_color] at h
  have ht := D.sectorCount_pos
  omega

/-! ## The pivot size is the rank

`PivotData.spans` says the selected rows span every row, so the rank is at
most the pivot size.  Nonsingularity of the selected square block gives the
other inequality: a vanishing combination of the selected rows, read off at
the selected columns, is a vanishing `vecMul` against a matrix of nonzero
determinant. -/

/-- The rational square block cut out by the selected rows and columns. -/
noncomputable def ratPivot {D : SectorDecomposition n t theta} {s : Type*}
    [Fintype s] (P : PivotData D s) : Matrix s s ℚ :=
  fun i j => coloredMatrix D (P.row i) (P.column j)

/-- The selected rows span the whole row space. -/
theorem span_row_eq {D : SectorDecomposition n t theta} {s : Type*} [Fintype s]
    (P : PivotData D s) :
    Submodule.span ℚ (Set.range (coloredMatrix D))
      = Submodule.span ℚ (Set.range fun i => coloredMatrix D (P.row i)) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    have hrow : coloredMatrix D r
        = ∑ i, P.rowCoeff r i • coloredMatrix D (P.row i) := by
      funext c
      rw [Finset.sum_apply]
      exact P.spans r c
    rw [hrow]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨P.row i, rfl⟩

/-- **The selected rows are linearly independent** when the square block they
cut out is nonsingular. -/
theorem linearIndependent_rows {D : SectorDecomposition n t theta} {s : Type*}
    [Fintype s] [DecidableEq s] (P : PivotData D s)
    (hdet : (ratPivot P).det ≠ 0) :
    LinearIndependent ℚ fun i => coloredMatrix D (P.row i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hzero : c = 0 := by
    refine Matrix.eq_zero_of_vecMul_eq_zero hdet ?_
    funext j
    have hj := congrFun hc (P.column j)
    simpa [Matrix.vecMul, dotProduct, ratPivot, Finset.sum_apply,
      mul_comm] using hj
  intro i
  exact congrFun hzero i

/-- **The pivot size is the rank of the coloured matrix** -- the first half of
the paper's `eq:qualitative-pivot-size`. -/
theorem card_eq_rank {D : SectorDecomposition n t theta} {s : Type*}
    [Fintype s] [DecidableEq s] (P : PivotData D s)
    (hdet : (ratPivot P).det ≠ 0) :
    Fintype.card s = (coloredMatrix D).rank := by
  rw [Matrix.rank_eq_finrank_span_row]
  show Fintype.card s
    = Module.finrank ℚ (Submodule.span ℚ (Set.range (coloredMatrix D)))
  rw [span_row_eq P]
  have hli := linearIndependent_rows P hdet
  exact (finrank_span_eq_card hli).symm

/-- **The coloured matrix has rank at most `n + t - 1`, unconditionally.**

This needs no pivot at all: the rank of any matrix is at most its number of
columns, and there are `n` physical columns and one colour per non-base
sector.  Together with `card_eq_rank` it closes the paper's chain
`s = rank R <= n + t - 1` -- but note that chain still runs through a supplied
`PivotData`, and nothing in the tree yet constructs one. -/
theorem rank_le (D : SectorDecomposition n t theta) :
    (coloredMatrix D).rank ≤ n + t - 1 := by
  classical
  have h := Matrix.rank_le_card_width (coloredMatrix D)
  rw [Fintype.card_sum, Fintype.card_fin, card_color] at h
  have ht := D.sectorCount_pos
  omega

/-! ## A pivot exists

`card_eq_rank` above says "any pivot you are handed has size the rank".  The
paper asserts more: that such a pivot *exists*, cut out by a nonsingular
binary minor.  That is what this section supplies, so the chain
`s = rank R <= n + t - 1` no longer runs through a hypothesis. -/

/-- **A nonsingular pivot exists for the coloured matrix.**

Independent rows are extracted from the row space, and
`DeterminantalRank.exists_nonsingular_minor` selects coordinates on which they
stay independent. -/
theorem exists_pivotData (D : SectorDecomposition n t theta) :
    ∃ P : PivotData D (Fin (coloredMatrix D).rank),
      (ratPivot P).det ≠ 0 := by
  classical
  set A := coloredMatrix D with hA
  have hdim : Module.finrank ℚ
      (Submodule.span ℚ (Set.range A.row)) = A.rank :=
    (Matrix.rank_eq_finrank_span_row A).symm
  obtain ⟨f, hf_mem, hf_span, hf_ind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.row)
  -- transport the index along the rank equality
  let e : Fin A.rank ≃
      Fin (Module.finrank ℚ (Submodule.span ℚ (Set.range A.row))) :=
    finCongr hdim.symm
  choose row hrow using fun i : Fin A.rank => hf_mem (e i)
  have hind : LinearIndependent ℚ fun i : Fin A.rank => A (row i) := by
    have : (fun i : Fin A.rank => A (row i)) = fun i => f (e i) := by
      funext i; exact hrow i
    rw [this]
    exact hf_ind.comp e e.injective
  obtain ⟨column, hdet⟩ :=
    DeterminantalRank.exists_nonsingular_minor
      (fun i : Fin A.rank => A (row i)) hind
  have hmem : ∀ rho, A rho ∈ Submodule.span ℚ
      (Set.range fun i : Fin A.rank => A (row i)) := by
    intro rho
    have hrange : (Set.range fun i : Fin A.rank => A (row i))
        = Set.range f := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, (hrow i).symm⟩
      · rintro ⟨j, rfl⟩
        refine ⟨e.symm j, ?_⟩
        show A.row (row (e.symm j)) = f j
        rw [hrow, Equiv.apply_symm_apply]
    rw [hrange, hf_span]
    exact Submodule.subset_span ⟨rho, rfl⟩
  choose coef hcoef using fun rho =>
    (Submodule.mem_span_range_iff_exists_fun ℚ).1 (hmem rho)
  refine ⟨{ row := row, column := column, rowCoeff := coef, spans := ?_ }, hdet⟩
  intro rho c
  have := congrFun (hcoef rho) c
  simpa [Finset.sum_apply, smul_eq_mul] using this.symm

/-- **`eq:qualitative-pivot-size`, with no hypothesis left.**

There is a pivot; its size is the rank of the coloured matrix; and that rank
is at most `n + t - 1`.  Previously each half was conditional -- one on a
supplied `PivotData`, the other additionally on its nonsingularity. -/
theorem exists_pivot_card_eq_rank_le (D : SectorDecomposition n t theta) :
    ∃ P : PivotData D (Fin (coloredMatrix D).rank),
      (ratPivot P).det ≠ 0 ∧
      Fintype.card (Fin (coloredMatrix D).rank) = (coloredMatrix D).rank ∧
      (coloredMatrix D).rank ≤ n + t - 1 := by
  obtain ⟨P, hdet⟩ := exists_pivotData D
  exact ⟨P, hdet, card_eq_rank P hdet, rank_le D⟩

end MainTheory.PivotSize
