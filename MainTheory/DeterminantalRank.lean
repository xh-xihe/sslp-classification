import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The determinantal characterization of rank

Mathlib does not have it: a matrix of rank `r` has an `r x r` submatrix of
nonzero determinant.  This repository does prove the instance it needed --
`D3SparseRationalization.exists_nonsingular_coordinate_minor`, for real rows
indexed by `Fin n` -- and that proof uses nothing about the field or the
column index.

Recorded here in the general form, over an arbitrary field with an arbitrary
finite column index, so that it can be applied to the rational coloured matrix
of the finite-lift argument.
-/

namespace MainTheory.DeterminantalRank

open Module

variable {K : Type*} [Field K] {J : Type*} [Fintype J]

/-- **Linearly independent rows admit a nonsingular coordinate minor.**

Given `r` linearly independent vectors indexed by a finite coordinate set,
some `r` of the coordinates already separate them: the square matrix cut out
by those coordinates is invertible. -/
theorem exists_nonsingular_minor {r : ℕ} (v : Fin r → J → K)
    (hv : LinearIndependent K v) :
    ∃ coordinate : Fin r ↪ J,
      (show Matrix (Fin r) (Fin r) K from
        fun i j => v i (coordinate j)).det ≠ 0 := by
  classical
  let A : Matrix (Fin r) J K := fun i j => v i j
  have hrow : LinearIndependent K A.row := by
    simpa [A, Matrix.row] using hv
  have hdim : finrank K (Submodule.span K (Set.range A.col)) = r := by
    rw [← Matrix.rank_eq_finrank_span_cols]
    simpa using hrow.rank_matrix
  obtain ⟨f, hf_mem, _, hf_independent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
  let e : Fin r ≃ Fin (finrank K (Submodule.span K (Set.range A.col))) :=
    finCongr hdim.symm
  choose coordinate hcoordinate using fun i : Fin r => hf_mem (e i)
  have hinj : Function.Injective coordinate := by
    intro i j hij
    apply e.injective
    apply hf_independent.injective
    rw [← hcoordinate i, ← hcoordinate j, hij]
  let emb : Fin r ↪ J := ⟨coordinate, hinj⟩
  let M : Matrix (Fin r) (Fin r) K := fun i j => v i (emb j)
  have hcols : LinearIndependent K M.col := by
    have hselected : LinearIndependent K (fun j : Fin r => f (e j)) :=
      hf_independent.comp e e.injective
    have hcol_eq : M.col = fun j : Fin r => f (e j) := by
      funext j i
      simpa [M, A, emb, Matrix.col] using congrFun (hcoordinate j) i
    rw [hcol_eq]
    exact hselected
  refine ⟨emb, ?_⟩
  have hunit : IsUnit M := Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  exact (M.isUnit_iff_isUnit_det.mp hunit).ne_zero

end MainTheory.DeterminantalRank
