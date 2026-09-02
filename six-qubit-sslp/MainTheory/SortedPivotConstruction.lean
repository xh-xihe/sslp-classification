import MainTheory.SortedPivot
import MainTheory.D3BoundedNormalForm

/-!
# Building the pivot where the normal form is built

`SortedPivot` reduced the coarse-filter entry to one statement about a sorted
normal form: its left support, restricted to the coordinates its angle
touches, spans.  `SortedPivot.span_rqpoint_of_shifted_nonsingular` transports
that across the cube shift separating the normal form from the fresh sparse
pivot.  What is left, and what this file does, is name the two sides.

* The **fresh** side is `frameFreshSparsePhase T`, whose `data.minor` is by
  definition `data.row i (data.coordinate j)` and whose `data_row` field says
  `data.row = bitRows basis.vertex`.  So the minor *is* the bit matrix of
  `basis.vertex` on `data.coordinate`, which is the shape the transport wants.
* The **normal form** side is `S.frame.vec 0`, and `S.frame_eq` says exactly
  how it factors: a coordinate permutation `S.perm`, then a shift by `S.x0`,
  applied to `S.source`.

`exists_sortedNormalForm_of_generator'` keeps `S.source` and the fact that the
shift is by a supported point, which is the hypothesis the transport needs on
that side; `TwoFiberCertificate.base_supported` supplies the same on the fresh
side.
-/

namespace MainTheory.SortedPivotConstruction

open MainTheory
open MainTheory.SortedForm
open MainTheory.SixQubitSemanticEntrance
open MainTheory.D3NormalizedFreshPhase

noncomputable section

variable {n : ℕ}

/-! ## The fresh side is a bit matrix -/

/-- The sparse pivot's minor is the bit matrix of its own supported basis on
its own selected coordinates.  Both halves are definitional; this records the
composite in the shape the transport consumes. -/
theorem freshMinor_eq {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : D3FreshSparseAssembly.FreshSparsePhase c d theta) (i j : Fin F.basis.rank) :
    F.data.minor i j =
      if F.basis.vertex i (F.data.coordinate j) then 1 else 0 := by
  rw [D3SparseRationalization.Data.minor, F.data_row,
    D3SparseRationalization.bitRows]

/-- Hence the minor is the matrix the transport expects, verbatim. -/
theorem freshMinor_det_ne_zero {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : D3FreshSparseAssembly.FreshSparsePhase c d theta) :
    (Matrix.of fun i j =>
      if F.basis.vertex i (F.data.coordinate j) then (1 : ℤ) else 0).det ≠ 0 := by
  have hEq : (Matrix.of fun i j =>
      if F.basis.vertex i (F.data.coordinate j) then (1 : ℤ) else 0)
      = F.data.minor := by
    funext i j
    exact (freshMinor_eq F i j).symm
  rw [hEq]
  exact F.data.minor_nonsingular

/-! ## The two supports -/

/-- The zero word lies in the normalized support: the shift is by a point of
the first logical word's own support. -/
theorem zero_mem_normalizedSupport {d q : ℕ} [NeZero q]
    {C : CodeSpec.ExactCode n 2 d}
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    (normalizedFrame T).vec 0 (fun _ => false) ≠ 0 := by
  have hval : (normalizedFrame T).vec 0 (fun _ => false)
      = G.eigenFrame.vec 0 T.x0 := by
    simp [normalizedFrame, normalizedState]
  rw [hval]
  exact T.base_supported

/-- The same on the normal form's own side.  Permuting the all-false string
leaves it alone, and shifting it by `x0` gives `x0`. -/
theorem zero_mem_sortedSupport {d : ℕ} {C : CodeSpec.ExactCode n 2 d}
    (S : SortedNormalForm C) (hbase : S.source.vec 0 S.x0 ≠ 0) :
    S.frame.vec 0 (fun _ => false) ≠ 0 := by
  rw [S.frame_eq]
  have hperm : SixQubit.CodeEquiv.permStr S.perm (fun _ => false)
      = (fun _ : Fin n => false) := by
    funext i
    simp [SixQubit.CodeEquiv.permStr]
  rw [hperm]
  have hb : SS.bxor (fun _ : Fin n => false) S.x0 = S.x0 := by
    funext i
    simp [SS.bxor]
  rw [hb]
  exact hbase

end

end MainTheory.SortedPivotConstruction
