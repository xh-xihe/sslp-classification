import MainTheory.CodeDirectoryEntry
import MainTheory.Generated.FiniteCoarseMomentBridge

/-!
# A code's row survives the moment stage

`CodeDirectoryEntry.code_enters_coarse_directory` puts a code on a *kept* row
of the coarse directory, so the code is inside the 508.  The next filter is the
moment programme, which takes the 508 to 291.

A code passes it for the same reason it passes the coarse filter, and by the
same device: each of the 508 rows carries either a rational primal point or a
rational separator, and a rational separator excludes the *real* fibre
programme too (`RealMomentSeparatorBridge.CertifiedMomentRow.not_realFeasible`).
The code supplies a real point, so its row cannot be the separator kind.

No rational point of a rational polyhedron is ever produced; the descent from
`ℝ` to `ℚ` is not needed, because only the certificate is cast.
-/

namespace MainTheory.CodeMomentFeasible

open MainTheory
open MainTheory.Generated.FinitePairMappingBase
open MainTheory.Generated.Coarse.DirectoryBase
open MainTheory.RealMomentSeparatorBridge

/-- **A kept row admitting a real moment point carries a feasible moment
row.** -/
theorem exists_feasible_output (i : PairId)
    (hkeep : MainTheory.Generated.FiniteCoarseDirectory.directory.keepAt i
      = true)
    (hf : ∃ p : RealWeight
        (MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i),
      RealFeasible
        (MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i) p) :
    ∃ j : OutputId,
      MainTheory.Generated.FiniteCoarseDirectory.directory.outputSource j = i ∧
      (MainTheory.Generated.FiniteCoarseMomentBridge.rowAt j).result.isFeasible
        = true := by
  obtain ⟨j, hj⟩ :=
    MainTheory.Generated.FiniteCoarseDirectory.validity.kept_covered i hkeep
  refine ⟨j, hj, ?_⟩
  by_contra hne
  have hfalse :
      (MainTheory.Generated.FiniteCoarseMomentBridge.rowAt j).result.isFeasible
        = false := by
    cases h : (MainTheory.Generated.FiniteCoarseMomentBridge.rowAt j).result.isFeasible
    · rfl
    · exact absurd h hne
  have hnot := CertifiedMomentRow.not_realFeasible _ hfalse
  have hpair :
      (MainTheory.Generated.FiniteCoarseMomentBridge.rowAt j).pair
        = MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i := by
    rw [MainTheory.Generated.FiniteCoarseMomentBridge.row_pair j]
    show MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt
        (MainTheory.Generated.FiniteCoarseDirectory.directory.outputSource j)
      = MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i
    rw [hj]
  rw [hpair] at hnot
  exact hnot hf

/-- **Every exact `((6,2,3))` code with a projectively nontrivial diagonal
symmetry occupies a moment-feasible row.**

Chaining `CodeDirectoryEntry.code_enters_coarse_directory`: the code is inside
the 508, and its row is one of the 291. -/
theorem code_enters_moment_stage (C : CodeSpec.ExactCode 6 2 3)
    (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ (S : MainTheory.SortedForm.SortedNormalForm C) (j : OutputId),
      S.q ≤ 9 ∧
      MainTheory.Generated.FiniteCoarseDirectory.directory.outputAt j
        = MainTheory.OuterCompleteness.recordFiberPair
            (MainTheory.CodeFiberBridge.recordOf S) ∧
      (MainTheory.Generated.FiniteCoarseMomentBridge.rowAt j).result.isFeasible
        = true := by
  obtain ⟨S, i, hq9, hi, hkeep⟩ :=
    MainTheory.CodeDirectoryEntry.code_enters_coarse_directory C theta hpres hnt
  have hf :=
    MainTheory.CodeDirectoryEntry.exists_realFeasible_of_normalForm S _ hi
  obtain ⟨j, hj, hfeas⟩ := exists_feasible_output i hkeep hf
  refine ⟨S, j, hq9, ?_, hfeas⟩
  show MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt
      (MainTheory.Generated.FiniteCoarseDirectory.directory.outputSource j)
    = MainTheory.OuterCompleteness.recordFiberPair
        (MainTheory.CodeFiberBridge.recordOf S)
  rw [hj, hi]

end MainTheory.CodeMomentFeasible
