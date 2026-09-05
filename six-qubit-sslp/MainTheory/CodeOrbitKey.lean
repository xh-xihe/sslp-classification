import MainTheory.CodeRankFilter
import MainTheory.CodeMomentFeasible
import MainTheory.Generated.FiniteCoarseMomentContinuity
import MainTheory.Generated.FiniteMomentRankContinuity
import MainTheory.Generated.FiniteRankOrbitContinuity
import MainTheory.Generated.FiniteOrbitCertificate

/-!
# From a code to one of the sixty-six orbit keys

The four generated continuity theorems say the stages of the pipeline hand the
same *pairs* to each other, not merely the same numeric labels:

* `FiniteCoarseMomentContinuity.coarseEntries_eq_certifiedEntries`
  (508 coarse outputs = 508 certified moment rows, with the feasibility flag);
* `FiniteMomentRankContinuity.rankEntries_eq_feasibleMomentEntries`
  (291 feasible moment rows = 291 rank rows);
* `FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries`
  (215 compatible rank rows = the orbit directory's 215 inputs);
* `FiniteOrbitCertificate.orbit_coverage`
  (every input is labelled equivalent to one of the 66 keys).

This file walks a code along them.  Nothing here is new mathematics -- the two
semantic filters were entered in `CodeDirectoryEntry`/`CodeMomentFeasible` and
`CodeRankFilter` -- but until now no statement connected an
`ExactCode 6 2 3` to `keyAt`.
-/

namespace MainTheory.CodeOrbitKey

open MainTheory
open MainTheory.FinitePipeline
open MainTheory.FiniteRankPipeline
open MainTheory.Generated.Coarse.DirectoryBase
open MainTheory.Generated.FiniteMomentRankContinuity

/-! ## 508 to 291 -/

/-- The coarse output's moment row is one of the independently certified
moment rows, with the same pair and the same feasibility flag. -/
theorem exists_momentRow (j : OutputId) :
    ∃ mr ∈ MainTheory.Generated.FiniteMomentData.certifiedRows,
      mr.pair = (MainTheory.Generated.FiniteCoarseMomentBridge.rowAt j).pair ∧
        mr.result.isFeasible =
          (MainTheory.Generated.FiniteCoarseMomentBridge.rowAt j).result.isFeasible := by
  have hmem :
      MainTheory.Generated.FiniteCoarseMomentContinuity.ofRow
          (MainTheory.Generated.FiniteCoarseMomentBridge.rowAt j)
        ∈ MainTheory.Generated.FiniteCoarseMomentContinuity.coarseEntries := by
    simp only [MainTheory.Generated.FiniteCoarseMomentContinuity.coarseEntries,
      List.mem_toArray, List.mem_ofFn]
    exact ⟨j, rfl⟩
  rw [MainTheory.Generated.FiniteCoarseMomentContinuity.coarseEntries_eq_certifiedEntries]
    at hmem
  simp only [MainTheory.Generated.FiniteCoarseMomentContinuity.certifiedEntries,
    List.mem_toArray, List.mem_map] at hmem
  obtain ⟨mr, hmr, heq⟩ := hmem
  refine ⟨mr, hmr, ?_, ?_⟩
  · exact congrArg MainTheory.Generated.FiniteCoarseMomentContinuity.MomentEntry.pair heq
  · exact congrArg MainTheory.Generated.FiniteCoarseMomentContinuity.MomentEntry.feasible heq

/-! ## 291 to the rank rows -/

/-- A feasible certified moment row is matched by a rank row carrying the same
pair. -/
theorem exists_rankRow {mr : CertifiedMomentRow}
    (hmem : mr ∈ MainTheory.Generated.FiniteMomentData.certifiedRows)
    (hf : mr.result.isFeasible = true) :
    ∃ rr ∈ MainTheory.Generated.FiniteRankData.certifiedRows,
      rr.row.pair = mr.pair := by
  have hfil : mr ∈ MainTheory.Generated.FiniteMomentData.certifiedRows.filter
      (fun row => row.result.isFeasible) := by
    exact List.mem_filter.2 ⟨hmem, by simp [hf]⟩
  have hmem2 : ofMomentRow mr ∈ feasibleMomentEntries := by
    simp only [feasibleMomentEntries, List.mem_toArray, List.mem_map]
    exact ⟨mr, hfil, rfl⟩
  rw [← rankEntries_eq_feasibleMomentEntries] at hmem2
  simp only [rankEntries, List.mem_toArray, List.mem_map] at hmem2
  obtain ⟨rr, hrr, heq⟩ := hmem2
  exact ⟨rr, hrr, congrArg PairEntry.pair heq⟩

/-! ## The rank rows to the orbit inputs -/

/-- A compatible rank row's pair is one of the orbit directory's 215
inputs. -/
theorem exists_orbitInput {rr : CertifiedRankRow}
    (hmem : rr ∈ MainTheory.Generated.FiniteRankData.certifiedRows)
    (hc : rr.row.compatible = true) :
    ∃ i : Fin 215,
      MainTheory.Generated.FiniteOrbitBase.inputAt i = rr.row.pair := by
  have hfil : rr.row ∈ MainTheory.Generated.FiniteRankData.compatibleRows := by
    refine List.mem_filter.2 ⟨?_, by simp [hc]⟩
    exact List.mem_map.2 ⟨rr, hmem, rfl⟩
  have hmem2 : ofRankRow rr.row ∈
      MainTheory.Generated.FiniteRankOrbitContinuity.compatibleRankEntries := by
    simp only [MainTheory.Generated.FiniteRankOrbitContinuity.compatibleRankEntries,
      List.mem_toArray, List.mem_map]
    exact ⟨rr.row, hfil, rfl⟩
  rw [← MainTheory.Generated.FiniteRankOrbitContinuity.orbitInputEntries_eq_compatibleRankEntries]
    at hmem2
  simp only [MainTheory.Generated.FiniteRankOrbitContinuity.orbitInputEntries,
    List.mem_toArray, List.mem_map] at hmem2
  obtain ⟨e, he, heq⟩ := hmem2
  have hpair : e.2 = rr.row.pair :=
    congrArg PairEntry.pair heq
  have hsnd : e.2 ∈ List.ofFn MainTheory.Generated.FiniteOrbitBase.inputAt :=
    (List.of_mem_zip he).2
  obtain ⟨i, hi⟩ := List.mem_ofFn.1 hsnd
  exact ⟨i, hi.trans hpair⟩

/-! ## The whole chain -/

/-- **Every exact `((6,2,3))` code carrying a projectively nontrivial diagonal
symmetry occupies one of the sixty-six orbit keys.**

This is the statement the certified chain `13,877 -> ... -> 66` never had: up
to now `thm:six-66-orbits` classified a list, and nothing said a code appears
on it.  Both semantic filters are entered from the code itself -- the coarse
one by its pivot and its own moment point, the rank one additionally by the
real form of `six:eq:forcedzero` and the equal-active-rank lemma. -/
theorem code_reaches_orbit_key (C : CodeSpec.ExactCode 6 2 3)
    (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ (S : MainTheory.SortedForm.SortedNormalForm C) (k : Fin 66),
      MainTheory.DistanceSignature.LabeledEquivalent
        (MainTheory.OuterCompleteness.recordFiberPair
          (MainTheory.CodeFiberBridge.recordOf S)).q
        (MainTheory.OuterCompleteness.recordFiberPair
          (MainTheory.CodeFiberBridge.recordOf S)).m
        (MainTheory.FiniteOrbitPipeline.fibersOfPair
          (MainTheory.OuterCompleteness.recordFiberPair
            (MainTheory.CodeFiberBridge.recordOf S)))
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).q
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).m
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
      (∀ v : MainTheory.ClassificationLevels.diagonalSymmetryGroup
          (MainTheory.GlobalClassificationBridge.exactCodeProjector C),
        (∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
          * ((theta j : ℝ) : ℂ))
            = (((v : MainTheory.ClassificationLevels.LocalPhase 6) j : ℂ))) →
        S.m = orderOf (MainTheory.ClassificationLevels.intrinsicClass
          (MainTheory.GlobalClassificationBridge.exactCodeProjector C) v)) := by
  obtain ⟨S, P, hq9, hzero, hS0, hord⟩ :=
    MainTheory.SortedPivotConstruction.exists_normalForm_pivot_full C theta hpres hnt
  obtain ⟨i, hi⟩ := MainTheory.CodeDirectoryEntry.exists_row_of_normalForm S hq9
  have hkeep := MainTheory.CodeDirectoryEntry.keepAt_of_normalForm S hS0 i hi
  have hf := MainTheory.CodeDirectoryEntry.exists_realFeasible_of_normalForm S _ hi
  obtain ⟨j, hj, hfeas⟩ :=
    MainTheory.CodeMomentFeasible.exists_feasible_output i hkeep hf
  obtain ⟨mr, hmr, hmrpair, hmrfeas⟩ := exists_momentRow j
  -- the coarse row's pair is the code's own
  have hrowpair :
      (MainTheory.Generated.FiniteCoarseMomentBridge.rowAt j).pair
        = MainTheory.OuterCompleteness.recordFiberPair
            (MainTheory.CodeFiberBridge.recordOf S) := by
    rw [MainTheory.Generated.FiniteCoarseMomentBridge.row_pair j]
    show MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt
        (MainTheory.Generated.FiniteCoarseDirectory.directory.outputSource j)
      = _
    rw [hj, hi]
  obtain ⟨rr, hrr, hrrpair⟩ := exists_rankRow hmr (hmrfeas.trans hfeas)
  have hpair : rr.row.pair
      = MainTheory.OuterCompleteness.recordFiberPair
          (MainTheory.CodeFiberBridge.recordOf S) := by
    rw [hrrpair, hmrpair, hrowpair]
  have hcompat : rr.row.compatible = true :=
    MainTheory.CodeRankFilter.compatible_of_pivot_certified P rr hrr hpair
      (MainTheory.CodeDirectoryEntry.realFeasible_weightOf_of_normalForm S _ hpair)
      hzero
  obtain ⟨i2, hi2⟩ := exists_orbitInput hrr hcompat
  obtain ⟨k, hk⟩ := MainTheory.Generated.FiniteOrbitCertificate.orbit_coverage i2
  refine ⟨S, k, ?_, hord⟩
  rw [hi2, hpair] at hk
  exact hk

end MainTheory.CodeOrbitKey
