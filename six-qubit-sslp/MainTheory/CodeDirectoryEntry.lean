import MainTheory.CodeMomentPoint
import MainTheory.CoarseFilterUnconditional
import MainTheory.SortedPivotConstruction
import MainTheory.Generated.FinitePairProvenance

/-!
# From a code to a row of the coarse directory

`CodeFiberBridge.recordOf_mem_nonemptyFiber` carries a code's sorted normal
form into the 12,768 surviving outer records, and there it stopped: nothing
took the record on to the 11,422 deduplicated fibre pairs, which is where the
generated directory is indexed.  Fifteen files mention `keyAt` and none of them
mentions `ExactCode 6 2 3`; twenty-seven mention `ExactCode 6 2 3` and none of
them mentions `keyAt`.  That is the gap this file starts to close.

The step across is `PairProvenance`: the generated table's `recordToPair`
assigns every outer record a pair id, and its `exactRecord` obligation says the
payload stored there is *the record's own* fibre pair -- not merely one
equivalent to it.  So a code does not just occupy some row; it occupies a row
whose stored data is the code's two residue fibres.

With that identification the two inputs of `CoarseFilterUnconditional` are both
available for a code: `SortedPivotConstruction.exists_normalForm_s0Clause`
gives the `S_0` clause, and `CodeMomentPoint.exists_realFeasible` gives the
real moment point.  Hence a code's row is kept, and the code enters the 508.
-/

namespace MainTheory.CodeDirectoryEntry

open MainTheory
open MainTheory.CodeFiberBridge
open MainTheory.OuterCompleteness
open MainTheory.SortedForm
open MainTheory.Generated.FinitePairMappingBase

noncomputable section

/-! ## The record's own row -/

/-- The pair id assigned to an outer record by the generated provenance
table. -/
def pairIdOfIndex (i : PairProvenance.OuterRecordIndex) : PairId :=
  MainTheory.Generated.FinitePairProvenance.table.recordToPair i

set_option maxRecDepth 40000 in
/-- **The row a record occupies stores that record's own fibre pair.** -/
theorem inputAt_pairIdOfIndex (i : PairProvenance.OuterRecordIndex) :
    MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt
        (pairIdOfIndex i)
      = recordFiberPair (PairProvenance.outerRecord i) := by
  rw [MainTheory.Generated.FiniteCoarseDirectory.inputAt_eq_pairAtId]
  exact MainTheory.Generated.FinitePairProvenance.exactRecord i

/-- Every surviving outer record is indexed. -/
theorem exists_index_of_mem {r : OuterEnumeration.RawRecord}
    (h : r ∈ OuterEnumeration.nonemptyFiberRecords) :
    ∃ i : PairProvenance.OuterRecordIndex, PairProvenance.outerRecord i = r := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.1 h
  exact ⟨i, hi⟩

/-- **A code's sorted normal form occupies a directory row carrying its own
two residue fibres.** -/
theorem exists_row_of_normalForm {C : CodeSpec.ExactCode 6 2 3}
    (S : SortedNormalForm C) (hq9 : S.q ≤ 9) :
    ∃ i : PairId,
      MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i
        = recordFiberPair (recordOf S) := by
  obtain ⟨idx, hidx⟩ := exists_index_of_mem (recordOf_mem_nonemptyFiber S hq9)
  refine ⟨pairIdOfIndex idx, ?_⟩
  rw [inputAt_pairIdOfIndex, hidx]

/-! ## The code supplies both filter inputs on that row -/

/-- The normal form's frame, written as the two-element list the
Knill--Laflamme predicate of `SixQubit.CodeBridge` expects. -/
theorem hasDistance_pair {C : CodeSpec.ExactCode 6 2 3}
    (S : SortedNormalForm C) :
    SS.HasDistance ![S.frame.vec 0, S.frame.vec 1] 3 := by
  have hveq : S.frame.vec = ![S.frame.vec 0, S.frame.vec 1] := by
    funext k
    fin_cases k <;> rfl
  have h := S.hasDistance
  rwa [hveq] at h

/-- **A code supplies a real moment point on any pair equal to its own.**

Stated with the pair as a variable so that the dependent type `RealWeight pair`
can be discharged by substitution rather than by rewriting under a binder. -/
theorem exists_realFeasible_of_normalForm {C : CodeSpec.ExactCode 6 2 3}
    (S : SortedNormalForm C) (pair : FinitePipeline.FiberPair)
    (hpair : pair = recordFiberPair (recordOf S)) :
    ∃ p : MainTheory.RealMomentSeparatorBridge.RealWeight pair,
      MainTheory.RealMomentSeparatorBridge.RealFeasible pair p := by
  subst hpair
  exact MainTheory.CodeMomentPoint.exists_realFeasible _
    (S.frame.vec 0) (S.frame.vec 1)
    (fun x hx => support_mask0 S x hx)
    (fun x hx => support_mask1 S x hx)
    (by simpa using S.frame.orthonormal 0 0)
    (by simpa using S.frame.orthonormal 1 1)
    (hasDistance_pair S)

/-- The same, naming the point rather than only asserting one exists.  The
rank filter needs the code's *own* distribution, because it is what the active
face is read off. -/
theorem realFeasible_weightOf_of_normalForm {C : CodeSpec.ExactCode 6 2 3}
    (S : SortedNormalForm C) (pair : FinitePipeline.FiberPair)
    (hpair : pair = recordFiberPair (recordOf S)) :
    MainTheory.RealMomentSeparatorBridge.RealFeasible pair
      (MainTheory.CodeMomentPoint.weightOf pair
        (S.frame.vec 0) (S.frame.vec 1)) := by
  subst hpair
  exact MainTheory.CodeMomentPoint.realFeasible_weightOf _
    (S.frame.vec 0) (S.frame.vec 1)
    (fun x hx => support_mask0 S x hx)
    (fun x hx => support_mask1 S x hx)
    (by simpa using S.frame.orthonormal 0 0)
    (by simpa using S.frame.orthonormal 1 1)
    (hasDistance_pair S)

/-- **A code's row is kept by the coarse filter.**

Both inputs are supplied by the code itself: the `S_0` clause by the sorted
normal form's pivot, and the real moment point by the code's own pair of
probability distributions. -/
theorem keepAt_of_normalForm {C : CodeSpec.ExactCode 6 2 3}
    (S : SortedNormalForm C)
    (hS0 : CoarseFilterSound.S0Clause (recordFiberPair (recordOf S)))
    (i : PairId)
    (hi : MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i
      = recordFiberPair (recordOf S)) :
    MainTheory.Generated.FiniteCoarseDirectory.directory.keepAt i = true := by
  refine MainTheory.CoarseFilterUnconditional.keepAt_of_s0_of_feasible i ?_ ?_
  · rw [hi]; exact hS0
  · exact exists_realFeasible_of_normalForm S _ hi

/-- **Every exact `((6,2,3))` code with a projectively nontrivial diagonal
symmetry occupies a kept row of the coarse directory, and that row stores the
code's own two residue fibres.**

This is the entrance the certified chain `13,877 -> ... -> 66` never had. -/
theorem code_enters_coarse_directory (C : CodeSpec.ExactCode 6 2 3)
    (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ (S : SortedNormalForm C) (i : PairId),
      S.q ≤ 9 ∧
      MainTheory.Generated.FiniteCoarseDirectory.directory.inputAt i
        = recordFiberPair (recordOf S) ∧
      MainTheory.Generated.FiniteCoarseDirectory.directory.keepAt i = true := by
  obtain ⟨S, hq9, hS0⟩ :=
    MainTheory.SortedPivotConstruction.exists_normalForm_s0Clause C theta hpres hnt
  obtain ⟨i, hi⟩ := exists_row_of_normalForm S hq9
  exact ⟨S, i, hq9, hi, keepAt_of_normalForm S hS0 i hi⟩

end

end MainTheory.CodeDirectoryEntry
