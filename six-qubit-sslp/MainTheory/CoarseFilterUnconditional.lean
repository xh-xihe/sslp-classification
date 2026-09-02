import MainTheory.Generated.CoarseRightRowsData

/-!
# The coarse filter, with no unproved input

`CoarseFilterSound.keepAt_of_s0_of_feasible` carried one hypothesis: that a
right-rejected row's pair is one of the 422 certified moment-infeasible ones.
`Generated.CoarseRightRowsData.rejectRight_mem` discharges it, so the
statement below has no hypothesis beyond the two a code supplies.

What this buys.  The paper's coarse filter is justified by `q <= beta_r` at
the **affine** rank of the actual support (`six:eq:ractual`,
`six:eq:qbetar`).  This development proves only the linear-rank version, and
the two differ by one exactly when the origin lies outside the support's
affine hull (`results/coarse-filter-audit.md`).  The theorem here needs
neither: it uses the `S_0` clause, which the linear-rank bound does give
because the zero-residue fibre contains the all-zero word
(`MaskRankBridge.residueZeroMask_affineRank_eq_span`), together with the fact
that a code supplies a common moment point and every right-rejected row admits
none.

No number the paper reports changes: the directory still has 508 outputs.
-/

namespace MainTheory.CoarseFilterUnconditional

open MainTheory.CoarseFilter
open MainTheory.CoarseFilterSound
open MainTheory.FinitePipeline
open MainTheory.Generated.FiniteCoarseDirectory
open MainTheory.Generated.FinitePairMappingBase

/-- **The coarse filter keeps every row a code could occupy.**

`h0` is the `S_0` clause, which `CoarseFilterEntry` derives from a code's own
support; `hf` is the code's own pair of distributions. -/
theorem keepAt_of_s0_of_feasible (i : PairId)
    (h0 : S0Clause (directory.inputAt i))
    (hf : ∃ p0 p1, Feasible (directory.inputAt i) p0 p1) :
    directory.keepAt i = true :=
  MainTheory.CoarseFilterSound.keepAt_of_s0_of_feasible i
    (MainTheory.Generated.CoarseRightRows.rejectRight_mem i) h0 hf

/-- The same, phrased through the intrinsic two-clause criterion: for a row a
code could occupy, the criterion holds -- including the clause whose stated
justification could not be reconstructed. -/
theorem fullFiberCriterion_of_s0_of_feasible (i : PairId)
    (h0 : S0Clause (directory.inputAt i))
    (hf : ∃ p0 p1, Feasible (directory.inputAt i) p0 p1) :
    FullFiberCriterion (directory.inputAt i) :=
  MainTheory.CoarseFilterSound.fullFiberCriterion_of_s0_of_feasible i
    (MainTheory.Generated.CoarseRightRows.rejectRight_mem i) h0 hf

/-- Consequently such a row occurs in the 508-row output directory. -/
theorem exists_output_of_s0_of_feasible (i : PairId)
    (h0 : S0Clause (directory.inputAt i))
    (hf : ∃ p0 p1, Feasible (directory.inputAt i) p0 p1) :
    ∃ j : Fin 508, directory.outputSource j = i :=
  MainTheory.Generated.FiniteCoarseDirectory.kept_covered i
    (keepAt_of_s0_of_feasible i h0 hf)

end MainTheory.CoarseFilterUnconditional
