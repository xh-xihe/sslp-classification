import MainTheory.Generated.FiniteOrbitCertificate
import MainTheory.Generated.FiniteMomentData
import MainTheory.OuterEnumeration

/-!
# The reduction chain, in the paper's own statements

The 20260902 revision of `main.tex` breaks the six-qubit reduction
`13,877 -> 13,449 -> 12,768 -> 11,422 -> 508 -> 291 -> 215 -> 66` into eight
named lemmas and one proposition, where the previous draft ran it as
continuous prose.  Every number in the chain was already a kernel theorem
here, but each lived inside the module that produced it, under a name shaped
by the pipeline rather than by the paper.  Nothing stated the chain.

This file is that statement, and it proves nothing new: each theorem below is
the paper's lemma, discharged by the existing result.  The point of writing it
out is that a reader checking `thm:six-66-orbits` against this development
should not have to know where `nonemptyFiberRecordCount` lives.

`lem:six-active-rank-reduction` has two halves.  The pair-level one is below.
The other -- that the 215 rank-compatible pairs are *represented by 216
primitive angle records* -- is a projection back onto the pre-hashing records,
and is `ActiveRankRecordCount.compatible_record_count`, which runs it through
the provenanced record-to-pair map itself.
-/

namespace MainTheory.PaperReductionChain

open MainTheory

/-! ## `lem:six-raw-outer-count` -/

/-- **Raw outer count** (`lem:six-raw-outer-count`, `six:eq:13877`).

The exhaustive sorted outer list for the controlled data of
`six:eq:qcutoff`--`six:eq:sorted` contains exactly `13,877` records. -/
theorem raw_outer_count :
    OuterEnumeration.rawRecords.length = 13877 :=
  OuterEnumeration.raw_records_exact

/-! ## The primitive sorted-vector counts -/

/-- **Primitive sorted-vector count** (`six:eq:primitivevalues`).

`P_6(q)` for `q = 2, ..., 9`, each by kernel enumeration.  The paper also
gives the Mobius closed form `six:eq:primitiveMobius`; that inversion is not
formalized here, and these eight values are obtained by counting, not by the
formula. -/
theorem primitive_sorted_counts :
    (OuterEnumeration.primitiveAngles6 2).length = 6 ∧
      (OuterEnumeration.primitiveAngles6 3).length = 27 ∧
      (OuterEnumeration.primitiveAngles6 4).length = 77 ∧
      (OuterEnumeration.primitiveAngles6 5).length = 209 ∧
      (OuterEnumeration.primitiveAngles6 6).length = 428 ∧
      (OuterEnumeration.primitiveAngles6 7).length = 923 ∧
      (OuterEnumeration.primitiveAngles6 8).length = 1632 ∧
      (OuterEnumeration.primitiveAngles6 9).length = 2975 :=
  ⟨OuterEnumeration.primitive_two, OuterEnumeration.primitive_three,
    OuterEnumeration.primitive_four, OuterEnumeration.primitive_five,
    OuterEnumeration.primitive_six_exact, OuterEnumeration.primitive_seven_exact,
    OuterEnumeration.primitive_eight_exact, OuterEnumeration.primitive_nine_exact⟩

/-! ## `lem:six-primitivity-reduction` -/

/-- **Primitivity reduction** (`lem:six-primitivity-reduction`,
`six:eq:primitiveTotal`).

Imposing `six:eq:primitive` reduces the `13,877` raw records to `13,449`
primitive records. -/
theorem primitivity_reduction :
    OuterEnumeration.primitiveRecords.length = 13449 :=
  OuterEnumeration.primitive_records_exact

/-! ## `lem:six-nonempty-fiber-reduction` -/

/-- **Nonempty-fiber reduction** (`lem:six-nonempty-fiber-reduction`,
`six:eq:nonemptyrecords`).

Discarding records with an empty second fibre reduces the `13,449` primitive
records to `12,768`. -/
theorem nonempty_fiber_reduction :
    OuterEnumeration.nonemptyFiberRecords.length = 12768 :=
  OuterEnumeration.nonempty_fiber_records_exact

/-! ## `lem:six-fiber-hashing` -/

/-- **Exact fiber hashing** (`lem:six-fiber-hashing`, `six:eq:hashedpairs`).

Exact hashing of the labeled full-fibre pairs reduces the `12,768` nonempty
records to `11,422` distinct labeled fibre pairs.

Hashing is lossless in the strong sense the paper needs and this development
proves separately: `FinitePairProvenance.validity` shows every record points
at the exact pair computed from it and every table entry is realized by a
record, and `FinitePairProvenance.deduplicated` shows distinct entries carry
distinct payloads. -/
theorem fiber_hashing :
    MainTheory.Generated.FinitePairData.pairTable.size = 11422 :=
  MainTheory.Generated.FinitePairData.pairTable_size

/-! ## `lem:six-affine-smith-reduction` -/

/-- **Affine--Smith reduction** (`lem:six-affine-smith-reduction`,
`six:eq:508`).

The rank condition `six:eq:coarserank` reduces the `11,422` labeled pairs to
`508`. -/
theorem affine_smith_reduction :
    MainTheory.Generated.FinitePairData.coarsePairIds.size = 508 :=
  MainTheory.Generated.FinitePairData.coarsePairIds_size

/-! ## `lem:six-moment-lp-reduction` -/

/-- **Moment-LP reduction** (`lem:six-moment-lp-reduction`, `six:eq:291`).

Exact solution of the two-colour degree-two moment programme reduces the `508`
coarse survivors to `291` feasible pairs.  Each of the `508` carries an exact
rational certificate either way, so the count is a theorem about the programme
and not about a solver. -/
theorem moment_lp_reduction :
    (MainTheory.Generated.FiniteMomentData.momentResults.toList.filter
      (·.isFeasible)).length = 291 :=
  MainTheory.Generated.FiniteMomentData.moment_feasible_count

/-! ## `lem:six-active-rank-reduction` -/

/-- **Active-rank reduction** (`lem:six-active-rank-reduction`,
`six:eq:215`), at the pair level.

The active-face rank criterion `six:eq:rankcriterion` reduces the `291`
moment-feasible pairs to `215` rank-compatible pairs.  The paper's further
clause counting `216` representing primitive angle records is
`ActiveRankRecordCount.compatible_record_count`. -/
theorem active_rank_reduction :
    MainTheory.Generated.FinitePairData.compatiblePairIds.size = 215 :=
  MainTheory.Generated.FinitePairData.compatiblePairIds_size

/-! ## `lem:six-orbit-reduction` and `thm:six-66-orbits` -/

/-- **Orbit reduction** (`lem:six-orbit-reduction`, `six:eq:66`).

The Boolean-cube action on labeled fibre pairs collapses the `215`
rank-compatible pairs to exactly `66` orbits.  `HasExactlyClasses` is the
two-sided statement: every input is covered by a class representative, and no
representative is a ghost. -/
theorem orbit_reduction :
    MainTheory.FiniteOrbitPipeline.HasExactlyClasses
      MainTheory.Generated.FiniteOrbitCertificate.directory 66 :=
  MainTheory.Generated.FiniteOrbitCertificate.hasExactlyClasses

/-- **The `66` SSLP moment orbits** (`thm:six-66-orbits`), as the composite of
the eight steps above. -/
theorem six_66_orbits :
    OuterEnumeration.rawRecords.length = 13877 ∧
      OuterEnumeration.primitiveRecords.length = 13449 ∧
      OuterEnumeration.nonemptyFiberRecords.length = 12768 ∧
      MainTheory.Generated.FinitePairData.pairTable.size = 11422 ∧
      MainTheory.Generated.FinitePairData.coarsePairIds.size = 508 ∧
      (MainTheory.Generated.FiniteMomentData.momentResults.toList.filter
        (·.isFeasible)).length = 291 ∧
      MainTheory.Generated.FinitePairData.compatiblePairIds.size = 215 ∧
      MainTheory.FiniteOrbitPipeline.HasExactlyClasses
        MainTheory.Generated.FiniteOrbitCertificate.directory 66 :=
  ⟨raw_outer_count, primitivity_reduction, nonempty_fiber_reduction,
    fiber_hashing, affine_smith_reduction, moment_lp_reduction,
    active_rank_reduction, orbit_reduction⟩

end MainTheory.PaperReductionChain
