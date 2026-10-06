import QECC.SecondTheorem
import QECC.GeneralPhysicalOrderBound
import QECC.DistanceThreeOrderBound
import QECC.DistanceThreeMatrixProvenance
import QECC.PhysicalOrderCutoff

/-!
The formalization of the abstract results in Section III.C is split into
reusable layers:

* `ProjectorSupport` and `SectorProbabilities` define the actual positive
  supports of logical phase sectors and their probability distributions;
* `AffineMoments` proves that distance at least three forces the actual
  supports to have the same real affine span;
* `BinaryPhaseSystem`, `SectorPhaseSystem`, and `DistanceThreePhaseSystem`
  construct the binary systems used for rational phase replacement;
* `SmithBounds` proves denominator clearing and defines the abstract bounds
  `smithBeta`, without assuming any tabulated numerical values;
* `GeneralPhysicalOrderBound` proves the general bound with at most
  `n + ell - 1` variables;
* `DistanceThreeOrderBound` proves the rank-two distance-three refinement,
  with an `r x r` binary certificate where `r` is the common affine
  dimension of the two actual supports;
* `DistanceThreeMatrixProvenance` identifies that certificate with the
  coordinate minor of a basis matrix selected from the normalized support;
* `PhysicalOrderCutoff` records the rank-two distance-two, distance-three,
  and piecewise symbolic cutoff corollaries used by the finite enumeration.

The numerical evaluation of `smithBeta` is deliberately separate from these
abstract theorems.
-/
