import QECC.GeneralSSLP
import QECC.GeneralCanonicalSSLP
import QECC.SSLPConverse
import QECC.SectorTransport
import QECC.RankTwoSSLP
import QECC.RankTwoCyclicity
import QECC.RankTwoCyclicGroup
import QECC.RankTwoCanonical

/-!
The formalization of Section III.B is split into reusable layers:

* `PauliKL` encodes the full phase-free Pauli Knill--Laflamme condition;
* `SubsetSum`, `SectorDecomposition`, and `ProjectiveSectorOrder` identify
  logical phase sectors and compute their projective order;
* `ColorArithmetic` converts relative residues into primitive SSLP colors;
* `CanonicalSSLP` and `SectorTransport` implement local-X and
  qubit-permutation normalization of the code and its actual phase sectors;
* `GeneralSSLP` and `GeneralCanonicalSSLP` state the forward theorem, its
  canonical-coordinate form, and its probability/moment consequences;
* `SSLPConverse` constructs the converse code projector from an orthogonal
  family of fiber-supported component projectors;
* `RankTwoSSLP`, `RankTwoCyclicity`, `RankTwoCyclicGroup`, and
  `RankTwoCanonical` prove the rank-two sector theorem, unconditional
  cyclicity, the literal `ZMod m` group model, and the two canonical fibers.
-/
