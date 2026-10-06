# Lean formalization of Section III

This standalone Lean 4 package formalizes the abstract results in Sections
III.A, III.B, and III.C of the accompanying manuscript. The three main entry
points are:

| Section | Lean entry point | Subject |
|---|---|---|
| III.A | [`FirstTheorem.lean`](FirstTheorem.lean) | Finite diagonal logical groups and reduced physical representatives |
| III.B | [`SecondTheorem.lean`](SecondTheorem.lean) | Subset-sum logical phase (SSLP) normal form and converse |
| III.C | [`ThirdTheorem.lean`](ThirdTheorem.lean) | Abstract physical-order bounds and the distance-three refinement |

[`QECC.lean`](../QECC.lean) imports the complete development. The original
package folder is named `LeanSecIII`; the Lean modules and declarations retain
the `QECC` prefix because they formalize quantum error-correcting codes.

## About this copy

This library is Bei Zeng's standalone LeanSecIII package, which formalizes
Section III of the 20260929 manuscript. It is included here with her
agreement and ported from Lean 4.28.0 / Mathlib v4.28.0 to the Lean 4.27.0 /
Mathlib revision this repository pins. The original toolchain port changed no
statement or proof. This table records that port; later integration changes
are listed separately:

| File | Change |
|---|---|
| [`MathlibCompat.lean`](MathlibCompat.lean) | New. `AddCircle.toCircle_neg` (Mathlib) and `Nat.gcd_left_comm` (Lean core) exist in 4.28.0 but not in the pinned versions; both are copied with their upstream statement, name and proof. |
| [`Basic.lean`](Basic.lean) | One added line, `import QECC.MathlibCompat`. |
| [`DistanceThreePhaseSystem.lean`](DistanceThreePhaseSystem.lean), [`DistanceThreeOrderBound.lean`](DistanceThreeOrderBound.lean) | `set_option genInjectivity false in` before one structure each. Under Lean 4.27, generating the constructor injectivity theorems of these two dependent structures exceeds the heartbeat limit; 4.28 does it quickly. Nothing uses those theorems, and a use would fail to compile. |
| [`Audit.lean`](Audit.lean) | New. `#print axioms` for the seventeen main declarations below; read by the repository's axiom gate. |

The other 46 modules and [`QECC.lean`](../QECC.lean) are byte-identical to
the delivered package. When the repository moves to Lean and Mathlib 4.28.0,
delete `MathlibCompat.lean` and the two `set_option` lines; the backported
names will otherwise clash with upstream.

## Building in this repository

### Integration extension, 2026-10-04

`DistanceThreeOrderBound.lean` now exposes
`CodeProjector.distanceThree_physicalOrder_bound_of_representative`, retaining
the supplied physical representative through the support and Smith-bound
construction. The original `distanceThree_physicalOrder_bound` statement is
preserved as a wrapper around that proof. This lets the frame bridge bind the
bound to the same physical gate used elsewhere in the paper.

`Audit.lean` now checks eighteen roots, including this new entry point, with
the shared `#certification_axioms` command. Its transitive-axiom policy is the
same three standard axioms. These are explicit post-port integration changes.

The library is the `QECC` target in the repository's `lakefile.lean`. Build it
with the repository's serial builder, which compiles one module at a time:

```console
python tools/build_lean.py --module QECC --module QECC.Audit
```

The original package pinned Lean 4.28.0 and Mathlib v4.28.0 and was built
standalone with `lake update`, `lake exe cache get` and `lake build`.

The development contains no `sorry`, `admit`, or project-specific axioms.
It uses the standard classical and quotient principles supplied by Lean and
Mathlib.

## Common formal language

- `CodeProjector n K` is an orthogonal projector of rank `K` on `n` qubits.
- `PhaseVector n = Fin n → UnitAddCircle` records local diagonal phases in
  additive full-turn units.
- `diagonalGate theta` is the corresponding diagonal product gate.
- `C.Preserves theta` means that this gate preserves the code.
- `C.ActsAsScalar theta` means that its restriction to the code is scalar.
- `C.ProjectiveDiagonalGroup` is the additive quotient of preserving phase
  vectors by scalar phase vectors. This directly models projective logical
  actions; no ambient `PU(K)` is introduced.
- `C.HasDistanceAtLeast d` is the full phase-free Pauli Knill--Laflamme
  condition for errors of weight below `d`.

The most common order notation is:

| Paper notation | Lean representation |
|---|---|
| projective logical order `m` | `addOrderOf U` |
| reduced physical order `q` | `R.q` for a `ReducedDiagonalRepresentative` |
| number of active logical phase sectors `ell` | `Fintype.card (C.ActiveResidue R.a)` |
| common affine dimension `r` | `actualSectorAffineDimension` |
| final Smith invariant `d_s(C)` | `NonsingularBinaryMatrix.finalSmithInvariant` |
| universal binary-matrix bound `beta_nu` | `smithBeta nu` |

## Section III.A: finite diagonal logical groups

### Main declaration

`CodeProjector.finite_diagonal_logical_group_and_physical_representatives`

If every single-site Pauli `Z` is detected, the projective diagonal logical
group is finite abelian. Every nonzero class has a reduced representative
`D(a;q)` whose physical gate has exact order `q`, whose residue vector is
primitive, and whose projective logical order divides `q`.

### Proof flow

1. Convert single-site `Z` detection to detection of the number operators.
2. Encode preservation by an integral edge matrix built from nonzero entries
   of the code projector.
3. Show that real directions in the homogeneous edge kernel act as a common
   scalar on the code.
4. Apply a uniform rational-section theorem to replace every preserving phase
   by one with a code-dependent common denominator, modulo a scalar action.
5. Obtain finiteness as the image of a finite set of modular phase vectors.
6. Reduce a nonzero finite-order representative to its exact physical order;
   exact residue order supplies the gcd-one condition, and the quotient map
   shows that the projective order divides the physical order.

### Modules

| File | Role |
|---|---|
| [`Basic.lean`](Basic.lean) | Bit strings, operators, code projectors, and detection conditions |
| [`FiniteDiagonal.lean`](FiniteDiagonal.lean) | Diagonal gates, preservation and scalar actions, logical restrictions, and the projective quotient |
| [`RationalSection.lean`](RationalSection.lean) | Uniform rational lifting for consistent integral systems |
| [`UniformRepresentative.lean`](UniformRepresentative.lean) | Projector edge matrix and uniform rational representatives |
| [`ReducedRepresentative.lean`](ReducedRepresentative.lean) | Primitive modular representatives and exact physical order |
| [`FirstTheorem.lean`](FirstTheorem.lean) | Finiteness, reduced representatives, and the packaged III.A theorem |

The rational-section theorem is independent of coding theory. The detection
hypothesis is used when an edge-kernel direction is identified with a scalar
logical action.

## Section III.B: SSLP normal form

### Main declarations

- `CodeProjector.general_sslp_normal_form`
- `CodeProjector.general_sslp_canonical_normal_form`
- `CodeProjector.general_sslp_converse`
- `general_sslp_directSum_converse`
- `CodeProjector.sslp_sector_probabilities_and_moments`
- `CodeProjector.rankTwo_sslp_normal_form`
- `CodeProjector.projectiveDiagonalGroup_isAddCyclic`
- `CodeProjector.exists_projectiveDiagonalGroup_zmod_model`
- `CodeProjector.rankTwo_sslp_canonical_normal_form`

### Proof flow

1. Use Section III.A to choose a reduced representative of a nonzero
   projective class, with physical order `q` and logical order `m | q`.
2. Decompose the code into the nonzero intersections with the modular
   subset-sum fibers. These are the active logical phase sectors.
3. Prove that the relative active residues are distinct, have joint additive
   order `m`, have positive multiplicities summing to `K`, and support their
   sectors in the corresponding fibers.
4. Express the relative residues as embedded primitive colors in `ZMod m`.
5. Normalize an anchor by local `X` gates, permute qubits into canonical
   coefficient order, and transport the code and all sectors by explicit
   linear equivalences.
6. For rank two, positivity and the dimension sum force exactly two
   one-dimensional sectors. Their phase ratio gives a faithful circle
   character, which proves cyclicity. A unit power of a generator normalizes
   the two colors to `0` and `q/m`.
7. Conversely, an orthogonal family of nonzero projectors supported in
   distinct fibers produces a code preserved by the modular diagonal gate.
   Primitive colors give exact projective order. The requested code distance
   remains the full Knill--Laflamme hypothesis.

### Module groups

| Files | Role |
|---|---|
| [`PauliKL.lean`](PauliKL.lean) | Pauli errors, weights, detection, and code distance |
| [`SubsetSum.lean`](SubsetSum.lean), [`SectorDecomposition.lean`](SectorDecomposition.lean) | Subset-sum fibers, fiber subspaces, phase sectors, and active residues |
| [`ProjectiveSectorOrder.lean`](ProjectiveSectorOrder.lean) | Projective order from relative active residues |
| [`ColorArithmetic.lean`](ColorArithmetic.lean), [`ColoredSSLP.lean`](ColoredSSLP.lean) | Primitive logical colors in `ZMod m` |
| [`NormalFormTransport.lean`](NormalFormTransport.lean), [`PauliTransport.lean`](PauliTransport.lean), [`CanonicalSSLP.lean`](CanonicalSSLP.lean), [`SectorTransport.lean`](SectorTransport.lean) | Local-X and permutation normalization, including distance and sector transport |
| [`SectorProbabilities.lean`](SectorProbabilities.lean) | Sector distributions and common low-degree binary moments |
| [`GeneralSSLP.lean`](GeneralSSLP.lean), [`GeneralCanonicalSSLP.lean`](GeneralCanonicalSSLP.lean) | General forward, canonical, and existing-code converse statements |
| [`SSLPConverse.lean`](SSLPConverse.lean) | Direct-sum construction from fiber-supported projectors |
| [`RankTwoSSLP.lean`](RankTwoSSLP.lean), [`RankTwoCyclicity.lean`](RankTwoCyclicity.lean), [`RankTwoCyclicGroup.lean`](RankTwoCyclicGroup.lean), [`RankTwoCanonical.lean`](RankTwoCanonical.lean) | Rank-two sectors, cyclicity, `ZMod m` model, and canonical fibers |
| [`SecondTheorem.lean`](SecondTheorem.lean) | Section III.B overview and imports |

An active sector is a nonzero code phase sector contained in a subset-sum
fiber. It need not equal the entire fiber subspace. The probability theorem
uses binary monomials of degree below the code distance.

## Section III.C: physical-order bounds

### Main declarations

- `CodeProjector.phaseSectors_positive_probability_commonFirstMoments`
- `NonsingularBinaryMatrix.exists_integral_finalSmithInvariant_smul`
- `CodeProjector.general_physicalOrder_bound`
- `CodeProjector.distanceThree_physicalOrder_bound`
- `CodeProjector.rankTwo_distanceTwo_physicalOrder_cutoff`
- `CodeProjector.rankTwo_distanceThree_physicalOrder_cutoff`
- `CodeProjector.rankTwo_physicalOrder_cutoff`

### General bound

For a nonzero projective class on a code detecting all one-site number
operators, choose a reduced source representative and let `ell` be its number
of active phase sectors. The proof normalizes one actual support point to zero,
then forms an integral binary system with `n` physical variables and
`ell - 1` sector-offset variables. Pivoting produces a nonsingular binary
minor. A rational solution gives the same projective logical action, and the
final Smith invariant clears its denominators.

The resulting certificate contains

```text
addOrderOf U | q,
q | d_s,
q <= d_s <= smithBeta (n + ell - 1) <= smithBeta (n + K - 1),
```

together with the corresponding bound on `minimalPhysicalOrder U`.

### Distance-three refinement

`actualSectorSupport` is the positive support of the normalized diagonal of a
sector projector, rather than the full subset-sum fiber. Distance at least
three equates the first and second moments of the two rank-two sector
distributions. Equality of the squared expectation of every affine functional
then proves that their real affine spans agree.

After a local-X normalization, the anchor support contains zero. If `r` is
the common affine dimension, the formalization selects `r` independent
support rows and `r` coordinate columns. It proves that the returned binary
Smith matrix is exactly their coordinate minor. The final certificate contains

```text
2 <= addOrderOf U,
addOrderOf U | q,
q | d_r,
q <= d_r <= smithBeta r <= smithBeta n,
1 <= r <= n.
```

### Module groups

| Files | Role |
|---|---|
| [`ProjectorSupport.lean`](ProjectorSupport.lean), [`AffineMoments.lean`](AffineMoments.lean) | Actual supports, common first moments, affine-square moments, and equal affine spans |
| [`GeneralRationalReplacement.lean`](GeneralRationalReplacement.lean), [`SupportReplacement.lean`](SupportReplacement.lean) | Projective equivalence of real and rational support-equation solutions |
| [`BinaryPhaseSystem.lean`](BinaryPhaseSystem.lean), [`SectorPhaseSystem.lean`](SectorPhaseSystem.lean) | Binary systems, pivot solutions, and the `n + ell - 1` variable count |
| [`SmithBounds.lean`](SmithBounds.lean), [`SmithOrderBound.lean`](SmithOrderBound.lean), [`PhysicalOrderMin.lean`](PhysicalOrderMin.lean) | Denominator clearing, `smithBeta`, exact reduced order, and minimum-order bounds |
| [`DistanceThreePhaseSystem.lean`](DistanceThreePhaseSystem.lean), [`DistanceThreeAffineDimension.lean`](DistanceThreeAffineDimension.lean) | Anchor-only distance-three system and identification of matrix rank with affine dimension |
| [`DistanceThreeMatrixProvenance.lean`](DistanceThreeMatrixProvenance.lean) | Support-row basis and coordinate-minor provenance |
| [`GeneralPhysicalOrderBound.lean`](GeneralPhysicalOrderBound.lean), [`DistanceThreeOrderBound.lean`](DistanceThreeOrderBound.lean) | The two top-level order-bound certificates |
| [`PhysicalOrderCutoff.lean`](PhysicalOrderCutoff.lean) | Rank-two distance-two, distance-three, and piecewise symbolic cutoffs |
| [`ThirdTheorem.lean`](ThirdTheorem.lean) | Section III.C overview and imports |

`finalSmithInvariant` is represented invariantly as the additive exponent of
the integer cokernel. A binary matrix here has entries zero or one and is
nonsingular over the rationals or reals; it need not be invertible modulo two.

## Scope boundary

- Sections III.A--C concern diagonal product gates in the fixed chosen product
  basis.
- The top-level order theorems are phrased intrinsically for a nonzero
  projective logical class and record a reduced source representative.
- The Section III.C development proves the abstract Smith bounds. It does not
  assume or prove tabulated numerical values such as `beta_6 = 9`; certifying
  those finite computations is a separate numerical task.
- `main.tex` remains the mathematical exposition. The Lean files use more
  explicit certificate structures so that the matrices, representatives,
  support sectors, and divisibility statements remain available downstream.
