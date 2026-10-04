ORBIT-2 LEAN VERIFICATION — COMPLETE ENUMERATOR FORMALIZATION

Status
------
The orbit-2 enumerator image is now proved end to end in Lean. The main
results are in Orbit2/Complete.lean:
  Encoder.enumerator
  Encoder.A3_zero
  Encoder.exact_distance_three
  orbit2_exact_enumerator_image
They use only the Encoder fields: two orthonormal six-qubit logical words,
full Pauli Knill--Laflamme detection through weight two, and logical IIZZZZ
acting with eigenvalues +1 and -1. No flatness, frame, spectral, quartic,
Gram-positivity, or five-qubit-seed correctness assumption is added.
All analytic reductions, the matrix-to-polynomial bridge, exact rational
certificate, enumerator transport, and parameter attainment are checked.
There are no sorry declarations, native_decide calls, or custom axioms.
The final axiom audit reports only propext, Classical.choice, and Quot.sound.

Formal theorem statement
---------------------------
V : C^2 -> C^64 is an isometry; IIZZZZ V = V Z; V* E V is scalar for every
Hermitian Pauli error of weight <= 2. With P = VV* and
A_w = sum_{wt(E)=w} (Tr(P E)/2)^2, the proposed conclusion is
  A = (1,alpha,1-alpha,0,11+4alpha,16-alpha,3-3alpha), 0 <= alpha <= 1,
and every alpha in this interval is attained. This is an enumerator image,
not a classification of projectors under local unitaries.

Lean-checked results
--------------------
Certificate.lean:
  An explicit rational factorization A = L diag(d) L^T, with d > 0,
  gives positive semidefiniteness over R and nonnegative Hermitian quadratic
  forms for EVERY complex vector. For A = M-4I it proves
    4 sum_i |z_i|^2 <= Re(z* M z).
  The real/imaginary quadratic form is proved equal to Re(z* M z).
  Only the weak inequality needed for rigidity is asserted; this package
  does not separately prove strict positive definiteness of the shifted matrix.

Blocks/Block000.lean through Blocks/Block110.lean:
  All 111 integer matrices M and complete rational L and d factors are
  explicit. Lean checks every positive pivot and every factorization entry
  with `decide +kernel`, which evaluates in the logical kernel, NOT with
  `native_decide`. Thus Python is an untrusted certificate producer.
  Total block dimension: 492. Largest block: 24.

BlockFamily.lean and Global.lean:
  Assemble the blocks into a concrete polynomial in 32 complex t-coordinates.
  Verify the Pauli support labels (one transverse factor, weight one or three),
  and verify that all 24 weight-three coefficient squares occur in the blocks.
  checked_polynomial_rigidity proves that all 48 real target coefficients and
  all 24 complex weight-three coefficients vanish, under the EXPLICIT input
    familyEnergy checkedBlocks (quadraticMonomials t) = -sum_e c_e^2.
  Positivity/coercivity is proved from the concrete checked blocks; it is not
  an assumption of this theorem. Complete.lean now proves the required
  nonpositivity from the physical equations and trace polynomial.

Analytic.lean:
  The three stated scalar complementary-purity equations plus nonnegative
  masses imply b=m=w=0 and a+u+v=1. The shadow inequality eliminates the
  additional spectator mass. Finite diagonal spectral saturation does not
  divide by amplitudes. The final quartic implication and the enumerator
  line/plane algebra are checked with explicit hypotheses.

MacWilliams.lean:
  Checks the 7x7 integer Krawtchouk table against its binomial definition.
  A_0=1 and B_j=A_j for j=0,1,2, using the transform factor 1/32, imply the
  exact stated normal form. Also checks the alternating spin-flip scalar
  identity. Its applicability is now proved separately in the physical modules.

PhysicalMacWilliams.lean, PhysicalShadow.lean, PhysicalB.lean, Encoder.lean:
  Define an actual Encoder using only two orthonormal logical words, full
  Pauli KL detection through weight two, and the chosen logical IIZZZZ action.
  Prove normalization, nonnegativity, all physical MacWilliams equations and
  the shadow inequality from those fields. PhysicalB derives the full B
  transform, rather than assuming its Krawtchouk table. General supporting
  proofs are vendored locally; see vendored_sources.txt.

TensorPauli.lean and HilbertBridge.lean:
  Define actual tensor matrices, prove multiplication, Hermiticity, traces,
  and the exact Gaussian-integer word-trace algorithm. Prove that this matrix
  action agrees with the SS Hilbert-state Pauli action, including Y phases,
  basis indexing, and compression. Sparse trace expansion identities are
  proved for arbitrary complex coefficients.

CharacterBlocks.lean and PauliConjugation.lean:
  Prove the character gate discards only coefficients already zero. Prove
  all off-block zeros and the actual single-site conjugation/six-word trace
  shortcut used in J. These are structural proofs from finite local Pauli
  multiplication, rather than assumed global sparsity patterns.

QuarticCoefficients.lean, Coefficients/, ZeroExtension.lean,
ReconstructionBase.lean, Reconstruction.lean:
  Check all 3584 within-character coefficients, including all zero rows.
  Prove their matrices coincide with twice the very matrices used in the
  LDL proofs; verify the embeddings/retractions of positive coordinates.
  Prove the energy identity after extending by the 36 zero coordinates,
  for every complex vector. Verify coverage and uniqueness of all 528
  monomials and each character, and cross-block zeros. The assembled
  reconstructed coefficient polynomial equals familyEnergy with the exact
  factor 1/24 versus 1/12. The full operator expansion and monomial/block
  regrouping are proved in the modules described below.

Frames.lean and Defects.lean:
  Construct Pi, Omega and T from an orthonormal eight-column frame; prove
  projector identities, Omega skew symmetry, both partial-isometry equations,
  the common-J lift and its trace normalization. Derive N=1/2, F=0 and R=0
  from the common-J equation and spin flip. These theorems still take the
  frame and common-J equation as explicit inputs. PhysicalCommonJ and
  PhysicalDefects now discharge these inputs for every Encoder.

SpectatorFrames.lean, FrameConstruction.lean, FrameKL.lean, FrameSpin.lean,
MagicBasis.lean, PhysicalCommonJ.lean, PhysicalDefects.lean:
  Derive spectator Pauli detection, the full diagonal spectator density I/4,
  and zero off-diagonal spectator density. Construct the Schmidt frames
  directly from the encoder amplitudes, prove eight-column orthonormality
  and the opposite parity sectors. Prove the physical/frame compression
  trace identity including its spectator transpose, and derive every mixed
  trace zero. Full mixed KL kills all weight-one spectator coefficients of
  each active compression block, implying spin symmetry. All spectator
  coefficients of the diagonal block sum vanish except the identity.
  Define an explicit Gaussian-integer magic basis and prove its normalized
  unitarity and spin identity. Derive ordinary symmetric blocks and their
  scalar diagonal sum, then the common-J equation for every physical Encoder.
  Construct Encoder.physicalT and prove, without extra encoder fields,
    normMass T=1/2, projectionDefect T=0,
    compressionDefect T sigma=0 for all twelve single-site Paulis.

Purification.lean, TensorEncoder.lean, PurificationKL.lean,
PurificationSymmetry.lean, PurityDefinitions.lean, PurityCases/,
PurityReduction.lean, PhysicalFlatness.lean, LowWeightFlatness.lean:
  Define the actual purified Encoder and prove its norm and complementary
  purity from Pauli Parseval. Derive reference KL zeros, logical-G pairing,
  and parity zeros from the encoder fields. Check a fixed coefficient
  identity on all 4^7 Pauli labels in 64 disjoint kernel-checked batches.
  Derive the physical purity combination and vanishing of all spectator,
  mixed spectator-Z, and four-transverse masses. Prove the remaining active
  mass is supported through weight three, compare it to the full physical
  low-weight enumerator, and use shadow to prove Encoder.flat:
    forall V : Encoder, V.A 1 + V.A 2 + V.A 3 = 1.
  This result has NO assumed purity, correlation, flatness, or frame fields.
  Encoder.enumerator_of_rigidity now requires only V.A 3=0 to derive the
  claimed enumerator line and parameter interval.

PauliReconstruction.lean:
  Proves actual Pauli matrix completeness and normalized trace reconstruction
  for every complex matrix on any number of qubits, by tensoring exact local
  Gaussian-integer identities. Thus operator-basis spanning is proved.

ActiveProjector.lean, EnumeratorTransport.lean, ProjectorSupport.lean:
  Construct the actual rank-eight active projector and prove its exact
  normalized-trace relation to the physical six-qubit Pauli coefficients.
  Derive vanishing of every spectator-dressed mass through weight three.
  Prove A3 = 4 sum_{active weight 3} normSq(tau(E Pi)), the absence of
  longitudinal coefficients of weight >=2, the four-transverse zeros,
  zero opposite-corner entries, and the exact projector diagonal formula.

FrameParity.lean, SpectralGeometry.lean, PhysicalSpectral.lean, TSupport.lean:
  Prove the physical projector preserves parity and Omega reverses it.
  Derive the diagonal common-J moment equations. The projector diagonal,
  opposite-corner zeros, and positivity of squared amplitudes imply the
  spectral saturation without dividing by row norms. Thus Omega has ONLY
  Hamming-distance-three entries and T ONLY distance-one entries, for every
  actual Encoder. Prove the actual four-qubit spin transpose/skew identities.

PhysicalPauliSupport.lean, TraceReality.lean, FinalReduction.lean:
  Derive zero Pauli traces outside the exact 32 certificate labels from
  Hamming support and spin skew-symmetry, prove completeness/injectivity,
  and prove T equals the sparse expansion in its true normalized trace
  coordinates. Prove the four-word traces are real and the phase products
  with equal Pauli character are real, using spin symmetry rather than an
  assumed imaginary-coefficient cancellation. Prove that vanishing of the
  24 weight-three T coordinates implies the actual physical A3=0.
  Encoder.enumerator_of_certificate_nonpositive proves the proposed
  enumerator and parameter interval for every Encoder, under JUST the
  explicit input
    familyEnergy checkedBlocks (quadraticMonomials V.physicalT_coordinates) <= 0.
  Complete.lean discharges this input using the physical defect equations
  and the checked polynomial expansions, giving Encoder.enumerator.

FiveQubit.lean, FiveQubitPhysical.lean, SplitSeed.lean, SplitPhysical.lean,
Attainment.lean, ExactDistance.lean:
  Construct explicit Gaussian-integer amplitudes for the pure five-qubit
  seed with logical ZZZII. Check every weight <=2 Pauli compression, then
  transport those checks to actual complex matrices. Check the full split
  family's degree-two compression coefficients and logical IIZZZZ action.
  Prove KL and isometry for arbitrary real a,b with a^2+b^2=1, and build an
  actual Encoder. Derive A1=(a^2-b^2)^2, A2=(2ab)^2, A3=0 from the physical
  shadow bound, and the complete enumerator from physical MacWilliams.
  Square-root identities prove parameter coverage, including both endpoints.
  every_parameter_attained_exact_distance proves, UNCONDITIONALLY:
    forall alpha, 0 <= alpha <= 1 -> exists V : Encoder,
      A(V) = enumeratorLine alpha and not HasDistance V.psi 4.
  The exclusion of distance four uses the physical B3 transform. There is
  no assumed five-qubit-code correctness or Singleton bound in this result.

MatrixSteps.lean:
  Checks h J + J h^T = 2 mu J from symmetric blocks and their prescribed sum.
  Checks W*W=I, ZZ W=W Z and the split projection formula from a^2+b^2=1.
  These do not, by themselves, derive mixed KL or the distance of the split code.

Orbit2.lean:
  Imports the development and prints axiom dependencies of the main results.
  The only dependencies are Lean/Mathlib's propext, Classical.choice and
  Quot.sound. There is no sorryAx, custom axiom, or native computation oracle.

Completion of the operator-to-certificate bridge
------------------------------------------------
ContractionExpansion.lean:
  Expands the actual projection-defect contraction into orderedPolynomial
  gCoeff. Derives the normalized mass and delta sums from actual Pauli
  orthogonality, including the factor two.

JExpansion.lean:
  Expands the actual weighted compression-defect contractions into
  orderedPolynomial jCoeff. Proves both six-Pauli trace reductions and the
  correlation-product phase identity, with the exact factor four.

CExpansion.lean:
  Expands weighted products of actual Pauli correlations into orderedPolynomial
  cCoeff. Equal-character phase products are proved real, so the integer
  real-part coefficient is the full complex coefficient.

PhysicalQuartic.lean:
  Proves the ordered g and J polynomials vanish for physical coordinates.
  Derives every forbidden correlation zero from the actual active projector.
  The c contraction reduces to a negative sum of squares of real correlations.
  Proves conjugate symmetrization and hence
    Re(orderedPolynomial rawCoefficient physicalT_coordinates) <= 0.

MonomialIndex.lean, MonomialRegroup.lean, BlockRegroup.lean:
  Check the finite index map for unordered pairs and prove its fibers are
  exactly the listed ordered pairs, each occurring once. Regroup the full
  ordered polynomial into all 528 monomials. A proved coordinate bijection
  then partitions the full quadratic form into the 111 character blocks,
  including all 36 zero coordinates and all cross-block zeros. Establish
    Re(orderedPolynomial rawCoefficient t) / 24
      = familyEnergy checkedBlocks (quadraticMonomials t)
  for every complex coefficient vector t.

Complete.lean:
  Combines the preceding identities to prove Encoder.certificate_nonpositive
  without an added hypothesis. Coercivity gives T-coordinate rigidity;
  FinalReduction transports it to A3=0 and the full enumerator line.
  The converse and unconditional exact-distance attainment together prove
    (exists V : Encoder, A(V)=A and not HasDistance V.psi 4)
      iff exists alpha in [0,1], A=enumeratorLine alpha.
  Thus the enumerator image is complete. No claim of an LU classification
  of the projectors is made.

Exposition and verifier findings
--------------------------------
The orbit-2 proof is in orbit2_enumerator_section.tex. supplementary.tex still
says orbit 2 is unresolved (notably sec:four-open-converse-progress); the new
section is not integrated into its status paragraphs. Neither TeX source was
changed in this work.

The original Python verifier checks exact LDL positivity, but it DOES NOT
compute the characteristic polynomials, despite the TeX table caption saying
every polynomial is verified. ../audit_certificate.py fills that executable
check: it recomputes each characteristic polynomial by integer
Faddeev--LeVerrier and checks all seven table formulas for all 111 blocks.
They all agree. It also checks every JSON block and rational pivot against
M regenerated by the original trace-expansion code, and the coordinate
partition into 36 zero and 492 nonzero coordinates. The characteristic table
is not needed for the Lean coercivity proofs.

The background quantum MacWilliams and shadow enumerator theory is documented
in primary literature:
  Eric Rains, Quantum Weight Enumerators, https://arxiv.org/abs/quant-ph/9612015
  Eric Rains, Quantum shadow enumerators, https://arxiv.org/abs/quant-ph/9611001
These support the background tools, not the new orbit-specific rigidity claim.
A limited literature search did not identify this exact orbit-2 theorem;
this is not a claim that no such result exists.

Build and reproduce
-------------------
Lean and Mathlib are pinned to v4.27.0, available in the local installation.
This package builds independently of the dyadic-ladder Lean package.

Portable setup, from this directory:
  lake update
  lake exe cache get
  lake build
The committed generated Lean files suffice; Python is not needed by Lake.

To regenerate the untrusted certificate files (then recheck with Lean):
  python generate_blocks.py
  python generate_coefficients.py
  python generate_fivequbit.py
  python generate_purity_cases.py

To use an already installed compatible Mathlib project read-only:
  python check.py --mathlib-project /path/to/mathlib-4.27-project --jobs 2
For this workspace the successful run used:
  env XDG_CACHE_HOME=/tmp/codex-mamba-cache /home/zhangc/.local/bin/micromamba run -n cuda129 python six-qubit-orbit2/lean/check.py --mathlib-project /home/zhangc/project/dyadic-lifts/six-qubit-sslp
Run that workspace command from the repository root. The wrapper writes all
compiled artifacts beneath this package's ignored .lake/build directory.

Independent exact Python audit, from the repository root:
  env XDG_CACHE_HOME=/tmp/codex-mamba-cache /home/zhangc/.local/bin/micromamba run -n cuda129 python six-qubit-orbit2/audit_certificate.py

The wrapper discovers all local imports and rebuilds every module in dependency
order; a successful full check therefore includes the new physical, coefficient,
and attainment modules, not only the original LDL package.

verification_log.txt records the successful 357-module dependency check
(663.1 seconds) and the final theorem axiom audits. This run used
--incremental, reusing previously checked unchanged dependencies while
rebuilding the coefficient/reconstruction graph and all completion modules.
The log is supporting evidence, not a proof dependency. Existing packaged data, TeX,
SHA256SUMS and orbit1 work were not modified.

verification_base_log.txt preserves the fresh 258-module build before the
new purification/flatness modules. The current log also covers their full
dependency graph. --incremental may reuse oleans newer than their source
and every local dependency; omit it for a fresh kernel rebuild.
