# Section II audit verdict (archived)

The adversarial audit that drove the Section II and III hardening.  Kept per
this repository's convention of retaining review records: they say which
relations are *not* available and which branches are vacuous, and that is
expensive to rediscover.

Disposition of its seven MISSING items, as of the hardening pass:

* eq:Nj-detection as an equivalence -- closed (`MainTheory/NumberOperator.lean`).
* The pivot matrix is binary -- closed (`MainTheory/BinaryPivot.lean`).
* The paper's Lie-theoretic proof of II.4 -- open, and not actionable: Cartan's
  closed-subgroup theorem, the Lie algebra of a group and `PU(K)` are all
  absent from Mathlib.
* m = |G| for a generator -- closed (`GroupOrder.rank_two_sslp_generator`).
* The sorted canonical form -- closed (`SortedForm.exists_sortedNormalForm`).
* Logical-state interchange -- closed (`MainTheory/InterchangeTransport.lean`);
  it had been treated as absorbed into an existential, which is true but is not
  a statement.
* A single named theorem for thm:rank-two-sslp -- closed
  (`RankTwoSSLP.rank_two_sslp`), and the same defect was then found and closed
  for thm:qualitative-finite-lift and thm:finite-projective-group.

Of its twenty PARTIAL items the substantive ones are likewise closed; the
sharpest, that `exists_pivot_card_eq_rank_le` was "the weaker of the two dressed
as the stronger", is fixed by `PivotSize.exists_pivot_rank_le`.

Two remain open by judgement rather than by work: `eq:spectral-decomp` is a
proof step in the paper, not a numbered conclusion, and the conclusions it
supports are proved; and `BetaExists.exists_betaBound` is content-free by
construction, the content coming from the certified beta_6.

--- original report follows ---

============================================================
lem:phase-sectors (Lemma II.2) — conclusions (i)–(iii) formalized at general (n, K, d), sorry-free; residual gaps are the hypothesis strength (d≥2 instead of Z_j-only) and the unstated identification of t and k_α with the eigen-data
  [PARTIAL] Hypotheses of the lemma: PZ_jP = λ_jP for every j, and D(θ) preserves the code.
     -> The assembled general theorem `SectionTwoGeneral.phaseSectors` does not take the Z_j hypothesis; it takes `C : CodeSpec.ExactCode n K d` together with `hd : 2 ≤ d`, i.e. `SS.HasDistance C.frame.vec d` = detection of ALL weight-1 Paulis (X_j and Y_j as well as Z_j). That is strictly stronger than the lemma's hypothesis. The paper itself justifies th
  [PARTIAL] k_α := rank R_α, and t is the number of DISTINCT eigenvalues of D(θ)|_Q — i.e. the T_α exhaust the spectrum.
     -> `SectionTwoGeneral.phaseSectors` is stated about `resolutionOf C theta hpres := Classical.choice (spectralExtractionPrinciple …)`, an arbitrary inhabitant of `LogicalSectorResolution`, not about the canonical `logicalSectorResolution`. No lemma states, for such a resolution, that `sectorCount` equals the number of distinct eigenvalues of D(θ)|_Q or
  [PARTIAL] Proof-internal structure: P = ∑_α R_α and D(θ)R_α = e^{2πiφ_α}R_α  [eq:spectral-decomp].
     -> Neither the projector identity P = ∑ R_α nor D(θ)R_α = e^{2πiφ_α}R_α is stated as an operator/matrix identity; `sectorProjectorKernel` is defined (D:\UTD\...\MainTheory\PhaseSectorFull.lean) but no lemma sums the kernels to `CodeSpec.projectorKernel C.frame`. These are proof steps in the paper, not numbered conclusions, so the omission does not wea
  [MISSING] eq:Nj-detection itself: with N_j := (I − Z_j)/2, detection of Z_j is EQUIVALENT to P N_j P = μ_j P.
     -> Only the diagonal/expectation consequence is proved (`SectorMeanValue.occOn_eq_klScalar`: every sector vector has occupation (1−λ_j)/2 at site j). The off-diagonal half (⟨ψ_u|N_j|ψ_v⟩ = 0 for u ≠ v) is available from `klScalar_spec` plus orthonormality but is never assembled, and neither direction of the stated equivalence is a declaration. This is
============================================================
thm:qualitative-finite-lift — mostly formalized at the sector level for general (n,K,d), but the code-level gate statement and the genuine `m ∣ q` are rank-two only, the pivot→rationalization link is conditional on a never-constructed `SmithWitness`, and the "binary" pivot claim is not formalized
  [PARTIAL] D(a;q) has exact physical order q (primitivity ⇒ exact order).
     -> It is never instantiated at the constructed lift. No declaration in the repository states that the gate produced by the finite-lift theorem has exact physical order `L.order`, even though both hypotheses are available for it (`canonicalRoot_primitive`, `modularAngle_primitive`). A grep for `pow_eq_one_iff` shows only the orbit-21 example instantiat
  [PARTIAL] The primitive representative preserves the code and realizes the SAME projective logical action as D(theta) — i.e. the two gates agree on the code up 
     -> RANK-TWO ONLY at the code level. `finiteGeneratorOfLift` / `finiteGeneratorOfLift_sameProjective` (D3RationalLiftFiniteGenerator.lean:284, 340) are typed at `C : CodeSpec.ExactCode n 2 d`, because `RankTwoGlobal.FiniteGeneratorResolution` hard-codes `eigenFrame : OrthonormalFrame n 2` and `eigenvalue : Fin 2 → ℂ`. At general K there is NO declarati
  [PARTIAL] eq:qualitative-m-divides-q: the projective logical order m is finite and m ∣ q.
     -> Two gaps. (1) RANK-TWO ONLY: `C : CodeSpec.ExactCode n 2 d` throughout; at general K no `m` is even defined as a group order, and no divisibility statement exists — only the eigenvalue-clearing surrogate. (2) Even at K=2 the divisibility is stated for the CONSTRUCTED generator's class `orderOf G.intrinsicClass ∣ q`; identifying that class with the 
  [MISSING] The pivot matrix C is BINARY: C ∈ {0,1}^{s×s}.
     -> Deliberate design choice, acknowledged in the source comment at FiniteLift.lean:114-116 ("this is the normalization-free version of the paper's locally-X-normalized binary row"). The consequence is that the paper's `C ∈ {0,1}^{s×s}` is replaced by a {−1,0,1}-entry matrix, and even that entry bound is nowhere stated. Anything downstream that needs b
  [PARTIAL] "the rationalization may be OBTAINED FROM" the nonsingular pivot: setting nonselected coordinates to zero and solving C u'_sel = h_0 yields a rational
     -> CONDITIONAL ON AN UNPROVED HYPOTHESIS. `SharpClearing.SmithWitness` (SharpClearing.lean:229) is a data structure carrying U, V, their inverses and the Smith reduction; the ONLY inhabitant constructed anywhere in the repository is `diagonalSmithWitness` for already-diagonal matrices (SharpClearing.lean:246). A repo-wide grep for `SmithWitness` retur
  [PARTIAL] Overall generality: the theorem holds for general n and general rank K.
     -> But the general-K conclusion is only the SECTOR-LEVEL package (rational lift, order ≥ 2, gcd-primitivity, sector-level projective agreement, relative phases cleared). Everything that turns that into the paper's sentence at the code level — a `FiniteGeneratorResolution` D(a;q), `SameProjectiveOnCode C.frame`, and `orderOf ... ∣ q` — is available onl
============================================================
PARTIAL — thm:finite-projective-group (II.4): abelianity and the primitive finite lift are formalized at general (n,K); finiteness of the projective group is proved only for rank K=2, distance ≥3 (all n), and by a different route than the paper's — the paper's own compact-Lie/Cartan proof is absent. All checked declarations are kernel-clean ({propext, Classical.choice, Quot.sound}), no sorry, no axiom, no native_decide.
  [PARTIAL] Hypothesis: the theorem assumes only that the rank-K code *detects every Z_j* (P Z_j P = lambda_j P, eq:Nj-detection) — strictly weaker than distance 
     -> Lean's code-level hypothesis is strictly stronger than the paper's. A code detecting every Z_j but not every X_j/Y_j (d = 1 in the KL sense) satisfies the paper's hypothesis and is outside the scope of every code-level Lean theorem here. Closing this needs a `ZDetects`-only `ExactCodeSectorLink.zDetects` variant; the current one (FiniteLift.lean:74
  [PARTIAL] Conclusion 1a: the projective diagonal logical group of a rank-K code is FINITE.
     -> RANK-TWO ONLY, and DISTANCE-THREE ONLY. The paper claims finiteness for rank K; Lean proves it only for K = 2. The rank-two restriction is load-bearing, not cosmetic: the entire bounded-lift machinery (`RankTwoGlobal.FiniteGeneratorResolution` with `eigenFrame : OrthonormalFrame n 2`, `TwoFiberCertificate`, `D3AutomaticBoundedGenerator`, `BoundedRe
  [PARTIAL] Conclusion 3: for a nontrivial element, its projective logical order m is finite.
     -> RANK-TWO ONLY as a statement about the group-theoretic order `orderOf g`. At general K the root-of-unity surrogate does imply finiteness of each element's projective order in principle, but no Lean declaration states `orderOf g` is finite, or even names m, for K > 2.
  [PARTIAL] Conclusion 4 (the m | q clause): if m is the projective logical order of a nontrivial element and q is the order of ANY finite physical lift, then m |
     -> RANK-TWO ONLY. There is no general-K m | q. The abstract fact that would give it, `ProjectiveGroupFinite.logicalOrder_dvd_physicalOrder` (line 75, `orderOf (restriction x) | orderOf x` via `orderOf_map_dvd`), is never instantiated at the quotient map `diagonalSymmetryGroup P ->* IntrinsicProjectiveDiagonalLogicalGroup P` — grep shows `orderOf_map_d
  [MISSING] The paper's PROOF of II.4: T_P is a closed subgroup of the compact torus T^n hence a compact abelian Lie group; rho : T_P -> PU(K) has compact (hence 
     -> The paper's route is what makes the theorem work at general K without any denominator bound; the Lean route trades that generality away. This is the structural reason claim 3 (finiteness) is stuck at K = 2 — closing K > 2 by the Lean route needs the whole bounded-lift stack re-derived at higher rank, not just a retyping.
  [UNCLEAR] Repository self-description of this theorem's status.
     -> README understates what exists at K = 2 and does not flag that the K = 2 result rests on a different proof strategy with a stronger (d >= 3) hypothesis. Worth reconciling so a reader does not conclude either 'nothing is proved' or 'II.4 is done'.
============================================================
thm:rank-two-sslp (Thm II.5, "Finite two-fiber SSLP normal form"), main.tex:706 — audited against MainTheory/ (build clean, all headline decls in {propext, Classical.choice, Quot.sound}, no sorry/native_decide; see .tfull.log)
  [PARTIAL] The projective diagonal logical group is FINITE (imported from thm:finite-projective-group; needed before 'cyclic, say C_m' can be stated).
     -> Distance is hard-wired at `ExactCode n 2 3`, so only codes of distance >= 3 are covered; the paper asserts the theorem for d >= 2 and its proof of finiteness uses only Z_j detection. The d = 2 case is not proved. The restriction is forced by the route: `GeneralFiniteness.hasBoundedRepresentation` goes through `D3NormalizedFreshPhase.canonicalTwoFib
  [PARTIAL] That group is CYCLIC, say C_m (via the phase-ratio embedding into U(1) and 'every finite subgroup of U(1) is cyclic').
     -> Unconditional only for distance >= 3 (`ExactCode n 2 3`), because its finiteness input is; the paper claims it for d >= 2. At d = 2 the statement in the repository is `isCyclic_of_diagonalizer`/`isCyclic_of_nontrivial` with `hfin : Finite (IntrinsicGroup C)` unproved.
  [MISSING] The m of eq:K2-bound is the order of the whole cyclic group C_m (i.e. the chosen element is a generator, so m = |G_diag(P)|).
     -> No declaration states 'for a generator g of IntrinsicGroup C, Nat.card (IntrinsicGroup C) = orderOf g and that number divides the physical order of its primitive lift'. What is proved is m | q for each individual element's own projective order. Grep for `Nat.card (IntrinsicGroup` returns only the three six-qubit uses.
  [MISSING] Permutation of the physical qubits produces the sorted canonical form 0 <= a_1 <= … <= a_n < q (first half of eq:a-canonical).
     -> No theorem states the normal form with a sorted angle vector. `TwoFiberCertificate` has no monotonicity field, and `permFiniteGeneratorResolution` has zero call sites anywhere in the repository (grep confirms), so the permutation transport is never composed with a sort. `permExactCode`/`permFiniteGeneratorResolution` are also pinned to `ExactCode n
  [MISSING] Logical-state interchange is among the harmless normalizations.
     -> Arguably unneeded in the Lean route (which never needs to swap), but the paper lists it as one of the quotienting operations and no Lean statement licenses it. Not claimed by the repository either — the RankTwo docstring lists 'the quotient by … logical interchange' as not done.
  [PARTIAL] CONVERSE: any orthonormal pair supported in S_0(a;q) and S_{q/m}(a;q) that satisfies the full desired Knill–Laflamme equations spans a code on which D
     -> `order_of_two_fiber` takes neither orthonormality nor the KL equations as hypotheses and produces no `ExactCode`; its own docstring (RankTwo.lean:130-138) admits the first two conclusions are vacuous when the states vanish, and that 'the paper's converse assumes an orthonormal pair satisfying the full Knill–Laflamme system; orthonormality is not im
  [MISSING] A single named Lean theorem stating thm:rank-two-sslp as a whole (code + nontrivial group ⟹ cyclic C_m + primitive lift + m|q + the canonical two-fibe
     -> The forward direction lives as a chain of separately-stated theorems plus a 30-field `TwoFiberCertificate` record, not as one statement matching the paper's. Anyone reading only a top-level name will not find the theorem; the audit had to reassemble it. (Also: README.md:584 is stale — it still reports 2.5 'Blocked' and 2.6 as lacking the coprime-po
============================================================
vacuity-review
  [PARTIAL] GeneralFiniteness.isCyclic (MainTheory/GeneralFiniteness.lean:125) is strictly weaker than what the repository already proves: its two hypotheses (u0,
     -> As recorded, cyclicity at arbitrary n reads as conditional on a projectively nontrivial diagonal symmetry — data the repository never constructs for any code — when in fact it holds for every exact rank-two distance-three code unconditionally. Restate `isCyclic` without u0/h0 (keep the conditional version as a private lemma if desired).
  [PARTIAL] GeneralFiniteness.finite_and_abelian (MainTheory/GeneralFiniteness.lean:134) presents 'finite abelian' as one result, but only the finiteness conjunct
     -> The headline 'the projective diagonal logical group is finite abelian, at arbitrary n' is carried entirely by the finiteness half; abelianness is a pointwise-commutativity fact about `LocalPhase n` and would be true of a projector unrelated to any code. Not wrong, but the conjunction makes the new content look twice as large as it is.
  [PARTIAL] GeneralFiniteness.hasBoundedRepresentation (MainTheory/GeneralFiniteness.lean:41) states its conclusion about an internally produced object and carrie
     -> Read alone, this theorem certifies that SOME class derived from theta is bounded, not that the class of theta's symmetry is; and `hd3` is decoration inherited from the d-general `rationalLift`/`finiteGenerator` signatures even though the theorem is pinned at d = 3. Both are cured downstream, so the defect is presentational, not a soundness hole.
  [UNCLEAR] Non-vacuity of the four GeneralFiniteness theorems is not established anywhere in the repository: no term of type `CodeSpec.ExactCode n 2 3` is ever b
     -> Mathematically ((5,2,3)) codes exist, so these ∀-statements are not vacuous in truth — but nothing in this development can conclude anything non-vacuous from them without an external code. For `isCyclic` the gap doubles: it also demands a projectively nontrivial `u0`, which is likewise never constructed.
  [PARTIAL] BetaExists.exists_betaBound (MainTheory/BetaExists.lean:70) is true but content-free, and its witness cannot be evaluated.
     -> There is no lemma anywhere relating `betaOf 6` to the certified `BetaBound 6 9` (grep: `betaOf` occurs only in BetaExists.lean and GeneralFiniteness.lean). So the arbitrary-n finiteness result does not subsume, and cannot recover, the sharp six-qubit statement q ≤ 9; the generalized theorems give a finite group with no numeric bound of any kind. Ge
  [PARTIAL] PivotSize.exists_pivot_card_eq_rank_le (MainTheory/PivotSize.lean:183) is advertised as 'eq:qualitative-pivot-size with no hypothesis left', but two o
     -> The 's = rank R' half is definitionally forced by choosing `Fin rank` as the index type rather than proved of an independently given pivot. The strong form is `card_eq_rank` (line 95), which does take an arbitrary Fintype s — the packaged theorem is the weaker of the two dressed as the stronger.

TALLY: {'FORMALIZED': 42, 'PARTIAL': 20, 'MISSING': 7, 'UNCLEAR': 2}
