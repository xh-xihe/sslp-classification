import MainTheory.WImageSettled62
import MainTheory.ParityFourConnectivity
import MainTheory.ParityFourPolytope
import MainTheory.CodeOrbitStatus
import MainTheory.IntrinsicOrderAudit
import SixQubit.Orbit8RaisingGram
import SixQubit.Orbit8OperatorQP
import SixQubit.Orbit7Marginal
import SixQubit.Orbit9MagnitudeCounts
import SixQubit.Orbit36
import SixQubit.Orbit8UniversalLadderClose
import SixQubit.Orbit8UniversalVacuum
import SixQubit.Orbit9Flip
import SixQubit.Block26
import SixQubit.Orbit31MomentPolytope
import SixQubit.Orbit7BoundaryIsolated
import SixQubit.Orbit7PairSum
import SixQubit.Orbit7UniversalScalar
import SixQubit.Orbit9SupportCard
import SixQubit.Orbit9NoTwo
import SixQubit.Orbit9ComponentPhase

/-!
# `supplementary.tex`: the weight-enumerator images and the parity-four geometry, by label

The companion of `PaperSupplementaryNoGo`.  That file names the manuscript's
no-go results; this one names the positive half -- the exact weight-enumerator
images -- together with the intermediate order-range corollaries and the
parity-four lemmas that the order-two section runs on.

As there, nothing new is proved.  Every theorem below is an existing result
restated under the manuscript's label, so that a reader checking
`supplementary.tex` against the package can find the result and not only its
parts.

Two things are worth saying about faithfulness.

* The families are the manuscript's, not lookalikes: `WImages.FI a` unfolds to
  `(1, a, 1-a, 0, 11+4a, 16-a, 3-3a)`, which is `eq:o7weightimage` on the nose,
  and `WImages.FII t` unfolds to `(1, 0, t, 1-t, 12-t, 15+t, 3)`, which is
  `eq:o45-A-image`.  The interval endpoints are the manuscript's as well.
* The three range corollaries `cor:q7range`, `cor:q8range` and `cor:q9range`
  are *staged* claims in the manuscript -- each records the bound available at
  that point in the argument.  The package proves the final bound
  `orderOf g <= 5` outright, so the staging is not reproduced; each corollary's
  actual assertion is recorded, and its proof here goes through the stronger
  final result rather than through the argument the manuscript gives at that
  point.  That is a difference in provenance, not in content, and it is stated
  rather than hidden.
-/

namespace MainTheory.PaperSupplementaryImages

open MainTheory

/-! ## The exact weight-enumerator images -/

/-- **`thm:o7weightimage`, `eq:o7weightimage`.**

`W_7 = { (1, a, 1-a, 0, 11+4a, 16-a, 3-3a) : 0 <= a <= 1 }`. -/
theorem o7_weight_image :
    Levels.WImage SixQubit.Orbit7Real.av 0 1 = WImages.FI '' Set.Icc 0 1 :=
  WImages.WImage_orbit7

/-- **`thm:o8weightimage`, `eq:o8weightimage`.**

The same family on the half-interval `1/2 <= a <= 1`. -/
theorem o8_weight_image :
    Levels.WImage SixQubit.Orbit8Real.av 0 1 = WImages.FI '' Set.Icc (1 / 2) 1 :=
  WImages.WImage_orbit8

/-- **`thm:o9weightimage`, `eq:o9weightimage`.**

`W_9 = { (1, 0, 1, 0, 11, 16, 3) }`, a single point. -/
theorem o9_weight_image :
    Levels.WImage SixQubit.Orbit9Real.av 0 1 = {Levels.E2A} :=
  WImages.WImage_orbit9

/-- **`thm:o21-enumerator`.**  `W_21 = { E_2^A }`. -/
theorem o21_enumerator :
    Levels.WImage SixQubit.Orbit21Cert.av 0 2 = {Levels.E2A} :=
  Levels.WImage_orbit21

/-- **`thm:o45-weightimage`, `eq:o45-A-image`.**

`W_45 = { (1, 0, t, 1-t, 12-t, 15+t, 3) : 2/3 <= t <= 1 }`. -/
theorem o45_weight_image :
    Levels.WImage SixQubit.Orbit45Support.av 0 3 = WImages.FII '' Set.Icc (2 / 3) 1 :=
  WImages.WImage_orbit45

/-- **`thm:m2-five-stabilizer-orbits`, `eq:m2-E2-orbits` and `eq:m2-E1-orbits`.**

`W_10 = W_16 = W_22 = { E_2^A }` and `W_11 = W_23 = { E_1^A }`. -/
theorem m2_five_stabilizer_orbits :
    Levels.WImage SixQubit.Orbit10Real.av 0 2 = {Levels.E2A} ∧
    Levels.WImage SixQubit.Orbit16Real.av 0 2 = {Levels.E2A} ∧
    Levels.WImage SixQubit.Orbit22Real.av 0 2 = {Levels.E2A} ∧
    Levels.WImage SixQubit.Orbit11Real.av 0 2 = {WImages.E1A} ∧
    Levels.WImage SixQubit.Orbit23Real.av 0 2 = {WImages.E1A} :=
  ⟨WImages.WImage_orbit10, WImages.WImage_orbit16, WImages.WImage_orbit22,
    WImages.WImage_orbit11, WImages.WImage_orbit23⟩

/-! ## The staged order-range corollaries -/

/-- **`cor:q9range`.**  Every projective diagonal logical element has order at
most `8`.  See the header on provenance: the package proves `<= 5`. -/
theorem q9_range (C : CodeSpec.ExactCode 6 2 3)
    (g : GlobalClassificationBridge.IntrinsicGroup C) : orderOf g ≤ 8 := by
  rcases MainTheory.IntrinsicOrderAudit.orderOf_mem C g with h | h | h | h <;> omega

/-- **`cor:q8range`, `eq:M36range`.**  Order at most `7`. -/
theorem q8_range (C : CodeSpec.ExactCode 6 2 3)
    (g : GlobalClassificationBridge.IntrinsicGroup C) : orderOf g ≤ 7 := by
  rcases MainTheory.IntrinsicOrderAudit.orderOf_mem C g with h | h | h | h <;> omega

/-- **`cor:q7range`, `eq:M36rangeAfter7`.**  Order at most `6`. -/
theorem q7_range (C : CodeSpec.ExactCode 6 2 3)
    (g : GlobalClassificationBridge.IntrinsicGroup C) : orderOf g ≤ 6 := by
  rcases MainTheory.IntrinsicOrderAudit.orderOf_mem C g with h | h | h | h <;> omega

/-! ## The order-five sector -/

/-- **`cor:m5-unique-unconditional`.**

Orbit 36 is the only rank-compatible moment orbit admitting a six-qubit
`((6,2,3))` code of projective diagonal logical order five. -/
theorem m5_unique_unconditional (C : CodeSpec.ExactCode 6 2 3)
    (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ (S : SortedForm.SortedNormalForm C) (k : Fin 66),
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = S.m ∧
      (S.m = 5 →
        MainTheory.Generated.FiniteOrbitBase.paperOrbitId k = 36) :=
  MainTheory.CodeOrbitStatus.code_orderFive_is_orbit36 C theta hpres hnt

/-! ## The parity-four geometry -/

/-- **`lem:parity4-moment`, `eq:parity4-momentequalities`.**

A nonnegative point lies in the parity-four moment polytope exactly when it is
nonnegative and satisfies the moment equalities for every `|S| <= 2`, and the
polytope's affine hull is four-dimensional -- the cross-polytope of the
manuscript, not a free-parameter count. -/
theorem parity4_moment (p : ParityFour.Cube → ℝ) :
    ((fun k => p (ParityFour.point k)) ∈ ParityFour.momentPolytope ↔
      (∀ x, 0 ≤ p x) ∧ ParityFour.MomentEquations p) ∧
    Module.finrank ℝ (affineSpan ℝ ParityFour.momentPolytope).direction = 4 :=
  ⟨ParityFour.momentPolytope_iff p, ParityFour.momentPolytope_affine_dimension⟩

/-- **`lem:parity4-connectivity`.**

The positive-support graph is connected, and after fixing any one coordinate
the remaining positive-support graph is empty or connected. -/
theorem parity4_connectivity (a : Fin 4 → ℝ) :
    (ParityFour.positiveGraph a).Connected ∧
    ∀ (i : Fin 4) (b : Bool),
      IsEmpty {x : ParityFour.Cube //
        BooleanCube.slice {i} (fun _ => b) x ∧ 0 < ParityFour.probability a x} ∨
        (ParityFour.positiveSliceGraph a i b).Connected :=
  ⟨ParityFour.positiveGraph_connected a,
    fun i b => ParityFour.positiveSliceGraph_empty_or_connected a i b⟩

/-! ## Orbit-specific structure lemmas -/

/-- **`cor:o8raisinggram`, `eq:o8Gramspectrum`.**

For the raising Gram matrix `(G_+)_{ij} = <0_L| sigma_i^- sigma_j^+ |0_L>` of
any exact orbit-8 solution, `G_+^2 = G_+/2` and the characteristic polynomial
is `X (X - 1/2)^5`, so the spectrum is `{0, 1/2, 1/2, 1/2, 1/2, 1/2}`.

The manuscript states the spectrum as a multiset; the characteristic
polynomial is that statement with the multiplicities, which is strictly more
than listing the eigenvalues. -/
theorem o8_raising_gram (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit8Universal.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit8Universal.av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c, d] 3) :
    SixQubit.Orbit8RaisingGram.raisingGram c
        * SixQubit.Orbit8RaisingGram.raisingGram c
        = (1 / 2 : ℂ) • SixQubit.Orbit8RaisingGram.raisingGram c ∧
      (SixQubit.Orbit8RaisingGram.raisingGram c).charpoly
        = Polynomial.X * (Polynomial.X - Polynomial.C (1 / 2 : ℂ)) ^ 5 :=
  SixQubit.Orbit8RaisingGram.fully_certified c d hc hd hnc hnd hcode

/-- **`cor:o9magnitudes`, `eq:o9activemagnitudes` and `eq:o9inactivemagnitude`.**

In the uniform gauge every exact orbit-9 solution has the displayed magnitude
pattern for some inactive pair `a, b`, and the ten-plus-one coefficient count
`1/12` ten times and `1/6` once on each logical word. -/
theorem o9_magnitudes (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    (∃ a b : Fin 6, SixQubit.Orbit9Universal.MagnitudePattern
        (SixQubit.Orbit9Universal.toUniform c)
        (SixQubit.Orbit9Universal.toUniform d) a b) ∧
      SixQubit.Orbit9Universal.ElevenCoefficientPattern c d :=
  SixQubit.Orbit9Universal.magnitudes_fully_certified c d hc hd hnc hnd hdist

/-- **`lem:o36allractive`.**

Every exact orbit-36 solution has `r_1 r_2 r_3 r_4 != 0`.  The hypotheses are
the orbit-36 moment equations themselves, which is what "exact orbit-36
solution" abbreviates in the manuscript. -/
theorem o36_all_r_active {r1 r2 r3 r4 c12 c13 c14 c23 c24 c34 : ℂ}
    (e1 : c12 * r2 + c13 * r3 + c14 * r4 = 0)
    (e2 : c12 * r1 + c23 * r3 + c24 * r4 = 0)
    (e3 : c13 * r1 + c23 * r2 + c34 * r4 = 0)
    (e4 : c14 * r1 + c24 * r2 + c34 * r3 = 0)
    (hP : Complex.normSq r1 + Complex.normSq r2 + Complex.normSq r3
            + Complex.normSq r4 = 2 / 5)
    (hD1 : Complex.normSq c12 + Complex.normSq c13 + Complex.normSq c14
            = Complex.normSq r1 + 1 / 10)
    (hD2 : Complex.normSq c12 + Complex.normSq c23 + Complex.normSq c24
            = Complex.normSq r2 + 1 / 10)
    (hD3 : Complex.normSq c13 + Complex.normSq c23 + Complex.normSq c34
            = Complex.normSq r3 + 1 / 10)
    (hD4 : Complex.normSq c14 + Complex.normSq c24 + Complex.normSq c34
            = Complex.normSq r4 + 1 / 10) :
    r1 * r2 * r3 * r4 ≠ 0 := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    SixQubit.Orbit36.vertices_active e1 e2 e3 e4 hP hD1 hD2 hD3 hD4
  simp [h1, h2, h3, h4]

/-! ## Internal steps of the orbit 8 and 9 arguments

These are proof-internal lemmas rather than headline results, so they are
recorded as aliases: an alias carries exactly the referenced theorem's
statement, which is what makes the label citation checkable rather than a
comment.  Each hypothesis set is the referenced theorem's own -- complete-fibre
support, the two normalizations and genuine distance three -- with no
Knill-Laflamme row assumed. -/

/-- **`lem:o8shells`, `eq:o8shellmasses`.**

Vacuum elimination and all five rigid shell masses:
`(mu_0, mu_3, mu_6) = (0, 5/6, 1/6)` and `(nu_1, nu_4) = (1/6, 5/6)`. -/
alias o8_shells := SixQubit.Orbit8Universal.rigid_shells

/-- **`lem:o8supporttwo`, `eq:o8supporttwo`.**  `|supp u| <= 2`. -/
alias o8_support_two := SixQubit.Orbit8Universal.singleton_support_le_two

/-- **`lem:o8ladder`, `eq:o8ladder01`.**  `R J |0_L> = -b |1_L>`. -/
alias o8_ladder01 := SixQubit.Orbit8Universal.ladder01

/-- **`lem:o8ladder`, `eq:o8ladder10`.**  `R J |1_L> = b |0_L>`. -/
alias o8_ladder10 := SixQubit.Orbit8Universal.ladder10

/-- **`lem:o8ladder`, `eq:o8QP`.**  `Q P = r P`, with `r = 1/6`.

`SixQubit.Orbit8Universal.Q_eigen` is the manuscript's derivation, which
produces the two eigenvalue equations; `QP_eq` is the operator identity the
manuscript states, obtained from them by linearity of `Q` and of the
projector. -/
alias o8_QP := SixQubit.Orbit8Universal.QP_eq

/-- **`lem:o9pqequal`, first clause of `eq:o9pqdegree`.**  `p_i = q_i`. -/
alias o9_pq_equal := SixQubit.Orbit9Universal.pq_equal

/-! ## Internal steps of the order-four arguments

Only the steps the package actually takes are recorded.  The orbit-26 argument
in `SixQubit.Block26` is a *repaired* one -- it closes a mixed-axis branch the
manuscript's route passes over -- and the orbit-30 argument likewise departs
from the manuscript's, so the headline no-gos `thm:q4o26nogo` and
`thm:q4o30nogo` are proved by a different route than the manuscript's.

The manuscript's own intermediate steps are nonetheless carried:
`lem:q4o26anchorsingular` is `MainTheory.Orbit26.anchor_singular`,
proved from the manuscript's displayed equations, and `lem:q4o30exceptional`
is `MainTheory.Orbit30.Data.q4o30_exceptional`. -/

/-- **`lem:q4o26Jorth`, `eq:q4o26Jorth`.**

Three pairwise `J`-orthogonal nonzero rows of `C^2` lie on one common
coordinate axis.  Self-isotropy is a consequence rather than a hypothesis: the
three relations involve only distinct pairs. -/
alias q4o26_Jorth := SixQubit.Block26.axis_lemma

/-- **`prop:q4o31momentnormal`.**

The two normalization equations and the twenty-one diagonal moment equations
have rank twenty-three, and a point satisfies them exactly when it has the
displayed normal form: `eq:q4o31equalprob` is the complement relation,
`eq:q4o31rowsums` the three row sums `1/4`, and `eq:q4o31alphabeta` the four
column relations `alpha_e = sum_i beta_{i,e} - 1/8`. -/
theorem q4o31_moment_normal (x : Fin 32 → ℝ) :
    (x ∈ SixQubit.Orbit31.momentPolytope ↔
      SixQubit.Orbit31.MomentNormalForm (fun i => x (Fin.castAdd 16 i))
        (fun i => x (Fin.natAdd 16 i))) ∧
    SixQubit.Orbit31.momentMatrix.rank = 23 :=
  ⟨SixQubit.Orbit31.momentPolytope_iff_normalForm x,
    SixQubit.Orbit31.momentMatrix_rank⟩

/-- **`lem:q4o31permanenttriangle`, `eq:q4o31oddpermanent`.**

Three pairs `(r_i, s_i)` with both entries nonzero cannot satisfy
`r_i s_j + s_i r_j = 0` for all `i < j`.

This is the orbit-26 axis lemma read contrapositively: those three equations
are exactly pairwise `J`-orthogonality for the rows `(r_i, s_i)`, so the axis
lemma forces every `s_i` to vanish or every `r_i` to, and both are excluded by
the nonvanishing hypothesis.

The manuscript's hypothesis is that all six entries are nonzero.  Only four of
them are used -- the three `r_i` and one `s_i` -- so the two marked `_` are
kept because the manuscript states them, not because the proof needs them. -/
theorem q4o31_permanent_triangle (r1 s1 r2 s2 r3 s3 : ℂ)
    (hr1 : r1 ≠ 0) (hs1 : s1 ≠ 0) (hr2 : r2 ≠ 0) (_hs2 : s2 ≠ 0)
    (hr3 : r3 ≠ 0) (_hs3 : s3 ≠ 0)
    (e12 : r1 * s2 + s1 * r2 = 0)
    (e13 : r1 * s3 + s1 * r3 = 0)
    (e23 : r2 * s3 + s2 * r3 = 0) : False := by
  rcases SixQubit.Block26.axis_lemma r1 s1 r2 s2 r3 s3
      (fun h => hr1 h.1) (fun h => hr2 h.1) (fun h => hr3 h.1)
      e12 e13 e23 with ⟨h1, _, _⟩ | ⟨h1, _, _⟩
  · exact hs1 h1
  · exact hr1 h1

/-! ## Internal steps of the orbit 7 and orbit 9 enumerator arguments

Located and then adversarially re-checked against the manuscript one by one.
Two of the manuscript's lemmas turned out not to be provable by any single
existing declaration, and were completed rather than approximated:

* `lem:o7scalarmoments` has four clauses.  Its three displayed equations are
  `scalar_normal_form` below.  Its closing sentence -- that every active qubit
  has maximally mixed one-qubit marginal -- had no proof in this repository;
  `SixQubit.Orbit7Marginal` supplies it, following the manuscript: the `Z_i`
  scalar vanishes because `eq:o7fractionalmatching` makes both occupations
  `1/2`, and the `X_i` and `Y_i` scalars vanish because the two words sit in
  different `ZMod 3` residue shells, so a one-coordinate flip leaves the
  shell.  The certified route does not need the clause -- it reaches `A_1`
  through the shadow/MacWilliams squeeze in `Orbit7UniversalEnum` -- so this
  completes the manuscript's lemma without entering the verified chain.
* `lem:o9supportfour` had no top-level statement at all.  Its two clauses
  existed only as a three-theorem chain assembled inside other proof bodies,
  each step carrying the previous step's conclusion as a hypothesis.
  `o9_support_four` below is that chain closed into one unconditional
  statement, which is new. -/

/-- **`lem:o7scalarmoments`, closing clause.**  Every active qubit has
maximally mixed one-qubit marginal, in both logical words. -/
alias o7_active_marginal := SixQubit.Orbit7Universal.active_marginal_maximally_mixed

/-- **`lem:o7scalarmoments`, `eq:o7extremenorms`, `eq:o7edgenorms` and
`eq:o7fractionalmatching`.**

The three displayed equations: the two extreme masses are `1/6`, the two edge
masses agree on every edge, and the resulting edge weights form a fractional
perfect matching of `K_5` with vertex degree `1/3` and total `5/6`.

The Lean hypotheses are the manuscript's own two fibres, the two
normalizations and honest distance three; no gauge is fixed and no
Knill--Laflamme row is assumed beyond what distance three supplies.  The
lemma's fourth clause is discussed in the section header. -/
alias o7_scalar_moments := SixQubit.Orbit7Universal.scalar_normal_form

/-- **`lem:o7boundaryreduction`, `eq:o7fullxsupport`.**

Either the target-star configuration already holds at some vertex, or every
one of the ten edge coordinates is nonzero.

The manuscript states this after fixing the gauge `u = (1,0)/sqrt 6`; the Lean
statement fixes no gauge, so its hypotheses are strictly weaker than the
manuscript's. -/
alias o7_boundary_reduction := SixQubit.Orbit7Universal.boundary_reduction

/-- **`lem:o7pairsum`, `eq:o7pairsumdet`.**

Five vectors of `C^2` with `det(w_i + w_j, w_k + w_l) = 0` for all four
distinct indices are collinear -- stated as the vanishing of all ten minors
`det(w_i, w_j)`, which in `C^2` is collinearity including the degenerate
all-zero case the manuscript's proof explicitly allows.  No nondegeneracy
side condition is added. -/
alias o7_pair_sum := SixQubit.Orbit7Universal.pairSum_collinear

/-- **`lem:o9momentnormalform`, `eq:o9shellmasses` and `eq:o9degreeformulas`.**

The lemma is a conjunction of two displays and no single declaration proves
both, so both are stated here: the four shell masses, and the degree
formulas for every index. -/
theorem o9_moment_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit9Universal.S0 → c x = 0)
    (hd : ∀ x, x ∉ SixQubit.Orbit9Universal.S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    (SixQubit.Orbit9Universal.Pmass c = 1 / 3 ∧
      SixQubit.Orbit9Universal.Rmass c = 2 / 3 ∧
      SixQubit.Orbit9Universal.Smass d = 2 / 3 ∧
      SixQubit.Orbit9Universal.Qmass d = 1 / 3) ∧
    ∀ i : Fin 6,
      SixQubit.Orbit9Universal.Rdeg c i
          = (1 / 3 - SixQubit.Orbit9Universal.p c i
              + 3 * SixQubit.Orbit9Universal.q d i) / 2 ∧
      SixQubit.Orbit9Universal.Sdeg d i
          = (1 / 3 - SixQubit.Orbit9Universal.q d i
              + 3 * SixQubit.Orbit9Universal.p c i) / 2 :=
  ⟨SixQubit.Orbit9Universal.global_masses c d hc hd hnc hnd hdist,
    fun i => SixQubit.Orbit9Universal.degree_normal_form c d hc hd hnc hnd hdist i⟩

/-- **`lem:o9components`.**

Every nonzero edge between two active vertices lies in a four-vertex clique
that is isolated from every other active vertex -- the manuscript's
active-component lemma, indexed by edge rather than by component, which is
equivalent since a nontrivial component is one containing an edge. -/
alias o9_components := SixQubit.Orbit9Universal.active_edge_has_actual_k4

/-- **`lem:o9supportfour`.**

The active support has exactly four elements and its graph is the complete
graph on them.

This statement is new.  The repository proved the two clauses only as a chain
-- `active_card_ne_two`, then `active_card_eq_four_of_ne_two` under the
hypothesis `card != 2`, then `active_k4_exact_of_card_four` under `card = 4`
-- and assembled it inside other proof bodies, so the lemma itself was never
stated.  Closing the chain here removes the hypotheses and makes it one
unconditional theorem. -/
theorem o9_support_four (c d : SS.State 6 ℂ)
    (H : SixQubit.Orbit9Universal.FullKL c d) :
    (SixQubit.Orbit9Universal.ActiveSet c).card = 4 ∧
      ∃ i j k l, SixQubit.Orbit9Universal.ActiveK4 c d i j k l ∧
        ∀ t, SixQubit.Orbit9Universal.Active c t
          ↔ t = i ∨ t = j ∨ t = k ∨ t = l := by
  have hfour := SixQubit.Orbit9Universal.active_card_eq_four_of_ne_two c d H
    (SixQubit.Orbit9Universal.active_card_ne_two c d H)
  exact ⟨hfour,
    SixQubit.Orbit9Universal.active_k4_exact_of_card_four c d H hfour⟩

/-! ## The order-two status column -/

set_option maxRecDepth 200000 in
/-- **`cor:m2-current-status`, clauses (i) and (iii).**

The projective-order-two sector is exactly the twenty-five manuscript orbits
listed, and within it a key admits an exact completion exactly when its
manuscript number is one of the eleven `1, 2, 3, 4, 10, 11, 16, 21, 22, 23,
45`.  So fourteen of the twenty-five have empty exact image, and only
`1, 2, 3, 4` are unresolved once the seven determined images of clause (ii)
are taken from `m2_five_stabilizer_orbits`, `o21_enumerator` and
`o45_weight_image`.

The sector had to be cut by the key's own `m`, not by the angle modulus `q`
that the existing no-go aggregates group on; those two groupings are
different and only the first is the manuscript's. -/
theorem m2_current_status :
    (Finset.univ.filter fun k : Fin 66 =>
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 2).image
          MainTheory.Generated.FiniteOrbitBase.paperOrbitId
      = ({1, 2, 3, 4, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
          24, 41, 42, 43, 44, 45, 46} : Finset ℕ) ∧
    ∀ k : Fin 66, (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 2 →
      (MainTheory.CubeCompletionTransport.HasCompletion
          (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ↔
        MainTheory.Generated.FiniteOrbitBase.paperOrbitId k ∈
          ([1, 2, 3, 4, 10, 11, 16, 21, 22, 23, 45] : List ℕ)) := by
  refine ⟨by decide, fun k _ => ?_⟩
  rw [MainTheory.RealizationOrbits15.hasCompletion_iff_mem_realizationKeys k]
  revert k
  decide

end MainTheory.PaperSupplementaryImages
