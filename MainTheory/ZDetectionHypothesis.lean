import MainTheory.QuantitativeGroup
import MainTheory.GeneralFinitenessRank
import MainTheory.ProjectiveGroupGeneral

/-!
# The paper's own hypothesis: detecting every `Z_j`

`lem:phase-sectors` opens "Assume that `P Z_j P = lambda_j P` for every `j`",
and `thm:finite-projective-group` and `cor:quantitative-projective-group` both
read "If a rank-`K` code detects every `Z_j`, then ...".  Every Lean statement
of those three results instead carries `hd : 2 <= d` on
`CodeSpec.ExactCode n K d`, and `ExactCode` bundles `SS.HasDistance frame.vec d`,
so `2 <= d` is the full Knill--Laflamme system for *every* weight-one Pauli --
`X_j` and `Y_j` included.  That is strictly stronger than what the paper
assumes, so the Lean theorems were weaker than the paper's.

Nothing in the chain ever used more than the `Z` equations.  Every occurrence
of `hd` in `SectionTwoGeneral` and `QuantitativeGroup` appears only inside
`(resolutionOf C theta hpres).zDetects hd`, and that in turn only feeds
`PhaseSectorFull.zDetects_of_hasDistance_reindex`, whose proof instantiates the
detection hypothesis at the single pure-`Z` Pauli `Z_j`.

This file isolates the hypothesis and restates the three results on it.

* `ZDetectsFrame F` is `P Z_j P = lambda_j P` for every `j`, and nothing else.
* `zDetectsFrame_of_codeSpan_eq` -- it is a property of the code subspace, not
  of the chosen frame, by the same scalar-compression argument that makes
  `HasDistance` frame-independent.
* `quantitative_projective_group_of_zDetects` and
  `finite_intrinsicGroup_of_zDetects` are `cor:quantitative-projective-group`
  and `thm:finite-projective-group` at the paper's hypothesis; the rest of the
  package's `2 <= d` versions follow from these by
  `zDetectsFrame_of_hasDistance`.
-/

namespace MainTheory.ZDetection

open MainTheory
open MainTheory.CodeSpec
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.PhaseSectorFull

variable {n K : ℕ}

/-- The pure-`Z` Pauli on qubit `j`. -/
def pureZ (j : Fin n) : SS.PauliString n := ⟨fun _ => false, SS.stdBasis j⟩

/-- **The paper's hypothesis**: the code detects every `Z_j`, that is
`P Z_j P = lambda_j P` for each `j`.  This is one Knill--Laflamme equation per
qubit, not the whole weight-one system. -/
def ZDetectsFrame (F : OrthonormalFrame n K) : Prop :=
  ∀ j : Fin n, SS.KLCondition F.vec (pureZ j)

/-- Distance at least two supplies it, so every existing `2 <= d` theorem is a
special case of the ones below. -/
theorem zDetectsFrame_of_hasDistance {d : ℕ} (F : OrthonormalFrame n K)
    (hF : SS.HasDistance F.vec d) (hd : 2 ≤ d) : ZDetectsFrame F := by
  intro j
  refine hF (pureZ j) ?_
  have hwt : (pureZ j).wt ≤ 1 := by
    simpa [pureZ] using SixQubit.wt_pureZ_single j
  omega

/-- One Knill--Laflamme equation is a property of the code subspace.  This is
`hasDistance_of_codeSpan_eq` for a single Pauli, which is all its proof ever
used. -/
theorem klCondition_of_codeSpan_eq {L : ℕ} (F : OrthonormalFrame n K)
    (G : OrthonormalFrame n L) (hspan : codeSpan F = codeSpan G)
    (P : SS.PauliString n) (h : SS.KLCondition F.vec P) :
    SS.KLCondition G.vec P := by
  obtain ⟨c, hcompression⟩ := scalarCompression_of_klCondition F P h
  refine ⟨c, ?_⟩
  intro i j
  have hi : G.vec i ∈ codeSpan F := by
    rw [hspan]; exact Submodule.subset_span (Set.mem_range_self i)
  have hj : G.vec j ∈ codeSpan F := by
    rw [hspan]; exact Submodule.subset_span (Set.mem_range_self j)
  rw [hcompression (G.vec i) hi (G.vec j) hj, G.orthonormal]
  by_cases hij : i = j <;> simp [hij]

/-- Hence the hypothesis travels between frames of the same code. -/
theorem zDetectsFrame_of_codeSpan_eq {L : ℕ} (F : OrthonormalFrame n K)
    (G : OrthonormalFrame n L) (hspan : codeSpan F = codeSpan G)
    (h : ZDetectsFrame F) : ZDetectsFrame G :=
  fun j => klCondition_of_codeSpan_eq F G hspan (pureZ j) (h j)

/-- The sector-level `ZDetects` from the frame-level hypothesis.  Same proof as
`zDetects_of_detects_reindex`, with the detection hypothesis instantiated at
`Z_j` rather than derived from a weight bound. -/
theorem zDetects_of_frame {t : ℕ} {theta : Fin n → ℝ}
    (D : SectorDecomposition n t theta) (e : Fin K ≃ D.Index)
    (h : ∀ j : Fin n, SS.KLCondition (fun k => D.vec (e k)) (pureZ j)) :
    ZDetects D := by
  intro j
  obtain ⟨c, hc⟩ := h j
  refine ⟨c, ?_⟩
  intro u v
  have hj := hc (e.symm u) (e.symm v)
  simpa [pureZ] using hj

/-- The link-level statement the resolution consumes. -/
theorem link_zDetects {d t : ℕ} {theta : Fin n → ℝ}
    {C : ExactCode n K d} {D : SectorDecomposition n t theta}
    (link : MainTheory.FiniteLift.ExactCodeSectorLink C D)
    (h : ZDetectsFrame C.frame) : ZDetects D := by
  refine zDetects_of_frame D link.reindex ?_
  exact zDetectsFrame_of_codeSpan_eq C.frame
    (MainTheory.FiniteLift.reindexedSectorFrame D link.reindex) link.span_eq h

/-- The resolution-level statement, at the paper's hypothesis. -/
theorem resolution_zDetects {d : ℕ} {theta : Fin n → ℝ}
    {C : ExactCode n K d}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (h : ZDetectsFrame C.frame) : ZDetects R.sectors :=
  link_zDetects R.link h


/-! ## The three results, at the paper's hypothesis -/

/-- **`lem:phase-sectors` at "assume `P Z_j P = lambda_j P` for every `j`".** -/
theorem phaseSectors_of_zDetects {d : ℕ} (C : ExactCode n K d)
    (hZ : ZDetectsFrame C.frame) (theta : Fin n → ℝ)
    (hpres : CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta)) :
    (∀ alpha x, 0 ≤ sectorProbability
        (SectionTwoGeneral.resolutionOf C theta hpres).sectors alpha x) ∧
    (∀ alpha, ∑ x,
      sectorProbability (SectionTwoGeneral.resolutionOf C theta hpres).sectors
        alpha x = 1) ∧
    (∀ alpha,
      (sectorSupport (SectionTwoGeneral.resolutionOf C theta hpres).sectors
        alpha).Nonempty) ∧
    (∀ alpha beta, alpha ≠ beta →
      Disjoint
        (sectorSupport (SectionTwoGeneral.resolutionOf C theta hpres).sectors alpha)
        (sectorSupport (SectionTwoGeneral.resolutionOf C theta hpres).sectors beta)) ∧
    (∀ alpha x,
      x ∈ sectorSupport
          (SectionTwoGeneral.resolutionOf C theta hpres).sectors alpha →
      ∃ k : ℤ, MainTheory.RealGate.angle theta x
        - (SectionTwoGeneral.resolutionOf C theta hpres).sectors.phase alpha
          = (k : ℝ)) ∧
    ∃ mu : Fin n → ℝ, ∀ alpha j,
      sectorMean (SectionTwoGeneral.resolutionOf C theta hpres).sectors alpha j
        = mu j :=
  phaseSectorFull_package _
    (resolution_zDetects (SectionTwoGeneral.resolutionOf C theta hpres) hZ)

/-- **`cor:quantitative-projective-group` at the paper's hypothesis.**

The proof is the `2 <= d` one; the distance hypothesis appeared in it only as
`(R.zDetects hd)`, which `resolution_zDetects` now supplies from the `Z`
equations alone. -/
theorem quantitative_projective_group_of_zDetects {d B : ℕ}
    (beta : BinaryBeta.BetaBound (n + K - 1) B)
    (C : ExactCode n K d) (hZ : ZDetectsFrame C.frame)
    (g : IntrinsicGroup C) (hg : g ≠ 1) :
    ∃ q : ℕ,
      MainTheory.GeneralLiftOrder.HasPrimitiveLift C g q ∧
      orderOf g ∣ q ∧
      2 ≤ orderOf g ∧
      orderOf g ≤ q ∧
      2 ≤ q ∧
      q ≤ B := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector (v : LocalPhase n)
  have hpres := MainTheory.SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (v : LocalPhase n) v.2 theta hexp
  have hnt := MainTheory.SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (v : LocalPhase n) v.2 theta hexp hg
  set R := SectionTwoGeneral.resolutionOf C theta hpres with hR
  have ht : 2 ≤ R.sectorCount :=
    SectionTwoGeneral.two_le_sectorCount_of_projectively_nontrivial
      C theta hpres hnt
  have htK : R.sectorCount ≤ K := SectionTwoGeneral.sectorCount_le R.link
  have hbeta : BinaryBeta.BetaBound (n + R.sectorCount - 1) B :=
    MainTheory.QuantitativeGroup.betaBound_mono beta (by omega)
  obtain ⟨Lft, _, _, _, _, _, hle⟩ :=
    MainTheory.ColoredBound.quantitative_colored_finite_lift hbeta R.sectors
      (resolution_zDetects R hZ) ht
  have hlift := MainTheory.GeneralLiftOrder.hasPrimitiveLift_of_rationalLift
    v hexp hpres Lft
  have hdvd := MainTheory.GeneralLiftOrder.orderOf_dvd_of_hasPrimitiveLift hlift
  have hne0 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) Lft.order_pos.ne'
  have hne1 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 1 := by
    intro h1
    exact hg (orderOf_eq_one_iff.mp h1)
  have h2 : 2 ≤ orderOf (intrinsicClass (exactCodeProjector C) v) := by
    omega
  exact ⟨Lft.order, hlift, hdvd, h2, Nat.le_of_dvd Lft.order_pos hdvd,
    le_trans h2 (Nat.le_of_dvd Lft.order_pos hdvd), hle⟩

/-- The bounded representation, at the paper's hypothesis. -/
theorem hasBoundedRepresentation_of_zDetects {d : ℕ} (C : ExactCode n K d)
    (hZ : ZDetectsFrame C.frame) :
    MainTheory.BoundedRepresentation.HasBoundedRepresentation
      (MainTheory.BetaExists.betaOf (n + K - 1)) C := by
  intro g
  by_cases hg : g = 1
  · subst hg
    exact ⟨MainTheory.LabelledGates.trivialLabel
        (MainTheory.BetaExists.betaOf_pos _), 1, rfl,
      by rw [MainTheory.LabelledGates.gateOfLabel_trivial]; rfl⟩
  · obtain ⟨q, hlift, _, _, _, _, hqB⟩ :=
      quantitative_projective_group_of_zDetects
        (MainTheory.BetaExists.betaBound_betaOf (n + K - 1)) C hZ g hg
    exact MainTheory.GeneralFinitenessRank.boundedLabel_of_hasPrimitiveLift hqB hlift

set_option maxHeartbeats 1000000 in
/-- **The finiteness half of `thm:finite-projective-group`, at the paper's
hypothesis**: a rank-`K` code detecting every `Z_j` has a finite intrinsic
projective diagonal group. -/
theorem finite_intrinsicGroup_of_zDetects {d : ℕ} (C : ExactCode n K d)
    (hZ : ZDetectsFrame C.frame) : Finite (IntrinsicGroup C) :=
  MainTheory.BoundedRepresentation.finite_of_representation
    (hasBoundedRepresentation_of_zDetects C hZ)

/-- And the cyclicity of `cor:K2-q-bound` at rank two, on the same
hypothesis. -/
theorem cyclic_of_zDetects {d : ℕ} (C : ExactCode n 2 d)
    (hZ : ZDetectsFrame C.frame) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame)) :=
  MainTheory.RankTwoSSLP.cyclic_of_finite C
    (finite_intrinsicGroup_of_zDetects C hZ)

end MainTheory.ZDetection
