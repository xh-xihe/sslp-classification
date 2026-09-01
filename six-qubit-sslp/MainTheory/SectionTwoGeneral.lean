import MainTheory.GeneralSpectralSectors
import MainTheory.SectorMeanValue
import MainTheory.FiniteLift
import MainTheory.PivotSize
import MainTheory.D3RationalLiftFiniteGenerator

/-!
# Section II at general `(n, K, d)`

With `GeneralSpectral.spectralExtractionPrinciple` proved for every code
shape, the results of Section II no longer need a supplied
`SectorDecomposition`: they can be stated from the paper's own hypotheses --
an exact code and a diagonal operation preserving it.

This file restates the two summary theorems in that form.  Nothing new is
proved; what changes is that the spectral data is now produced rather than
assumed, which is what makes these the paper's statements rather than
conditional versions of them.
-/

namespace MainTheory.SectionTwoGeneral

open MainTheory.PhaseSectorFull
open MainTheory.GeneralSpectral

variable {n K d : ℕ}

/-- The sector resolution produced for any preserving diagonal operation. -/
noncomputable def resolutionOf (C : CodeSpec.ExactCode n K d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta)) :
    PhaseSectorBridge.LogicalSectorResolution C theta :=
  Classical.choice (spectralExtractionPrinciple n K d C theta hpres)

/-- **`lem:phase-sectors` at general `(n, K, d)`.**

Stated on THE resolution of the given code and gate, not on an existentially
quantified decomposition: an existential form would be satisfiable by a
single computational basis vector, which is an eigenvector of every diagonal
gate, and would then use neither the distance nor the preservation
hypothesis. -/
theorem phaseSectors (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta)) :
    (∀ alpha x, 0 ≤ sectorProbability (resolutionOf C theta hpres).sectors alpha x) ∧
    (∀ alpha, ∑ x,
      sectorProbability (resolutionOf C theta hpres).sectors alpha x = 1) ∧
    (∀ alpha,
      (sectorSupport (resolutionOf C theta hpres).sectors alpha).Nonempty) ∧
    (∀ alpha beta, alpha ≠ beta →
      Disjoint (sectorSupport (resolutionOf C theta hpres).sectors alpha)
        (sectorSupport (resolutionOf C theta hpres).sectors beta)) ∧
    (∀ alpha x, x ∈ sectorSupport (resolutionOf C theta hpres).sectors alpha →
      ∃ k : ℤ, MainTheory.RealGate.angle theta x
        - (resolutionOf C theta hpres).sectors.phase alpha = (k : ℝ)) ∧
    ∃ mu : Fin n → ℝ, ∀ alpha j,
      sectorMean (resolutionOf C theta hpres).sectors alpha j = mu j :=
  phaseSectorFull_package _ ((resolutionOf C theta hpres).zDetects hd)

/-- The sector frame really is a frame for the given code: its span is the
code span.  This is what ties the resolution above to `C`. -/
theorem phaseSectors_span (C : CodeSpec.ExactCode n K d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta)) :
    CodeSpec.codeSpan C.frame
      = CodeSpec.codeSpan (MainTheory.FiniteLift.reindexedSectorFrame
        (resolutionOf C theta hpres).sectors
        (resolutionOf C theta hpres).link.reindex) :=
  (resolutionOf C theta hpres).link.span_eq

/-- **The common first moment is the number-operator scalar**, at general
`(n, K, d)`: `eq:Nj-detection`. -/
theorem phaseSectors_mean (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta))
    (alpha : Fin (resolutionOf C theta hpres).sectorCount) (j : Fin n) :
    ((sectorMean (resolutionOf C theta hpres).sectors alpha j : ℝ) : ℂ)
      = (1 - SectorMeanValue.klScalar (resolutionOf C theta hpres).sectors
          ((resolutionOf C theta hpres).zDetects hd) j) / 2 :=
  SectorMeanValue.sectorMean_eq_klScalar _ _ alpha j

/-! ## Projective nontriviality is exactly two or more sectors -/

/-- With a single sector the gate acts on the code by one scalar, so it is
projectively trivial.  Contrapositively, the paper's hypothesis "the logical
action is projectively nontrivial" is exactly `2 <= t`. -/
theorem two_le_sectorCount_of_projectively_nontrivial
    (C : CodeSpec.ExactCode n K d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    2 ≤ (resolutionOf C theta hpres).sectorCount := by
  by_contra hlt
  push_neg at hlt
  set R := resolutionOf C theta hpres with hR
  have hone : R.sectorCount = 1 := by
    have := R.sectors.sectorCount_pos
    omega
  refine hnt ⟨MainTheory.PhaseSectorFull.phaseExp
    (R.sectors.phase ⟨0, R.sectors.sectorCount_pos⟩), ?_, ?_⟩
  · exact Complex.exp_ne_zero _
  · intro phi hphi
    rw [R.link.span_eq] at hphi
    refine Submodule.span_induction
      (p := fun psi _ => PhaseSectorBridge.realGateEnd theta psi
        = MainTheory.PhaseSectorFull.phaseExp
          (R.sectors.phase ⟨0, R.sectors.sectorCount_pos⟩) • psi)
      ?_ ?_ ?_ ?_ hphi
    · rintro _ ⟨k, rfl⟩
      have heig := R.sectors.eigen (R.link.reindex k)
      have hsec : (R.link.reindex k).1
          = (⟨0, R.sectors.sectorCount_pos⟩ : Fin R.sectorCount) := by
        apply Fin.ext
        have := (R.link.reindex k).1.isLt
        omega
      funext x
      have := congrFun heig x
      simpa [MainTheory.FiniteLift.reindexedSectorFrame, hsec,
        PhaseSectorBridge.realGateEnd_apply] using this
    · simp only [map_zero, smul_zero]
    · intro a b _ _ ha hb
      rw [map_add, ha, hb, smul_add]
    · intro a psi _ hpsi
      rw [map_smul, hpsi, smul_comm]

/-- **`thm:qualitative-finite-lift` at general `(n, K, d)`.**

A preserving diagonal operation with a projectively nontrivial logical action
has a primitive root-of-unity physical representative of finite order at least
two, inducing the same projective sector action.

The last clause is `eq:qualitative-m-divides-q` in the form the general theory
proves it: every relative logical eigenvalue is cleared by `L.order`, i.e. is
an `order`-th root of unity.  An earlier version of this statement dropped it;
it is kept here. -/
theorem qualitativeFiniteLift (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta))
    (hnontrivial : 2 ≤ (resolutionOf C theta hpres).sectorCount) :
    ∃ L : MainTheory.FiniteLift.RationalColoredLift
        (resolutionOf C theta hpres).sectors,
      2 ≤ L.order ∧
      MainTheory.FiniteLift.SameProjectiveSectorAction
        (resolutionOf C theta hpres).sectors (fun j => (L.physical j : ℝ)) ∧
      (∀ j, (L.order : ℚ) * L.physical j = (L.numerator j : ℚ)) ∧
      (∀ e : ℕ, e ∣ L.order → (∀ j, (e : ℤ) ∣ L.numerator j) → e = 1) ∧
      (∀ alpha, ∃ b : ℤ,
        (L.order : ℝ) * ((resolutionOf C theta hpres).sectors.phase alpha
          - (resolutionOf C theta hpres).sectors.phase
            (MainTheory.FiniteLift.baseSector
              (resolutionOf C theta hpres).sectors)) = (b : ℝ)) := by
  obtain ⟨L, h2, hsame, hnum, hprim, _, hclear⟩ :=
    MainTheory.FiniteLift.qualitative_finite_lift
      (resolutionOf C theta hpres).sectors
      ((resolutionOf C theta hpres).zDetects hd) hnontrivial
  exact ⟨L, h2, hsame, hnum, hprim, hclear⟩

/-- **`thm:qualitative-finite-lift` with the paper's own hypothesis.**

Instead of `2 <= t`, this takes projective nontriviality of the logical
action, which is what the paper assumes; the two are the same by
`two_le_sectorCount_of_projectively_nontrivial`. -/
theorem qualitativeFiniteLift_of_nontrivial (C : CodeSpec.ExactCode n K d)
    (hd : 2 ≤ d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ L : MainTheory.FiniteLift.RationalColoredLift
        (resolutionOf C theta hpres).sectors,
      2 ≤ L.order ∧
      MainTheory.FiniteLift.SameProjectiveSectorAction
        (resolutionOf C theta hpres).sectors (fun j => (L.physical j : ℝ)) ∧
      (∀ j, (L.order : ℚ) * L.physical j = (L.numerator j : ℚ)) ∧
      (∀ e : ℕ, e ∣ L.order → (∀ j, (e : ℤ) ∣ L.numerator j) → e = 1) ∧
      (∀ alpha, ∃ b : ℤ,
        (L.order : ℝ) * ((resolutionOf C theta hpres).sectors.phase alpha
          - (resolutionOf C theta hpres).sectors.phase
            (MainTheory.FiniteLift.baseSector
              (resolutionOf C theta hpres).sectors)) = (b : ℝ)) :=
  qualitativeFiniteLift C hd theta hpres
    (two_le_sectorCount_of_projectively_nontrivial C theta hpres hnt)

/-! ## A finite generator, from the code alone

Chaining the general spectral extraction with the now-general packaging of a
rational lift as a root-of-unity gate: for any exact rank-two code of distance
at least two carrying a projectively nontrivial diagonal operation, a genuine
`FiniteGeneratorResolution` exists.  Previously this object could only be
constructed at `(6, 2, 3)`. -/

/-- The rational coloured lift of the resolution, at general `(n, 2, d)`. -/
noncomputable def rationalLift (C : CodeSpec.ExactCode n 2 d) (hd : 2 ≤ d)
    (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta)) :
    MainTheory.FiniteLift.RationalColoredLift (resolutionOf C theta hpres).sectors :=
  Classical.choice
    (MainTheory.FiniteLift.exists_rationalColoredLift _
      ((resolutionOf C theta hpres).zDetects hd))

/-- **A finite generator resolution exists for every exact rank-two code with
a projectively nontrivial diagonal operation**, at general `n` and `d`. -/
noncomputable def finiteGenerator (C : CodeSpec.ExactCode n 2 d) (hd : 2 ≤ d)
    (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    @RankTwoGlobal.FiniteGeneratorResolution n d C
      (rationalLift C hd theta hpres).order
      ⟨(rationalLift C hd theta hpres).order_pos.ne'⟩ :=
  MainTheory.D3RationalLiftFiniteGenerator.finiteGeneratorOfLift
    (resolutionOf C theta hpres) (rationalLift C hd theta hpres) hnt

/-- The generator really represents the given operation: the two induce the
same projective action on the code. -/
theorem finiteGenerator_sameProjective (C : CodeSpec.ExactCode n 2 d) (hd : 2 ≤ d)
    (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    CodeSpec.SameProjectiveOnCode C.frame
      (MainTheory.D3RationalLiftFiniteGenerator.finiteGeneratorOfLiftEnd
        (resolutionOf C theta hpres) (rationalLift C hd theta hpres) hnt)
      (PhaseSectorBridge.realGateEnd theta) :=
  MainTheory.D3RationalLiftFiniteGenerator.finiteGeneratorOfLift_sameProjective
    (resolutionOf C theta hpres) (rationalLift C hd theta hpres) hnt

end MainTheory.SectionTwoGeneral
