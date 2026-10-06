import MainTheory.QuantitativeGroup
import MainTheory.GeneralSpectralSectors

/-!
# The sharp clause of `cor:quantitative-projective-group`

The corollary's second sentence reads: *more sharply, an element with `t`
distinct logical eigenvalues admits `q <= beta_{n+t-1}`*.  The repository's
`QuantitativeGroup.exists_sectorCount_qMin_le` states
`exists t, 2 <= t /\ t <= K /\ ...`, and nothing ties that `t` to the number of
distinct logical eigenvalues of the element.  So as a certified proposition it
was the coarse `beta_{n+K-1}` bound wearing the sharp bound's name.

The gap is one `Classical.choice`.  `SectionTwoGeneral.resolutionOf` picks
*some* logical sector resolution, and its `sectorCount` is then opaque.  But
the canonical resolution is right there: `GeneralSpectral.logicalSectorResolution`
sets `sectorCount := GeneralSpectral.sectorCount hpres`, which is by definition
`Fintype.card (SectorIndex hpres)` -- the number of distinct eigenvalues of the
gate restricted to the code space, i.e. the paper's `t`.

So route the bound through the canonical resolution instead of the chosen one.
Two lemmas had to be freed of the choice: `two_le_sectorCount_of_resolution`
(now stated at an arbitrary resolution in `SectionTwoGeneral`) and the
primitive-lift step below.  Neither needed a new argument; both proofs already
used only the resolution's fields.

The statement quantifies over a *representative* `v` of the class rather than
asserting that `t` is an invariant of the class.  That is deliberate: making
`t` a function of the projective class needs its own theta-independence
argument, which is not here.
-/

namespace MainTheory.SharpSectorBound

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.GeneralLiftOrder
open MainTheory.SectionTwoGeneral
open MainTheory.PhaseSectorBridge
open MainTheory.D3RationalLiftFiniteGenerator

variable {n K d : ℕ}

/-- **`GeneralLiftOrder.hasPrimitiveLift_of_rationalLift` at an arbitrary
resolution.**

The original is stated at `resolutionOf C theta hpres`; its proof uses only
the resolution's own fields, so nothing is lost by taking the resolution as an
argument, and the canonical one becomes usable. -/
theorem hasPrimitiveLift_of_rationalLift' {C : CodeSpec.ExactCode n K d}
    {theta : Fin n → ℝ}
    (v : diagonalSymmetryGroup (exactCodeProjector C))
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ)))
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (L : MainTheory.FiniteLift.RationalColoredLift R.sectors) :
    HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) L.order := by
  letI : NeZero L.order := ⟨L.order_pos.ne'⟩
  exact ⟨inferInstance, modularAngle L, liftSymmetry R L,
    modularAngle_primitive_lift _ L, rfl,
    intrinsicClass_liftSymmetry _ L v hexp⟩

/-- **The sharp bound, with `t` the actual number of distinct logical
eigenvalues.**

`GeneralSpectral.sectorCount hpres` is `Fintype.card (SectorIndex hpres)`,
and `SectorIndex` is `Module.End.Eigenvalues` of the gate restricted to the
code space.  So the `t` in the bound below is the paper's `t`, not a
resolution's bookkeeping field. -/
theorem hasPrimitiveLift_le_beta_sectorCount {B : ℕ}
    (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (v : diagonalSymmetryGroup (exactCodeProjector C)) (theta : Fin n → ℝ)
    (hexp : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = (((v : LocalPhase n) j : ℂ)))
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id)
    (beta : MainTheory.BinaryBeta.BetaBound
      (n + MainTheory.GeneralSpectral.sectorCount hpres - 1) B) :
    ∃ q : ℕ,
      HasPrimitiveLift C (intrinsicClass (exactCodeProjector C) v) q ∧
      2 ≤ q ∧ q ≤ B := by
  set R := MainTheory.GeneralSpectral.logicalSectorResolution
    (F := C.frame) hpres C rfl with hR
  have hcount : R.sectorCount = MainTheory.GeneralSpectral.sectorCount hpres :=
    rfl
  have ht : 2 ≤ R.sectorCount := two_le_sectorCount_of_resolution hnt R
  have hbeta : MainTheory.BinaryBeta.BetaBound (n + R.sectorCount - 1) B := by
    rw [hcount]; exact beta
  obtain ⟨L, hord, _, _, _, _, hle⟩ :=
    MainTheory.ColoredBound.quantitative_colored_finite_lift hbeta R.sectors
      (R.zDetects hd) ht
  exact ⟨L.order, hasPrimitiveLift_of_rationalLift' v hexp R L, hord, hle⟩

end MainTheory.SharpSectorBound
