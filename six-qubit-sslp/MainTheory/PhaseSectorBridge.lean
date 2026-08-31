import MainTheory.FiniteLift

/-!
# Bridge from a code-preserving real diagonal gate to logical phase sectors

`PhaseSectorFull.SectorDecomposition` contains the finite orthonormal
eigenbasis needed by the phase-sector and finite-lift arguments.
`FiniteLift.ExactCodeSectorLink` says that this eigenbasis spans the actual
code, not merely an unrelated auxiliary space.  This file packages those two
pieces into the exact output that a finite-dimensional spectral theorem must
produce.

The important direction

```
CodePreserving C.frame (realGateEnd theta)
  -> Nonempty (LogicalSectorResolution C theta)
```

is deliberately *not* asserted as a theorem below.  It requires the spectral
theorem for the unitary restriction of `D(theta)` to the finite-dimensional
code space, followed by grouping equal eigenvalues and choosing real phase
representatives.  The current repository has not yet formalized that
extraction.  `SpectralExtractionPrinciple` gives the missing statement an
explicit name so that later aggregate theorems cannot silently treat it as
proved.

What is kernel-proved here is the converse semantic check: supplied complete
sector data really does imply that the real diagonal gate preserves the code.
-/

namespace MainTheory.PhaseSectorBridge

open MainTheory.PhaseSectorFull

noncomputable section

variable {n K d : ℕ} {theta : Fin n → ℝ}

/-- The real diagonal gate as a complex-linear endomorphism of the physical
Hilbert space. -/
noncomputable def realGateEnd (theta : Fin n → ℝ) :
    Module.End ℂ (SS.State n ℂ) where
  toFun := MainTheory.RealGate.realGate theta
  map_add' := by
    intro phi chi
    funext x
    simp only [MainTheory.RealGate.realGate, Pi.add_apply, mul_add]
  map_smul' := by
    intro a phi
    funext x
    simp only [MainTheory.RealGate.realGate, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp] theorem realGateEnd_apply (theta : Fin n → ℝ) (phi : SS.State n ℂ) :
    realGateEnd theta phi = MainTheory.RealGate.realGate theta phi := rfl

/-- Complete finite spectral data for the restriction of `D(theta)` to an
exact code.  The sector vectors are permitted to be an arbitrary orthonormal
logical eigenbasis: `link.span_eq`, rather than equality with the stored frame,
is the basis-independent completeness condition. -/
structure LogicalSectorResolution
    (C : MainTheory.CodeSpec.ExactCode n K d) (theta : Fin n → ℝ) where
  sectorCount : ℕ
  sectors : SectorDecomposition n sectorCount theta
  link : MainTheory.FiniteLift.ExactCodeSectorLink C sectors

/-- Forget the code-completeness data and retain the phase-sector
decomposition consumed by the geometric argument. -/
abbrev LogicalSectorResolution.decomposition
    {C : MainTheory.CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta) := R.sectors

/-- Forget the spectral data and retain the exact-code/sector-span bridge
consumed by the finite-lift argument. -/
abbrev LogicalSectorResolution.codeLink
    {C : MainTheory.CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta) := R.link

/-- An exact distance-at-least-two code transfers its weight-one `Z`
Knill--Laflamme equations to every vector of the complete sector resolution.
This is the hypothesis used by the equal-sector-means theorem. -/
theorem LogicalSectorResolution.zDetects
    {C : MainTheory.CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta) (hd : 2 ≤ d) :
    ZDetects R.sectors :=
  R.link.zDetects hd

/-- A complete logical sector resolution is not spurious: its eigenvector and
span clauses imply that the displayed real diagonal gate preserves the actual
code subspace. -/
theorem LogicalSectorResolution.codePreserving
    {C : MainTheory.CodeSpec.ExactCode n K d}
    (R : LogicalSectorResolution C theta) :
    MainTheory.CodeSpec.CodePreserving C.frame (realGateEnd theta) := by
  intro phi hphi
  rw [R.link.span_eq] at hphi ⊢
  refine Submodule.span_induction
    (p := fun psi _ =>
      realGateEnd theta psi ∈
        MainTheory.CodeSpec.codeSpan
          (MainTheory.FiniteLift.reindexedSectorFrame
            R.sectors R.link.reindex)) ?_ ?_ ?_ ?_ hphi
  · rintro _ ⟨k, rfl⟩
    change MainTheory.RealGate.realGate theta
        (R.sectors.vec (R.link.reindex k)) ∈ _
    rw [R.sectors.eigen (R.link.reindex k)]
    exact (MainTheory.CodeSpec.codeSpan
      (MainTheory.FiniteLift.reindexedSectorFrame
        R.sectors R.link.reindex)).smul_mem
          (phaseExp (R.sectors.phase (R.link.reindex k).1))
          (Submodule.subset_span (Set.mem_range_self k))
  · change realGateEnd theta 0 ∈ _
    rw [map_zero]
    exact (MainTheory.CodeSpec.codeSpan
      (MainTheory.FiniteLift.reindexedSectorFrame
        R.sectors R.link.reindex)).zero_mem
  · intro x y _ _ hx hy
    change realGateEnd theta (x + y) ∈ _
    rw [map_add]
    exact (MainTheory.CodeSpec.codeSpan
      (MainTheory.FiniteLift.reindexedSectorFrame
        R.sectors R.link.reindex)).add_mem hx hy
  · intro a x _ hx
    change realGateEnd theta (a • x) ∈ _
    rw [map_smul]
    exact (MainTheory.CodeSpec.codeSpan
      (MainTheory.FiniteLift.reindexedSectorFrame
        R.sectors R.link.reindex)).smul_mem a hx

/-- The precise remaining spectral-theorem obligation for a fixed code type.
No inhabitant of this proposition is postulated in this development. -/
def SpectralExtractionPrinciple (n K d : ℕ) : Prop :=
  ∀ (C : MainTheory.CodeSpec.ExactCode n K d) (theta : Fin n → ℝ),
    MainTheory.CodeSpec.CodePreserving C.frame (realGateEnd theta) →
      Nonempty (LogicalSectorResolution C theta)

/-- Once an explicit spectral-extraction theorem is supplied, it produces the
complete sector object used by all downstream phase-sector arguments.  This
lemma is only application of that explicit premise; it does not manufacture
the missing premise. -/
theorem resolution_of_extraction
    (hspectral : SpectralExtractionPrinciple n K d)
    (C : MainTheory.CodeSpec.ExactCode n K d) (theta : Fin n → ℝ)
    (hpres : MainTheory.CodeSpec.CodePreserving C.frame (realGateEnd theta)) :
    Nonempty (LogicalSectorResolution C theta) :=
  hspectral C theta hpres

end

end MainTheory.PhaseSectorBridge
