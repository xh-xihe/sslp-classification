import MainTheory.D3RationalLiftFiniteGenerator
import MainTheory.D3AutomaticOuterEntry

/-!
# Distance-three entrance from spectral sectors to the outer index

This file composes the qualitative rationalization theorem with the fully
constructed fresh sparse generator.  Starting with an actual
`LogicalSectorResolution` of a six-qubit distance-three code, it chooses the
rational coloured lift supplied by `FiniteLift.exists_rationalColoredLift`,
packages that lift as a primitive finite generator on the original code, and
then applies the automatic fresh-denominator construction and outer-index
theorem.

The final arbitrary-code theorem assumes only
`PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3` in addition to the
already proved binary determinant bound passed to this module.  In
particular, the older `D3ExtractionPrinciple` is not used: rationalization,
finite-generator packaging, the fresh order bound, and record entry are all
performed below by kernel-checked definitions and theorems.

The conclusion deliberately retains two independent pieces of information:

* the intermediate finite generator has the same projective action as the
  original real diagonal operation on the actual code; and
* the returned outer record has exactly the fresh modulus, logical order, and
  normalized angle (up to the returned coordinate permutation).

What this file does **not** claim is that the final coordinate permutation has
already been transported through the logical states, their supports/fibres,
or the KL equations.  Moreover the fresh generator is compared with the
locally-`X`- and unit-power-normalized finite operation on the explicitly
normalized code; it is not asserted to be the identical group element on the
original code.  These normalization and permutation transports are later
orbit-identification bridges.
-/

namespace MainTheory.D3SpectralOuterEntrance

open MainTheory
open MainTheory.D3AutomaticBoundedGenerator
open MainTheory.D3AutomaticOuterEntry
open MainTheory.D3NormalizedFreshPhase

noncomputable section

/-- The qualitative rational lift chosen from the kernel theorem for the
actual logical sector resolution.  Distance three supplies the required
weight-one `Z` detection. -/
def rationalLiftOfResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta) :
    FiniteLift.RationalColoredLift R.sectors :=
  Classical.choice
    (FiniteLift.exists_rationalColoredLift R.sectors
      (R.zDetects (by decide)))

/-- Canonical local instance for the least denominator of the chosen
qualitative rational lift. -/
def resolutionOrderNeZero
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta) :
    NeZero (rationalLiftOfResolution R).order :=
  ⟨(rationalLiftOfResolution R).order_pos.ne'⟩

/-- The chosen rational lift packaged as a genuine primitive finite
generator spanning the original code. -/
def finiteGeneratorOfResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    @RankTwoGlobal.FiniteGeneratorResolution 6 3 C
      (rationalLiftOfResolution R).order (resolutionOrderNeZero R) :=
  D3RationalLiftFiniteGenerator.finiteGeneratorOfLift
    R (rationalLiftOfResolution R) hnontrivial

/-- The finite operation associated with the chosen rational lift, exposed
without a dependent `NeZero` argument in its public type. -/
def resolutionFiniteGateEnd
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    Module.End ℂ (SS.State 6 ℂ) :=
  D3RationalLiftFiniteGenerator.finiteGeneratorOfLiftEnd
    R (rationalLiftOfResolution R) hnontrivial

/-- The canonical two-fibre certificate of the chosen finite generator. -/
def twoFiberOfResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    @RankTwoGlobal.TwoFiberCertificate 6 3
      (rationalLiftOfResolution R).order (resolutionOrderNeZero R) C
      (finiteGeneratorOfResolution R hnontrivial) := by
  letI : NeZero (rationalLiftOfResolution R).order :=
    resolutionOrderNeZero R
  exact canonicalTwoFiber (finiteGeneratorOfResolution R hnontrivial)

/-- The *fresh* least denominator constructed from the normalized two-fibre
data.  This is not the possibly larger order of the initially chosen lift. -/
def freshOrderOfResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) : ℕ := by
  letI : NeZero (rationalLiftOfResolution R).order :=
    resolutionOrderNeZero R
  exact
    (frameFreshSparsePhase
      (twoFiberOfResolution R hnontrivial)).data.order

/-- Logical projective order of the normalized fresh generator. -/
def freshLogicalOrderOfResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) : ℕ := by
  letI : NeZero (rationalLiftOfResolution R).order :=
    resolutionOrderNeZero R
  exact automaticFreshLogicalOrder (twoFiberOfResolution R hnontrivial)

/-- Natural representatives of the normalized fresh modular angle. -/
def freshNatAngleOfResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    OuterEnumeration.Angle6 := by
  letI : NeZero (rationalLiftOfResolution R).order :=
    resolutionOrderNeZero R
  exact automaticFreshNatAngle (twoFiberOfResolution R hnontrivial)

/-- The explicitly local-`X`-normalized exact code used by the fresh sparse
construction.  Keeping this code visible prevents a silent identification
with the original code. -/
def normalizedCodeOfResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    CodeSpec.ExactCode 6 2 3 := by
  letI : NeZero (rationalLiftOfResolution R).order :=
    resolutionOrderNeZero R
  exact normalizedCode (twoFiberOfResolution R hnontrivial)

/-- Finite gate of the fresh least-denominator generator, with both dependent
order instances kept internal. -/
def freshFiniteGateEndOfResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    Module.End ℂ (SS.State 6 ℂ) := by
  letI : NeZero (rationalLiftOfResolution R).order :=
    resolutionOrderNeZero R
  exact freshFiniteGateEnd (twoFiberOfResolution R hnontrivial)

/-- The locally normalized version of the initial finite gate.  This is the
operation to which the fresh generator is proved projectively equivalent;
transporting it back across local `X` and interpreting the coprime unit power
inside the original projective group are intentionally separate steps. -/
def normalizedFiniteGateEndOfResolution
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    Module.End ℂ (SS.State 6 ℂ) := by
  letI : NeZero (rationalLiftOfResolution R).order :=
    resolutionOrderNeZero R
  exact RankTwoGlobal.finiteGateEnd
    (finiteGeneratorOfResolution R hnontrivial).zeta
    (SixQubitSemanticEntrance.normalizedFiniteAngle
      (finiteGeneratorOfResolution R hnontrivial)
      (twoFiberOfResolution R hnontrivial))

/-- Exact, non-vacuous outer-record statement.  The record fields are fixed
by the three displayed parameters; an unrelated primitive record cannot
witness this proposition. -/
def ExactOuterRecordStatement
    (q m : ℕ) (a : OuterEnumeration.Angle6) : Prop :=
  2 ≤ q ∧ q ≤ 9 ∧
    ∃ record : OuterEnumeration.RawRecord,
      record ∈ OuterEnumeration.primitiveRecords ∧
      record.q = q ∧
      record.m = m ∧
      ∃ sigma : Equiv.Perm (Fin 6), record.a = a ∘ sigma

/-- Full semantic conclusion for a supplied logical sector resolution.  The
first conjunct binds the initial finite generator to the original operation;
the second binds the enumerated record to the automatically constructed fresh
generator. -/
def ResolutionOuterStatement
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) : Prop :=
  CodeSpec.SameProjectiveOnCode C.frame
      (resolutionFiniteGateEnd R hnontrivial)
      (PhaseSectorBridge.realGateEnd theta) ∧
    CodeSpec.SameProjectiveOnCode
      (normalizedCodeOfResolution R hnontrivial).frame
      (freshFiniteGateEndOfResolution R hnontrivial)
      (normalizedFiniteGateEndOfResolution R hnontrivial) ∧
    ExactOuterRecordStatement
      (freshOrderOfResolution R hnontrivial)
      (freshLogicalOrderOfResolution R hnontrivial)
      (freshNatAngleOfResolution R hnontrivial)

/-- The chosen finite generator is not an unrelated symmetry of the same
code: it agrees projectively with the original real operation on the code. -/
theorem finiteGeneratorOfResolution_sameProjective
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    CodeSpec.SameProjectiveOnCode C.frame
      (resolutionFiniteGateEnd R hnontrivial)
      (PhaseSectorBridge.realGateEnd theta) := by
  exact D3RationalLiftFiniteGenerator.finiteGeneratorOfLift_sameProjective
    R (rationalLiftOfResolution R) hnontrivial

/-- The fresh generator is linked to the normalized initial finite operation
on the explicitly normalized exact code.  This is the projective-action edge
used between rationalization and outer enumeration. -/
theorem freshGeneratorOfResolution_sameProjective_normalizedFinite
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    CodeSpec.SameProjectiveOnCode
      (normalizedCodeOfResolution R hnontrivial).frame
      (freshFiniteGateEndOfResolution R hnontrivial)
      (normalizedFiniteGateEndOfResolution R hnontrivial) := by
  letI : NeZero (rationalLiftOfResolution R).order :=
    resolutionOrderNeZero R
  exact automaticFreshGenerator_sameProjective_normalizedFinite
    (twoFiberOfResolution R hnontrivial)

/-- The automatically freshened generator produces a literal primitive outer
record with all three identifying fields retained. -/
theorem finiteGeneratorOfResolution_hasExactOuterRecord
    (betaSix : BinaryBeta.BetaBound 6 9)
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    ExactOuterRecordStatement
      (freshOrderOfResolution R hnontrivial)
      (freshLogicalOrderOfResolution R hnontrivial)
      (freshNatAngleOfResolution R hnontrivial) := by
  letI : NeZero (rationalLiftOfResolution R).order :=
    resolutionOrderNeZero R
  obtain ⟨hq2, hq9, record, hrecord, hq, hm, sigma, ha⟩ :=
    finiteGenerator_enters_primitive_outer_index betaSix
      (finiteGeneratorOfResolution R hnontrivial)
  exact ⟨hq2, hq9, record, hrecord, hq, hm, sigma, ha⟩

/-- Kernel composition from complete logical sector data to a code-linked,
bounded, exactly indexed finite representative. -/
theorem logicalSectorResolution_enters_outer
    (betaSix : BinaryBeta.BetaBound 6 9)
    {C : CodeSpec.ExactCode 6 2 3} {theta : Fin 6 → ℝ}
    (R : PhaseSectorBridge.LogicalSectorResolution C theta)
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    ResolutionOuterStatement R hnontrivial := by
  exact ⟨finiteGeneratorOfResolution_sameProjective R hnontrivial,
    freshGeneratorOfResolution_sameProjective_normalizedFinite
      R hnontrivial,
    finiteGeneratorOfResolution_hasExactOuterRecord
      betaSix R hnontrivial⟩

/-- Arbitrary-code entrance with the only remaining semantic premise exposed
as the finite-dimensional spectral extraction principle.  The rational lift
and every subsequent finite/sparse/outer object are constructed internally. -/
theorem arbitrary_code_enters_outer_from_spectral
    (spectral : PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3)
    (betaSix : BinaryBeta.BetaBound 6 9)
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    ∃ R : PhaseSectorBridge.LogicalSectorResolution C theta,
      ResolutionOuterStatement R hnontrivial := by
  obtain ⟨R⟩ := spectral C theta hpres
  exact ⟨R, logicalSectorResolution_enters_outer
    betaSix R hnontrivial⟩

/-- Code-only form.  The preserving nontrivial real diagonal operation is
unpacked from the code's symmetry hypothesis; spectral extraction is the sole
unproved semantic interface. -/
theorem code_with_nontrivial_diagonal_symmetry_enters_outer_from_spectral
    (spectral : PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3)
    (betaSix : BinaryBeta.BetaBound 6 9)
    (C : CodeSpec.ExactCode 6 2 3)
    (hsymmetry :
      SixQubitSemanticEntrance.HasNontrivialDiagonalSymmetry C) :
    ∃ theta : Fin 6 → ℝ,
      CodeSpec.CodePreserving C.frame
          (PhaseSectorBridge.realGateEnd theta) ∧
      ∃ hnontrivial :
          SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta,
        ∃ R : PhaseSectorBridge.LogicalSectorResolution C theta,
          ResolutionOuterStatement R hnontrivial := by
  obtain ⟨theta, hpres, hnontrivial⟩ := hsymmetry
  obtain ⟨R, hR⟩ := arbitrary_code_enters_outer_from_spectral
    spectral betaSix C theta hpres hnontrivial
  exact ⟨theta, hpres, hnontrivial, R, hR⟩

end

end MainTheory.D3SpectralOuterEntrance
