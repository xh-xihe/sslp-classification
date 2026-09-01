import MainTheory.BoundedRepresentationProof
import MainTheory.Generated.BinaryBetaSixKernel.Certificate
import MainTheory.D3LogicalSpectralExtraction

/-!
# The bounded representation, with the modulus bound supplied

`BoundedRepresentationProof` carries `BinaryBeta.BetaBound 6 9` as a
hypothesis so that it does not drag the 1716-case certificate into every
downstream file.  That certificate is proved, in
`MainTheory/Generated/BinaryBetaSixKernel/Certificate.lean`, so this file
supplies it and leaves `PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3`
as the single remaining premise.

Nothing here is a new mathematical step: it is the point where the two halves
of the argument -- the finite determinant bound and the semantic entrance --
are joined.
-/

namespace MainTheory.BoundedRepresentationCertified

open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge

/-- **Every exact six-qubit code has bounded representations**, given only the
spectral extraction principle. -/
theorem hasBoundedRepresentation
    (spectral : PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3)
    (C : CodeSpec.ExactCode 6 2 3) :
    BoundedRepresentation.HasBoundedRepresentation 9 C :=
  BoundedRepresentationProof.hasBoundedRepresentation spectral
    MainTheory.Generated.BinaryBetaSixKernel.Certificate.upper C

/-- **The intrinsic projective diagonal group of an exact six-qubit code is
finite**, given only the spectral extraction principle.

This is the conclusion the Cartan-free route was built for: finiteness comes
from a surjection off the bounded label type, with no Lie theory anywhere. -/
theorem finite_intrinsicGroup
    (spectral : PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3)
    (C : CodeSpec.ExactCode 6 2 3) :
    Finite (IntrinsicGroup C) :=
  BoundedRepresentation.finite_of_representation
    (hasBoundedRepresentation spectral C)

/-- The finite-cyclic classification inputs, with both the modulus bound and
the bounded representation discharged. -/
noncomputable def intrinsicFiniteCyclicInputs
    (spectral : PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3)
    (C : CodeSpec.ExactCode 6 2 3)
    (chi : IntrinsicGroup C →* ℂ)
    (hchi : Function.Injective chi) :
    IntrinsicFiniteCyclicInputs (B := 9) C :=
  BoundedRepresentation.inputsOfRepresentation
    (hasBoundedRepresentation spectral C) chi hchi

/-- Consequently the group is cyclic. -/
theorem isCyclic_intrinsicGroup
    (spectral : PhaseSectorBridge.SpectralExtractionPrinciple 6 2 3)
    (C : CodeSpec.ExactCode 6 2 3)
    (chi : IntrinsicGroup C →* ℂ)
    (hchi : Function.Injective chi) :
    IsCyclic (IntrinsicGroup C) :=
  (intrinsicFiniteCyclicInputs spectral C chi hchi).isCyclic

/-! ## Unconditional forms

`D3LogicalSpectralExtraction.spectralExtraction` proves
`SpectralExtractionPrinciple 6 2 3` outright, so the premise carried above can
simply be discharged.  Nothing below has any hypothesis left. -/

/-- **Every exact six-qubit code has bounded representations.** -/
theorem hasBoundedRepresentation_unconditional
    (C : CodeSpec.ExactCode 6 2 3) :
    BoundedRepresentation.HasBoundedRepresentation 9 C :=
  hasBoundedRepresentation
    MainTheory.D3LogicalSpectralExtraction.spectralExtraction C

/-- **The intrinsic projective diagonal group of an exact six-qubit code is
finite.**  No Lie theory, and no remaining semantic premise. -/
theorem finite_intrinsicGroup_unconditional
    (C : CodeSpec.ExactCode 6 2 3) : Finite (IntrinsicGroup C) :=
  BoundedRepresentation.finite_of_representation
    (hasBoundedRepresentation_unconditional C)

end MainTheory.BoundedRepresentationCertified
