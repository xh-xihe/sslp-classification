import MainTheory.D3AutomaticSpectralOuterEntrance
import MainTheory.Generated.BinaryBetaSixKernel.Certificate

/-!
# Certified six-qubit spectral entrance

This thin endpoint instantiates the universal binary determinant premise in
`D3AutomaticSpectralOuterEntrance` with the generated, fully kernel-checked
theorem `BinaryBetaSixKernel.Certificate.upper`.  The finite-dimensional
spectral extraction is now constructed internally by
`D3LogicalSpectralExtraction`, so it is no longer an explicit premise.

No orbit/fibre transport through the final coordinate permutation is asserted
here; the precise conclusion remains `ResolutionOuterStatement`.
-/

namespace MainTheory.D3CertifiedSpectralOuterEntrance

open MainTheory
open MainTheory.D3SpectralOuterEntrance

noncomputable section

/-- Arbitrary preserving nontrivial real diagonal operation enters the exact
fresh outer index.  Both the logical spectral resolution and the beta-six
determinant bound are supplied by kernel theorems. -/
theorem arbitrary_code_enters_outer
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    ∃ R : PhaseSectorBridge.LogicalSectorResolution C theta,
      ResolutionOuterStatement R hnontrivial :=
  D3AutomaticSpectralOuterEntrance.arbitrary_code_enters_outer
    MainTheory.Generated.BinaryBetaSixKernel.Certificate.upper
    C theta hpres hnontrivial

/-- Code-only form: after choosing a preserving nontrivial diagonal symmetry,
the spectral resolution and determinant bound are both discharged internally.
The conclusion deliberately stops before final coordinate-permutation
transport into generated orbit fibres. -/
theorem code_with_nontrivial_diagonal_symmetry_enters_outer
    (C : CodeSpec.ExactCode 6 2 3)
    (hsymmetry :
      SixQubitSemanticEntrance.HasNontrivialDiagonalSymmetry C) :
    ∃ theta : Fin 6 → ℝ,
      CodeSpec.CodePreserving C.frame
          (PhaseSectorBridge.realGateEnd theta) ∧
      ∃ hnontrivial :
          SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta,
        ∃ R : PhaseSectorBridge.LogicalSectorResolution C theta,
          ResolutionOuterStatement R hnontrivial :=
  D3AutomaticSpectralOuterEntrance.code_with_nontrivial_diagonal_symmetry_enters_outer
      MainTheory.Generated.BinaryBetaSixKernel.Certificate.upper C hsymmetry

end

end MainTheory.D3CertifiedSpectralOuterEntrance
