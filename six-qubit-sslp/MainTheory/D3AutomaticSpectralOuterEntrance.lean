import MainTheory.D3LogicalSpectralExtraction
import MainTheory.D3SpectralOuterEntrance

/-!
# Automatic spectral entrance to the bounded outer index

The two-dimensional spectral extraction is now a kernel theorem, so the
semantic entrance no longer needs it as an explicit premise.  This lightweight
endpoint deliberately leaves the independent binary determinant bound as an
argument; the generated beta-six certificate can be substituted in a final
thin module without coupling this semantic chain to the large generated DAG.

The conclusion remains the exact `ResolutionOuterStatement`.  In particular,
this file does not claim the still-missing transport through the final
coordinate permutation into generated orbit fibres or no-go certificates.
-/

namespace MainTheory.D3AutomaticSpectralOuterEntrance

open MainTheory
open MainTheory.D3SpectralOuterEntrance

noncomputable section

/-- Every preserving projectively nontrivial real diagonal operation enters
the exact fresh outer index; the only input left here is the independent
six-row binary determinant bound. -/
theorem arbitrary_code_enters_outer
    (betaSix : BinaryBeta.BetaBound 6 9)
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnontrivial :
      SixQubitSemanticEntrance.ProjectivelyNontrivialReal C theta) :
    ∃ R : PhaseSectorBridge.LogicalSectorResolution C theta,
      ResolutionOuterStatement R hnontrivial :=
  arbitrary_code_enters_outer_from_spectral
    D3LogicalSpectralExtraction.spectralExtraction betaSix
    C theta hpres hnontrivial

/-- Code-only form after unpacking the existence of a preserving nontrivial
real diagonal symmetry. -/
theorem code_with_nontrivial_diagonal_symmetry_enters_outer
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
          ResolutionOuterStatement R hnontrivial :=
  code_with_nontrivial_diagonal_symmetry_enters_outer_from_spectral
    D3LogicalSpectralExtraction.spectralExtraction betaSix C hsymmetry

end

end MainTheory.D3AutomaticSpectralOuterEntrance
