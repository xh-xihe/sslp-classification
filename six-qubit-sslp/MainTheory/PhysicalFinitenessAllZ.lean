import MainTheory.PhysicalDetectedComponentFactor
import MainTheory.PhysicalSymmetryEquivalence
import MainTheory.PhysicalStabilizerCompact

namespace MainTheory.PhysicalComponentFactor

open MainTheory.ClassificationLevels MainTheory.PhysicalTorusCells
open MainTheory.PhysicalIntrinsicBridge MainTheory.DiagonalInfinitesimal

noncomputable section

variable {n : ℕ}

theorem logicalHom_surjective (P : CodeProjector n) : Function.Surjective (logicalHom P) :=
  (QuotientGroup.mk'_surjective _).comp (symmetryHom_surjective P)

theorem detectedComponentFactor_surjective (P : CodeProjector n) (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel) :
    Function.Surjective (detectedComponentFactor P μ hμ) := by
  intro g
  obtain ⟨u, hu⟩ := logicalHom_surjective P g
  exact ⟨QuotientGroup.mk u, hu⟩

/-- The exact physical-component proof of the manuscript's finiteness theorem,
under only its displayed Z-detection hypothesis and for arbitrary projectors. -/
theorem finite_intrinsic_of_z_detection (P : CodeProjector n) (lam : Fin n → ℂ)
    (hz : ∀ j, P.kernel *
      MainTheory.PauliKernelTrace.pauliKernel (MainTheory.NumberOperator.zPauli j) *
      P.kernel = lam j • P.kernel) :
    Finite (IntrinsicProjectiveDiagonalLogicalGroup P) := by
  obtain ⟨μ, hμ⟩ := number_compression_of_z_detection P lam hz
  haveI := finite_physical_component_group P
  exact Finite.of_surjective _
    (detectedComponentFactor_surjective P (fun j => (μ j : ℂ)) hμ)

end

end MainTheory.PhysicalComponentFactor
