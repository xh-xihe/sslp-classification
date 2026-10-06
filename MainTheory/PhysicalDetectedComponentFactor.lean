import MainTheory.PhysicalComponentFactor
import MainTheory.RealNumberCompression

namespace MainTheory.PhysicalComponentFactor

open scoped BigOperators
open MainTheory.ClassificationLevels MainTheory.PhysicalTorusCells
open MainTheory.DiagonalInfinitesimal

noncomputable section

variable {n : ℕ}

/-- Only the displayed Z-detection hypothesis is needed; a full KL code is
not required for the physical-component argument. -/
theorem number_compression_of_z_detection (P : CodeProjector n)
    (lam : Fin n → ℂ)
    (hz : ∀ j, P.kernel *
      MainTheory.PauliKernelTrace.pauliKernel (MainTheory.NumberOperator.zPauli j) *
      P.kernel = lam j • P.kernel) :
    ∃ μ : Fin n → ℝ, ∀ j,
      P.kernel * numberKernel j * P.kernel = (μ j : ℂ) • P.kernel := by
  have hc (j : Fin n) : P.kernel * numberKernel j * P.kernel =
      ((2 : ℂ)⁻¹ * (1 - lam j)) • P.kernel := by
    rw [numberKernel_eq_half_one_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, P.idempotent, hz]
    module
  let mu : Fin n → ℂ := fun j => (2 : ℂ)⁻¹ * (1 - lam j)
  have hmu (j : Fin n) : P.kernel * numberKernel j * P.kernel = mu j • P.kernel := hc j
  refine ⟨fun j => (mu j).re, fun j => ?_⟩
  have hh := congrArg star (hmu j)
  simp only [star_mul, star_smul, P.hermitian, numberKernel_star] at hh
  have hs : star (mu j) • P.kernel = mu j • P.kernel := by
    rw [← hh]
    simpa only [Matrix.mul_assoc] using hmu j
  have hr : ((mu j).re : ℂ) = (mu j + star (mu j)) / 2 := by
    apply Complex.ext <;> simp
  rw [hmu, hr]
  calc
    mu j • P.kernel = (2 : ℂ)⁻¹ •
        (mu j • P.kernel + star (mu j) • P.kernel) := by rw [hs]; module
    _ = _ := by rw [← add_smul, smul_smul]; congr 1; ring

theorem detected_connected_component_le_kernel (P : CodeProjector n)
    (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel) :
    Subgroup.connectedComponentOfOne (stabilizerSubgroup P) ≤ (logicalHom P).ker := by
  intro u hu
  obtain ⟨z, hz⟩ := MainTheory.PhysicalRelativeAction.connected_component_scalar_exists
    P μ hμ u hu
  exact logicalHom_eq_one_of_scalar P u z hz

def detectedComponentFactor (P : CodeProjector n) (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel) :
    ((stabilizerSubgroup P) ⧸ Subgroup.connectedComponentOfOne (stabilizerSubgroup P)) →*
      IntrinsicProjectiveDiagonalLogicalGroup P :=
  QuotientGroup.lift _ (logicalHom P) (detected_connected_component_le_kernel P μ hμ)

theorem detectedComponentFactor_mk (P : CodeProjector n) (μ : Fin n → ℂ)
    (hμ : ∀ j, P.kernel * numberKernel j * P.kernel = μ j • P.kernel)
    (u : stabilizerSubgroup P) :
    detectedComponentFactor P μ hμ (QuotientGroup.mk u) = logicalHom P u := rfl

theorem z_detected_one_parameter_real_scalar (P : CodeProjector n)
    (lam : Fin n → ℂ)
    (hz : ∀ j, P.kernel *
      MainTheory.PauliKernelTrace.pauliKernel (MainTheory.NumberOperator.zPauli j) *
      P.kernel = lam j • P.kernel) (h : Fin n → ℝ)
    (hp : ∀ t : ℝ, expAngles (t • h) ∈ stabilizerSubgroup P) :
    ∃ μ : Fin n → ℝ, ∀ t : ℝ,
      operator (expAngles (t • h)) * P.kernel =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) *
          ((∑ j, h j * μ j : ℝ) : ℂ)) • P.kernel := by
  obtain ⟨μ, hμ⟩ := number_compression_of_z_detection P lam hz
  refine ⟨μ, fun t => ?_⟩
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul] using
    one_parameter_scalar P h (fun j => (μ j : ℂ)) hμ hp t

end

end MainTheory.PhysicalComponentFactor
