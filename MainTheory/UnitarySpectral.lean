import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The spectral theorem for unitary operators

Mathlib proves the finite-dimensional spectral theorem for *self-adjoint*
operators, but not for unitary or normal ones.  Section II of the paper needs
the unitary case: a diagonal product operation preserving a code restricts to
a unitary on that code, and the whole classification starts from its
eigen-decomposition.

This file supplies it, following the same skeleton as
`Analysis/InnerProductSpace/Spectrum.lean` with three substitutions.  The one
place where the argument genuinely diverges is the final step: the self-adjoint
proof uses the Rayleigh quotient to produce an eigenvalue, which is not
available here, so we use algebraic closedness of the complex numbers instead.
-/

namespace MainTheory.UnitarySpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

open scoped ComplexConjugate
open Module.End

/-- An operator preserving the inner product. -/
def IsUnitaryOn (T : E →ₗ[ℂ] E) : Prop :=
  ∀ x y : E, ⟪ T x, T y ⟫ = ⟪ x, y ⟫

variable {T : E →ₗ[ℂ] E}

/-- **Eigenvalues of a unitary operator lie on the unit circle.** -/
theorem conj_mul_eigenvalue (hT : IsUnitaryOn T) {mu : ℂ}
    (hmu : HasEigenvalue T mu) : conj mu * mu = 1 := by
  obtain ⟨v, hv1, hv2⟩ := hmu.exists_hasEigenvector
  rw [mem_eigenspace_iff] at hv1
  have hself : ⟪ v, v ⟫ ≠ 0 := inner_self_ne_zero.2 hv2
  have h := hT v v
  rw [hv1, inner_smul_left, inner_smul_right] at h
  have h' : (conj mu * mu - 1) * ⟪v, v⟫ = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact sub_eq_zero.mp h''
  · exact absurd h'' hself

/-- Eigenvalues of a unitary operator are nonzero. -/
theorem eigenvalue_ne_zero (hT : IsUnitaryOn T) {mu : ℂ}
    (hmu : HasEigenvalue T mu) : mu ≠ 0 := by
  intro h
  have := conj_mul_eigenvalue hT hmu
  rw [h, mul_zero] at this
  exact zero_ne_one this

/-- **Eigenspaces of a unitary operator for distinct eigenvalues are
orthogonal.** -/
theorem orthogonalFamily_eigenspaces (hT : IsUnitaryOn T) :
    OrthogonalFamily ℂ (fun mu => eigenspace T mu)
      fun mu => (eigenspace T mu).subtypeₗᵢ := by
  rintro mu nu hmn ⟨v, hv⟩ ⟨w, hw⟩
  by_cases hv0 : v = 0
  · simp [hv0]
  have hmu : conj mu * mu = 1 :=
    conj_mul_eigenvalue hT (hasEigenvalue_of_hasEigenvector ⟨hv, hv0⟩)
  rw [mem_eigenspace_iff] at hv hw
  have h := hT v w
  rw [hv, hw, inner_smul_left, inner_smul_right] at h
  have h' : (conj mu * nu - 1) * ⟪ v, w ⟫ = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h'' | h''
  · exfalso
    apply hmn
    have hcm : conj mu * nu = 1 := sub_eq_zero.mp h''
    have : mu * (conj mu * nu) = mu * 1 := by rw [hcm]
    rw [← mul_assoc, mul_comm mu (conj mu), hmu, one_mul, mul_one] at this
    exact this.symm
  · exact h''

theorem orthogonalFamily_eigenspaces' (hT : IsUnitaryOn T) :
    OrthogonalFamily ℂ (fun mu : Eigenvalues T => eigenspace T mu)
      fun mu => (eigenspace T mu).subtypeₗᵢ :=
  (orthogonalFamily_eigenspaces hT).comp Subtype.coe_injective

/-- **A unitary operator preserves orthogonal complements of its
eigenspaces.** -/
theorem invariant_orthogonalComplement_eigenspace (hT : IsUnitaryOn T)
    (mu : ℂ) (v : E) (hv : v ∈ (eigenspace T mu)ᗮ) :
    T v ∈ (eigenspace T mu)ᗮ := by
  intro w hw
  by_cases hmu : eigenspace T mu = ⊥
  · rw [hmu] at hw
    simp only [Submodule.mem_bot] at hw
    simp [hw]
  have hev : HasEigenvalue T mu := by
    rw [HasEigenvalue]
    exact hmu
  have hne := eigenvalue_ne_zero hT hev
  have hTw : T w = mu • w := by rwa [mem_eigenspace_iff] at hw
  have hkey : T (mu⁻¹ • w) = w := by
    rw [map_smul, hTw, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have := hT (mu⁻¹ • w) v
  rw [hkey] at this
  rw [this, inner_smul_left, hv w hw, mul_zero]

/-- The mutual orthogonal complement of all eigenspaces is invariant. -/
theorem orthogonalComplement_iSup_eigenspaces_invariant (hT : IsUnitaryOn T)
    ⦃v : E⦄ (hv : v ∈ (⨆ mu, eigenspace T mu)ᗮ) :
    T v ∈ (⨆ mu, eigenspace T mu)ᗮ := by
  rw [← Submodule.iInf_orthogonal] at hv ⊢
  exact T.iInf_invariant (invariant_orthogonalComplement_eigenspace hT) v hv

/-- On that complement the operator has no eigenvalue at all. -/
theorem orthogonalComplement_iSup_eigenspaces (hT : IsUnitaryOn T) (mu : ℂ) :
    eigenspace (T.restrict
      (orthogonalComplement_iSup_eigenspaces_invariant hT)) mu = ⊥ := by
  refine eigenspace_restrict_eq_bot
    (orthogonalComplement_iSup_eigenspaces_invariant hT) ?_
  have h : eigenspace T mu ⟂ (⨆ mu, eigenspace T mu)ᗮ :=
    (Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ _)
  exact h.disjoint

variable [FiniteDimensional ℂ E]

/-- **The eigenspaces of a unitary operator span.**

This is where the self-adjoint proof cannot be copied: it produces an
eigenvalue from the Rayleigh quotient, which needs symmetry.  Over the complex
numbers algebraic closedness produces one instead. -/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot (hT : IsUnitaryOn T) :
    (⨆ mu, eigenspace T mu)ᗮ = ⊥ := by
  set W : Submodule ℂ E := (⨆ mu, eigenspace T mu)ᗮ with hW
  by_contra hne
  have hnt : Nontrivial W := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hne
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue
    (T.restrict (orthogonalComplement_iSup_eigenspaces_invariant hT))
  have := orthogonalComplement_iSup_eigenspaces hT c
  rw [HasEigenvalue] at hc
  exact hc this

theorem orthogonalComplement_iSup_eigenspaces_eq_bot' (hT : IsUnitaryOn T) :
    (⨆ mu : Eigenvalues T, eigenspace T mu)ᗮ = ⊥ :=
  show (⨆ mu : { mu // eigenspace T mu ≠ ⊥ }, eigenspace T mu)ᗮ = ⊥ by
    rw [iSup_ne_bot_subtype, orthogonalComplement_iSup_eigenspaces_eq_bot hT]

/-- **The spectral theorem for unitary operators**: a finite-dimensional
complex inner product space is the internal orthogonal direct sum of the
eigenspaces of any unitary operator on it. -/
theorem directSum_isInternal (hT : IsUnitaryOn T) :
    DirectSum.IsInternal fun mu : Eigenvalues T => eigenspace T mu :=
  (orthogonalFamily_eigenspaces' hT).isInternal_iff.mpr
    (orthogonalComplement_iSup_eigenspaces_eq_bot' hT)

end MainTheory.UnitarySpectral
