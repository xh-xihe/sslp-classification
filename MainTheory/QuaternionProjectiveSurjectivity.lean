import MainTheory.QuaternionSpinMatrices

/-! Every actual U(2) matrix is a spin matrix up to a unit scalar. -/

namespace MainTheory.QuaternionProjectiveSurjectivity

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices
open scoped ComplexConjugate

theorem special_entries (W : Matrix.unitaryGroup (Fin 2) ℂ) (hdet : W.val.det = 1) :
    W.val 1 1 = conj (W.val 0 0) ∧ W.val 1 0 = -conj (W.val 0 1) := by
  have hAdj : W.val.adjugate = star W.val := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M * star W.val)
      (Matrix.adjugate_mul W.val)
    change (W.val.adjugate * W.val) * star W.val =
      (W.val.det • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * star W.val at he
    rw [Matrix.mul_assoc,W.property.2,Matrix.mul_one,hdet,one_smul,Matrix.one_mul] at he
    exact he
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hAdj
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hAdj
  rw [Matrix.adjugate_fin_two] at h00 h10
  change W.val 1 1 = conj (W.val 0 0) at h00
  change -W.val 1 0 = conj (W.val 0 1) at h10
  exact ⟨h00,by simpa only [neg_neg] using congrArg Neg.neg h10⟩

theorem special_is_spin (W : Matrix.unitaryGroup (Fin 2) ℂ) (hdet : W.val.det = 1) :
    ∃ q : unitary ℍ[ℝ], (unitarySpin q).val = W.val := by
  let q : ℍ[ℝ] := ⟨(W.val 0 0).re,(W.val 0 0).im,(W.val 0 1).re,(W.val 0 1).im⟩
  obtain ⟨h11,h10⟩ := special_entries W hdet
  have he : spin q = W.val := by
    ext i j
    fin_cases i <;> fin_cases j
    · apply Complex.ext <;> simp [spin,q]
    · apply Complex.ext <;> simp [spin,q]
    · change spin q 1 0 = W.val 1 0
      rw [h10]
      apply Complex.ext <;> simp [spin,q]
    · change spin q 1 1 = W.val 1 1
      rw [h11]
      apply Complex.ext <;> simp [spin,q]
  have hq : q ∈ unitary ℍ[ℝ] := by
    constructor
    · apply spin_injective
      rw [spin_mul,spin_star,he,spin_one]
      exact W.property.1
    · apply spin_injective
      rw [spin_mul,spin_star,he,spin_one]
      exact W.property.2
  exact ⟨⟨q,hq⟩,he⟩

theorem scalar_unitary (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ (a : unitary ℂ) (q : unitary ℍ[ℝ]), U.val = (a : ℂ) • (unitarySpin q).val := by
  have hdet := Matrix.det_of_mem_unitary U.property
  have hd : Complex.normSq U.val.det = 1 := by
    have he := congrArg Complex.re hdet.1
    simpa [Complex.normSq_apply,Complex.mul_re] using he
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq U.val.det (by decide : 0 < (2 : ℕ))
  have hna : Complex.normSq a = 1 := by
    have he := congrArg Complex.normSq ha
    rw [map_pow,hd] at he
    nlinarith [Complex.normSq_nonneg a]
  have hmem : a ∈ unitary ℂ := by
    apply Unitary.mem_iff_star_mul_self.mpr
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.normSq_apply] at hna ⊢
    · linarith
    · ring
  let au : unitary ℂ := ⟨a,hmem⟩
  let W : Matrix (Fin 2) (Fin 2) ℂ := (au⁻¹ : unitary ℂ).val • U.val
  have hW : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    constructor <;>
      simp only [W,StarModule.star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    · rw [U.property.1,(au⁻¹).property.2,one_smul]
    · rw [U.property.2,(au⁻¹).property.1,one_smul]
  have hWd : W.det = 1 := by
    change ((au⁻¹ : unitary ℂ).val • U.val).det = 1
    rw [Matrix.det_smul,Unitary.coe_inv]
    change (a⁻¹)^2 * U.val.det = 1
    rw [← ha,← mul_pow]
    have hne : a ≠ 0 := by intro hz; simp [hz] at hna
    rw [inv_mul_cancel₀ hne,one_pow]
  obtain ⟨q,hq⟩ := special_is_spin ⟨W,hW⟩ hWd
  refine ⟨au,q,?_⟩
  rw [hq]
  change U.val = a • ((au⁻¹ : unitary ℂ).val • U.val)
  rw [Unitary.coe_inv]
  change U.val = a • ((a⁻¹) • U.val)
  rw [smul_smul]
  have hne : a ≠ 0 := by intro hz; simp [hz] at hna
  rw [mul_inv_cancel₀ hne,one_smul]

theorem adjoint_surjective (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ q : unitary ℍ[ℝ], UnitaryAdjointRepresentation.adjoint (unitarySpin q) =
      UnitaryAdjointRepresentation.adjoint U := by
  obtain ⟨a,q,hq⟩ := scalar_unitary U
  exact ⟨q,((UnitaryAdjointRepresentation.adjoint_eq_iff U (unitarySpin q)).2 ⟨a,hq⟩).symm⟩

end

end MainTheory.QuaternionProjectiveSurjectivity
