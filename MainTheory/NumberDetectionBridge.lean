import QECC.Basic

namespace MainTheory.NumberDetectionBridge

noncomputable section
variable {n K : ℕ}

theorem single_site_iff (C : QECC.CodeProjector n K) (j : Fin n) (lam : ℂ) :
    C.proj * QECC.zOp j * C.proj = lam • C.proj ↔
      C.proj * QECC.numberOp j * C.proj = ((1 - lam) / 2) • C.proj := by
  have h : C.proj * QECC.zOp j * C.proj =
      C.proj - (2 : ℂ) • (C.proj * QECC.numberOp j * C.proj) := by
    rw [QECC.CodeProjector.zOp_eq_one_sub_two_numberOp]
    simp [Matrix.mul_sub, Matrix.sub_mul, C.idempotent, Matrix.mul_assoc]
  rw [h]
  constructor
  · intro hz
    ext x y
    have he := congrFun (congrFun hz x) y
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at he ⊢
    linear_combination (-1 / 2 : ℂ) * he
  · intro hn
    rw [hn]
    ext x y
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem all_sites_iff (C : QECC.CodeProjector n K) :
    C.DetectsSingleZ ↔ C.DetectsNumberOps := by
  constructor
  · exact C.detectsNumberOps_of_detectsSingleZ
  · rintro ⟨mu, hmu⟩
    refine ⟨fun j => 1 - 2 * mu j, fun j => ?_⟩
    apply (single_site_iff C j _).mpr
    have hc : ((1 : ℂ) - ((1 - 2 * mu j : ℝ) : ℂ)) / 2 = (mu j : ℂ) := by
      push_cast
      ring
    rw [hc]
    exact hmu j

end
end MainTheory.NumberDetectionBridge
