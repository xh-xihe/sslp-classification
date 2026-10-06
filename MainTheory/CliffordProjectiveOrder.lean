import MainTheory.QuaternionCliffordTrace
import MainTheory.QuaternionProjectiveSurjectivity

/-! Literal single-qubit Clifford matrices have projective order at most four. -/

namespace MainTheory.CliffordProjectiveOrder

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisFrames
  MainTheory.QuaternionCliffordAxes MainTheory.QuaternionAxisGeometry
  MainTheory.QuaternionProjectiveOrders MainTheory.QuaternionCliffordMatrixBridge
  MainTheory.UnitaryAdjointRepresentation

theorem zero_im_adjoint (q : unitary ℍ[ℝ])
    (hi : q.val.imI=0) (hj : q.val.imJ=0) (hk : q.val.imK=0) :
    adjoint (unitarySpin q)=1 := by
  apply (adjoint_eq_one_iff _).mpr
  exact (scalar_spin_iff q.val).2 ⟨hi,hj,hk⟩

theorem allowed_short_power (q : unitary ℍ[ℝ]) (hq : AllowedScalar q.val.re) :
    ∃ m : ℕ,0 < m ∧ m ≤ 4 ∧ adjoint (unitarySpin q)^m=1 := by
  have hn := normSq_unitary q
  simp only [Quaternion.normSq_def'] at hn
  rcases hq with ha | ha | ha | ha
  · refine ⟨1,by norm_num,by norm_num,?_⟩
    rw [pow_one]
    apply zero_im_adjoint <;> nlinarith [sq_nonneg q.val.imI,sq_nonneg q.val.imJ,sq_nonneg q.val.imK]
  · refine ⟨2,by norm_num,by norm_num,?_⟩
    rw [← map_pow,← map_pow]
    obtain ⟨hi,hj,hk⟩ := square_im q.val
    apply zero_im_adjoint
    · change (q.val^2).imI=0; simp_all
    · change (q.val^2).imJ=0; simp_all
    · change (q.val^2).imK=0; simp_all
  · refine ⟨3,by norm_num,by norm_num,?_⟩
    rw [← map_pow,← map_pow]
    obtain ⟨hi,hj,hk⟩ := cube_im q
    apply zero_im_adjoint
    · change (q.val^3).imI=0; simp_all
    · change (q.val^3).imJ=0; simp_all
    · change (q.val^3).imK=0; simp_all
  · refine ⟨4,by norm_num,by norm_num,?_⟩
    rw [← map_pow,← map_pow]
    obtain ⟨hi,hj,hk⟩ := fourth_im q
    apply zero_im_adjoint
    · change (q.val^4).imI=0; simp_all
    · change (q.val^4).imJ=0; simp_all
    · change (q.val^4).imK=0; simp_all

theorem clifford_normalizes (q : unitary ℍ[ℝ]) (hq : IsClifford (unitarySpin q)) :
    Normalizes q := by
  have hc (p : Fin 3) : CoordinateAxis (conjugate q (axis p)) := by
    obtain ⟨r,hr⟩ := hq p
    rcases hr with hr | hr
    · have he : conjugate q (axis p)=axis r := by
        apply Subtype.ext
        apply spin_injective
        rw [spin_conjugate,spin_axis,Matrix.mul_smul,Matrix.smul_mul,spin_axis]
        exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => Complex.I • M) hr
      rw [he]
      fin_cases r <;> simp [axis,CoordinateAxis]
    · have he : conjugate q (axis p)= -axis r := by
        apply Subtype.ext
        apply spin_injective
        change spin (conjugate q (axis p)).val=spin (-(axis r).val)
        rw [spin_conjugate,spin_axis,spin_negative,spin_axis,
          Matrix.mul_smul,Matrix.smul_mul,← smul_neg]
        exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => Complex.I • M) hr
      rw [he]
      fin_cases r <;> simp [axis,CoordinateAxis]
  exact ⟨hc 2,hc 1,hc 0⟩

theorem bounded_order (U : Matrix.unitaryGroup (Fin 2) ℂ) (hU : IsClifford U) :
    0<orderOf (adjoint U) ∧ orderOf (adjoint U)≤4 := by
  obtain ⟨q,hq⟩ := MainTheory.QuaternionProjectiveSurjectivity.adjoint_surjective U
  have hc := clifford_of_same_adjoint U (unitarySpin q) hq.symm hU
  obtain ⟨m,hmp,hmb,hm⟩ := allowed_short_power q
    (MainTheory.QuaternionCliffordTrace.allowed_trace q (clifford_normalizes q hc))
  rw [hq] at hm
  have hd := orderOf_dvd_of_pow_eq_one hm
  have hp : 0<orderOf (adjoint U) := by
    by_contra hn
    have hz : orderOf (adjoint U)=0 := by omega
    rw [hz,zero_dvd_iff] at hd
    omega
  exact ⟨hp,(Nat.le_of_dvd hmp hd).trans hmb⟩

theorem order_five_not_clifford (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (hU : orderOf (adjoint U)=5) : ¬IsClifford U := by
  intro hc
  have hb := (bounded_order U hc).2
  omega

theorem conjugate_order (B U : Matrix.unitaryGroup (Fin 2) ℂ) :
    orderOf (adjoint U)=orderOf (adjoint (B*U*B⁻¹)) := by
  apply SemiconjBy.orderOf_eq (adjoint B)
  unfold SemiconjBy
  simp [map_mul,map_inv,mul_assoc]

theorem order_five_no_clifford_basis (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (hU : orderOf (adjoint U)=5) (B : Matrix.unitaryGroup (Fin 2) ℂ) :
    ¬IsClifford (B*U*B⁻¹) := by
  exact order_five_not_clifford _ ((conjugate_order B U).symm.trans hU)

end

end MainTheory.CliffordProjectiveOrder
