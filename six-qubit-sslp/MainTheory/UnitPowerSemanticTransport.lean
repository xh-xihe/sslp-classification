import MainTheory.D3BoundedOuterRecord

/-!
# Semantic transport through a coprime unit power

Multiplying a finite angle vector by `u : (ZMod q)ˣ` replaces its diagonal
gate by the natural power indexed by the canonical representative of `u`.
This file proves that statement pointwise, transports eigenstates and exact SS
fibres, and rebuilds `FiniteGeneratorResolution` on the unchanged exact code.

This is only the coprime unit-power step.  No local-`X` conjugation or physical
coordinate permutation is folded into the construction.
-/

namespace MainTheory.UnitPowerSemanticTransport

open MainTheory

noncomputable section

/-- Canonical natural exponent represented by a unit modulo `q`. -/
def unitExponent {q : ℕ} (u : (ZMod q)ˣ) : ℕ :=
  (u : ZMod q).val

/-- The diagonal entry of the unit-scaled angle is the corresponding power of
the old diagonal entry. -/
theorem diag_unit_mul {n q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (u : (ZMod q)ˣ) (a : Fin n → ZMod q) (s : SS.BitString n) :
    Gate.diag zeta (fun j ↦ (u : ZMod q) * a j) s =
      Gate.diag zeta a s ^ unitExponent u := by
  calc
    Gate.diag zeta (fun j ↦ (u : ZMod q) * a j) s =
        Cyclic.chi zeta
          (SS.weight (fun j ↦ (u : ZMod q) * a j) s) := rfl
    _ = Cyclic.chi zeta ((u : ZMod q) * SS.weight a s) := by
      rw [RankTwoGlobal.weight_unit_mul]
    _ = Cyclic.chi zeta (unitExponent u • SS.weight a s) := by
      congr 2
      unfold unitExponent
      rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]
    _ = Cyclic.chi zeta (SS.weight a s) ^ unitExponent u :=
      (Cyclic.chi_pow zeta hzeta (SS.weight a s) (unitExponent u)).symm
    _ = Gate.diag zeta a s ^ unitExponent u := rfl

/-- An eigenstate for the original finite gate remains an eigenstate after a
unit power, with its eigenvalue raised to the same exponent. -/
theorem gate_unit_mul_eigen {n q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (u : (ZMod q)ˣ) (a : Fin n → ZMod q)
    (psi : SS.State n ℂ) (lambda : ℂ)
    (heigen : Gate.gate zeta a psi = fun s ↦ lambda * psi s) :
    Gate.gate zeta (fun j ↦ (u : ZMod q) * a j) psi =
      fun s ↦ lambda ^ unitExponent u * psi s := by
  funext s
  unfold Gate.gate
  rw [diag_unit_mul zeta hzeta]
  by_cases hs : psi s = 0
  · simp [hs]
  · have hpoint := congrFun heigen s
    unfold Gate.gate at hpoint
    have hdiag : Gate.diag zeta a s = lambda :=
      mul_right_cancel₀ hs hpoint
    rw [hdiag]

/-- Forward transport of an exact SS fibre under unit scaling. -/
theorem ssConditionState_unitPower {n q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (a : Fin n → ZMod q) (r : ZMod q)
    (psi : SS.State n ℂ) (h : SS.SSConditionState a r psi) :
    SS.SSConditionState (fun j ↦ (u : ZMod q) * a j)
      ((u : ZMod q) * r) psi :=
  RankTwoGlobal.ssConditionState_unit_mul u a r psi h

/-- Every vector of a stored orthonormal frame has an actual nonzero
amplitude. -/
private theorem exists_frame_amplitude_ne_zero {n : ℕ}
    (F : CodeSpec.OrthonormalFrame n 2) (k : Fin 2) :
    ∃ s, F.vec k s ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : F.vec k = 0 := funext h
  have hself := F.orthonormal k k
  rw [hz] at hself
  simp [SS.innerC] at hself

/-- A unit power cannot collapse the two distinct logical eigenvalues of a
finite generator. -/
theorem eigenvalue_unitPower_ne
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (u : (ZMod q)ˣ) :
    G.eigenvalue 0 ^ unitExponent u ≠
      G.eigenvalue 1 ^ unitExponent u := by
  obtain ⟨s0, hs0⟩ := exists_frame_amplitude_ne_zero G.eigenFrame 0
  obtain ⟨s1, hs1⟩ := exists_frame_amplitude_ne_zero G.eigenFrame 1
  have hvalue0 : G.eigenvalue 0 = Gate.diag G.zeta G.angle s0 := by
    have hpoint := congrFun (G.eigen 0) s0
    unfold Gate.gate at hpoint
    exact (mul_right_cancel₀ hs0 hpoint).symm
  have hvalue1 : G.eigenvalue 1 = Gate.diag G.zeta G.angle s1 := by
    have hpoint := congrFun (G.eigen 1) s1
    unfold Gate.gate at hpoint
    exact (mul_right_cancel₀ hs1 hpoint).symm
  intro hpow
  rw [hvalue0, hvalue1, Cyclic.diag_eq_chi, Cyclic.diag_eq_chi,
    Cyclic.chi_pow G.zeta G.primitiveRoot
      (SS.weight G.angle s0) (unitExponent u),
    Cyclic.chi_pow G.zeta G.primitiveRoot
      (SS.weight G.angle s1) (unitExponent u)] at hpow
  have hscaled := Cyclic.chi_injective G.zeta G.primitiveRoot hpow
  have hunitScaled :
      (u : ZMod q) * SS.weight G.angle s0 =
        (u : ZMod q) * SS.weight G.angle s1 := by
    simpa [unitExponent, nsmul_eq_mul, ZMod.natCast_val,
      ZMod.cast_id] using hscaled
  have hcancel := congrArg
    (fun z : ZMod q ↦ ((↑(u⁻¹) : ZMod q) * z)) hunitScaled
  have hweight : SS.weight G.angle s0 = SS.weight G.angle s1 := by
    simpa [mul_assoc] using hcancel
  apply G.projectively_nontrivial
  rw [hvalue0, hvalue1, Cyclic.diag_eq_chi, Cyclic.diag_eq_chi, hweight]

/-- Rebuild the complete finite-generator resolution after replacing the
generator by a coprime unit power.  The exact code and eigenframe are
unchanged; the angle and logical eigenvalues carry the power. -/
def unitPowerFiniteGeneratorResolution
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (u : (ZMod q)ˣ) : RankTwoGlobal.FiniteGeneratorResolution C q where
  zeta := G.zeta
  primitiveRoot := G.primitiveRoot
  angle := fun j ↦ (u : ZMod q) * G.angle j
  primitive := D3BoundedOuterRecord.primitive_unit_mul u G.angle G.primitive
  eigenFrame := G.eigenFrame
  span_eq := G.span_eq
  eigenvalue := fun k ↦ G.eigenvalue k ^ unitExponent u
  eigen := by
    intro k
    exact gate_unit_mul_eigen G.zeta G.primitiveRoot u G.angle
      (G.eigenFrame.vec k) (G.eigenvalue k) (G.eigen k)
  projectively_nontrivial := eigenvalue_unitPower_ne G u

/-- The logical phase ratio of the rebuilt generator is exactly the same
unit power of the old ratio. -/
theorem unitPower_ratio
    {n d q : ℕ} [NeZero q] {C : CodeSpec.ExactCode n 2 d}
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (u : (ZMod q)ˣ) :
    (unitPowerFiniteGeneratorResolution G u).eigenvalue 1 /
        (unitPowerFiniteGeneratorResolution G u).eigenvalue 0 =
      (G.eigenvalue 1 / G.eigenvalue 0) ^ unitExponent u := by
  simp [unitPowerFiniteGeneratorResolution, div_pow]

end

end MainTheory.UnitPowerSemanticTransport
