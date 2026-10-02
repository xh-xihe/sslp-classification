import QECC.ReducedRepresentative
import QECC.UniformRepresentative

/-!
The formalization of Section III.A is split into reusable layers:

* `Basic` defines code projectors and the single-site `Z` and number-operator
  detection conditions;
* `FiniteDiagonal` models local phases in `R/Z`, diagonal product gates, code
  preservation, scalar actions, and the projective diagonal logical group. It
  also proves that every exact real edge-kernel direction acts as a logical
  scalar under number-operator detection;
* `RationalSection` proves a uniform rational-section theorem for arbitrary
  integer matrices by choosing a rational generalized inverse of `Aᵀ A` and
  clearing its denominators;
* `UniformRepresentative` applies that theorem to the projector edge matrix,
  producing one code-dependent denominator that represents every preserving
  phase modulo scalar actions;
* `ReducedRepresentative` converts any nonzero finite-order phase vector to a
  primitive residue vector modulo its exact order and proves that the
  corresponding physical gate has that exact order;
* this file proves finiteness of the projective group, constructs reduced
  representatives, and packages the complete Section III.A theorem in
  `finite_diagonal_logical_group_and_physical_representatives`.
-/

namespace QECC

noncomputable section

/-- Multiplying a rational phase vector by its denominator gives zero in the torus. -/
theorem rationalPhase_nsmul {n q : ℕ} (hq : 0 < q) (a : Fin n → ℤ) :
    q • rationalPhase q a = 0 := by
  funext j
  change q • (((a j : ℝ) / (q : ℝ) : ℝ) : LocalPhase) = 0
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul, mul_div_cancel₀]
  · exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨a j, by simp⟩
  · exact_mod_cast hq.ne'

/-- Rational phase vectors have finite physical order. -/
theorem rationalPhase_isOfFinAddOrder {n q : ℕ} (hq : 0 < q) (a : Fin n → ℤ) :
    IsOfFinAddOrder (rationalPhase q a) := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  exact ⟨q, hq, rationalPhase_nsmul hq a⟩

/-- Reducing integer numerators modulo `q` does not change their circle phases. -/
theorem rationalPhase_eq_phaseHom {n q : ℕ} (hq : 0 < q) (a : Fin n → ℤ) :
    rationalPhase q a = phaseHom n q hq (fun j => (a j : ZMod q)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  funext j
  change (((a j : ℝ) / (q : ℝ) : ℝ) : LocalPhase) =
    ZMod.toAddCircle (a j : ZMod q)
  rw [ZMod.toAddCircle_intCast]

namespace CodeProjector

variable {n K : ℕ} (C : CodeProjector n K)

/-- Send a preserving physical phase to its projective logical class. -/
def projectiveClassMap : C.preservingPhases →+ C.ProjectiveDiagonalGroup :=
  QuotientAddGroup.mk' C.scalarPhases

/-- Two preserving gates define the same formal projective class exactly when their
restrictions to the code differ by one common phase. -/
theorem projectiveClass_eq_iff_gate_restrictions
    (theta phi : PhaseVector n) (htheta : C.Preserves theta) (hphi : C.Preserves phi) :
    C.projectiveClassMap ⟨theta, htheta⟩ = C.projectiveClassMap ⟨phi, hphi⟩ ↔
      ∃ c : LocalPhase, diagonalGate theta * C.proj =
        ((c.toCircle : Circle) : ℂ) • (diagonalGate phi * C.proj) := by
  constructor
  · intro hclass
    have hscalar := QuotientAddGroup.eq_iff_sub_mem.mp hclass
    change C.ActsAsScalar (theta - phi) at hscalar
    obtain ⟨c, hc⟩ := hscalar
    refine ⟨c, ?_⟩
    classical
    ext x y
    by_cases hxy : C.proj x y = 0
    · simp [diagonalGate, hxy]
    · have hphase : supportPhase theta x = c + supportPhase phi x := by
        rw [← sub_eq_iff_eq_add]
        simpa [sub_eq_add_neg] using hc x y hxy
      simp only [diagonalGate, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
      rw [hphase, AddCircle.toCircle_add]
      change ((c.toCircle : Circle) : ℂ) *
        (((supportPhase phi x).toCircle : Circle) : ℂ) * C.proj x y =
        ((c.toCircle : Circle) : ℂ) *
          ((((supportPhase phi x).toCircle : Circle) : ℂ) * C.proj x y)
      rw [mul_assoc]
  · rintro ⟨c, hgate⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change C.ActsAsScalar (theta - phi)
    refine ⟨c, fun x y hxy => ?_⟩
    have hentry := congrFun (congrFun hgate x) y
    simp only [diagonalGate, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at hentry
    rw [← mul_assoc] at hentry
    have hccomplex : (((supportPhase theta x).toCircle : Circle) : ℂ) =
        ((c.toCircle : Circle) : ℂ) *
          (((supportPhase phi x).toCircle : Circle) : ℂ) :=
      mul_right_cancel₀ hxy hentry
    have hcircle : (supportPhase theta x).toCircle =
        (c + supportPhase phi x).toCircle := by
      apply Subtype.coe_injective
      simpa [AddCircle.toCircle_add] using hccomplex
    have hphase : supportPhase theta x = c + supportPhase phi x :=
      AddCircle.injective_toCircle one_ne_zero hcircle
    rw [sub_eq_add_neg, supportPhase_add, supportPhase_neg, hphase]
    abel

/-- Residue vectors modulo `q` whose physical diagonal gates preserve the code. -/
def ModularPreserving (q : ℕ) (hq : 0 < q) :=
  {a : Fin n → ZMod q // C.Preserves (phaseHom n q hq a)}

/-- A preserving residue vector determines a projective logical class. -/
def modularClassMap (q : ℕ) (hq : 0 < q) :
    C.ModularPreserving q hq → C.ProjectiveDiagonalGroup :=
  fun a => C.projectiveClassMap ⟨phaseHom n q hq a.1, a.2⟩

/-- A common denominator for representatives makes the projective logical group finite. -/
theorem projectiveDiagonalGroup_finite_of_uniform (Q : ℕ) (hQ : 0 < Q)
    (huniform : ∀ theta : PhaseVector n, C.Preserves theta →
      ∃ a : Fin n → ℤ, C.Preserves (rationalPhase Q a) ∧
        C.ActsAsScalar (theta - rationalPhase Q a)) :
    Finite C.ProjectiveDiagonalGroup := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  letI : Finite (C.ModularPreserving Q hQ) := by
    dsimp [ModularPreserving]
    infer_instance
  apply Finite.of_surjective (C.modularClassMap Q hQ)
  intro U
  obtain ⟨theta, rfl⟩ :=
    (QuotientAddGroup.mk'_surjective C.scalarPhases) U
  obtain ⟨a, ha_preserves, ha_scalar⟩ := huniform theta.1 theta.2
  have heq : rationalPhase Q a =
      phaseHom n Q hQ (fun j => (a j : ZMod Q)) :=
    rationalPhase_eq_phaseHom hQ a
  let aMod : C.ModularPreserving Q hQ :=
    ⟨fun j => (a j : ZMod Q), heq ▸ ha_preserves⟩
  refine ⟨aMod, ?_⟩
  symm
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change C.ActsAsScalar
    (theta.1 - phaseHom n Q hQ (fun j => (a j : ZMod Q)))
  rw [← heq]
  exact ha_scalar

/-- Single-site number detection implies finiteness of the projective diagonal group. -/
theorem projectiveDiagonalGroup_finite (hdetect : C.DetectsNumberOps) :
    Finite C.ProjectiveDiagonalGroup := by
  obtain ⟨Q, hQ, huniform⟩ :=
    C.exists_uniform_rationalPhase_representative hdetect
  exact C.projectiveDiagonalGroup_finite_of_uniform Q hQ huniform

/-- Every nonzero projective class has a reduced physical representative, and its
projective order divides the exact physical order. -/
theorem exists_reduced_representative (hdetect : C.DetectsNumberOps)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    ∃ R : ReducedDiagonalRepresentative n,
      ∃ hRpreserves : C.Preserves R.phase,
        C.projectiveClassMap ⟨R.phase, hRpreserves⟩ = U ∧
        R.commonGCD = 1 ∧
        orderOf (diagonalGate R.phase) = R.q ∧
        addOrderOf U ∣ R.q := by
  obtain ⟨Q, hQ, huniform⟩ :=
    C.exists_uniform_rationalPhase_representative hdetect
  obtain ⟨theta, hthetaU⟩ :=
    (QuotientAddGroup.mk'_surjective C.scalarPhases) U
  obtain ⟨a, ha_preserves, ha_scalar⟩ := huniform theta.1 theta.2
  let rat := rationalPhase Q a
  have hrat_finite : IsOfFinAddOrder rat := rationalPhase_isOfFinAddOrder hQ a
  have hrat_ne : rat ≠ 0 := by
    intro hzero
    apply hU
    rw [← hthetaU]
    apply (QuotientAddGroup.eq_zero_iff theta).2
    change C.ActsAsScalar theta.1
    simpa [rat, hzero] using ha_scalar
  obtain ⟨R, hR⟩ :=
    exists_reducedDiagonalRepresentative rat hrat_finite hrat_ne
  have hRpreserves : C.Preserves R.phase := by
    rw [hR]
    exact ha_preserves
  have hclass : C.projectiveClassMap ⟨R.phase, hRpreserves⟩ = U := by
    rw [← hthetaU]
    symm
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change C.ActsAsScalar (theta.1 - R.phase)
    rw [hR]
    exact ha_scalar
  refine ⟨R, hRpreserves, hclass, R.commonGCD_eq_one, R.orderOf_diagonalGate, ?_⟩
  let rep : C.preservingPhases := ⟨R.phase, hRpreserves⟩
  have hdvd := addOrderOf_map_dvd C.projectiveClassMap rep
  have hmap : C.projectiveClassMap rep = U := by
    simpa [rep] using hclass
  rw [hmap] at hdvd
  have hrepOrder : addOrderOf rep = R.q := by
    have hinj := addOrderOf_injective C.preservingPhases.subtype
      (AddSubgroup.subtype_injective C.preservingPhases) rep
    change addOrderOf R.phase = addOrderOf rep at hinj
    rw [R.addOrderOf_phase] at hinj
    exact hinj.symm
  rwa [hrepOrder] at hdvd

/-- The complete formal conclusion of the first theorem in Section III. -/
structure FiniteDiagonalLogicalGroupConclusion where
  groupFinite : Finite C.ProjectiveDiagonalGroup
  commutes : ∀ U V : C.ProjectiveDiagonalGroup, U + V = V + U
  representative : ∀ U : C.ProjectiveDiagonalGroup, U ≠ 0 →
    ∃ R : ReducedDiagonalRepresentative n,
      ∃ hRpreserves : C.Preserves R.phase,
        C.projectiveClassMap ⟨R.phase, hRpreserves⟩ = U ∧
        R.commonGCD = 1 ∧
        orderOf (diagonalGate R.phase) = R.q ∧
        addOrderOf U ∣ R.q

/-- **Finite diagonal logical group and physical representatives.**

If every single-site Pauli `Z` is detected, the projective logical group induced by
code-preserving diagonal product gates is finite abelian. Every nonidentity class has
a reduced representative `D(a;q)` whose physical matrix has exact order `q`, and the
projective logical order divides `q`. -/
theorem finite_diagonal_logical_group_and_physical_representatives
    (hZ : C.DetectsSingleZ) :
    C.FiniteDiagonalLogicalGroupConclusion := by
  have hdetect := C.detectsNumberOps_of_detectsSingleZ hZ
  exact
    { groupFinite := C.projectiveDiagonalGroup_finite hdetect
      commutes := fun U V => add_comm U V
      representative := fun U hU => C.exists_reduced_representative hdetect U hU }

end CodeProjector

end


end QECC
