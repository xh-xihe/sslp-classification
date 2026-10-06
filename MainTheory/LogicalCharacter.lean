import MainTheory.D3LogicalSecondEigenvector
import MainTheory.IntrinsicAbelian
import MainTheory.SymmetryToEntrance
import MainTheory.D3LogicalPerpSpan
import MainTheory.D3LogicalNormalization
import MainTheory.BoundedRepresentationCertified

/-!
# The logical action as a group homomorphism

`D3LogicalAction.logicalAction F U` is the two-by-two matrix of `U` in the
frame `F`.  On operators that preserve the code it is multiplicative, because
`synthesis_logicalAction` intertwines it with composition and synthesis is
injective.

This is the first step towards the faithful phase-ratio character of
`thm:rank-two-sslp`: it turns the diagonal symmetry group into a group of
two-by-two matrices, where the eigenvalue ratio can be read off.
-/

namespace MainTheory.LogicalCharacter

variable {n d : ℕ}

open MainTheory.ClassificationLevels
open MainTheory.D3LogicalAction

/-- The logical action of a composite is the composite of the logical
actions, provided the inner operator preserves the code. -/
theorem logicalAction_comp (F : CodeSpec.OrthonormalFrame n 2)
    (U V : Module.End ℂ (SS.State n ℂ))
    (hU : CodeSpec.CodePreserving F U) (hV : CodeSpec.CodePreserving F V) :
    logicalAction F (U.comp V)
      = (logicalAction F U).comp (logicalAction F V) := by
  have hUV : CodeSpec.CodePreserving F (U.comp V) := fun phi hphi =>
    hU _ (hV _ hphi)
  refine LinearMap.ext fun v => ?_
  refine synthesis_injective F ?_
  rw [synthesis_logicalAction F _ hUV v]
  simp only [LinearMap.comp_apply]
  rw [synthesis_logicalAction F U hU, synthesis_logicalAction F V hV]

/-! ## Diagonal symmetries as two-by-two matrices -/

variable {C : CodeSpec.ExactCode n 2 d}

/-- A diagonal symmetry preserves the code, in the frame-level sense the
logical action needs. -/
theorem codePreserving_diagonalEnd
    {u : LocalPhase n}
    (hu : u ∈ diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) :
    CodeSpec.CodePreserving C.frame
      (GlobalClassificationBridge.diagonalEnd u) := by
  intro phi hphi
  have := hu.1 phi
    ((GlobalClassificationBridge.inProjectorRange_ofFrame_iff C.frame phi).2 hphi)
  exact (GlobalClassificationBridge.inProjectorRange_ofFrame_iff C.frame _).1 this

/-- The logical action of a product of diagonal symmetries. -/
theorem logicalAction_mul
    {u v : LocalPhase n}
    (hu : u ∈ diagonalSymmetryGroup (CodeProjector.ofFrame C.frame))
    (hv : v ∈ diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) :
    logicalAction C.frame (GlobalClassificationBridge.diagonalEnd (u * v))
      = (logicalAction C.frame (GlobalClassificationBridge.diagonalEnd u)).comp
          (logicalAction C.frame (GlobalClassificationBridge.diagonalEnd v)) := by
  have hcomp : GlobalClassificationBridge.diagonalEnd (u * v)
      = (GlobalClassificationBridge.diagonalEnd u).comp
        (GlobalClassificationBridge.diagonalEnd v) := by
    refine LinearMap.ext fun phi => ?_
    simp only [GlobalClassificationBridge.diagonalEnd, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.comp_apply]
    exact diagonalAction_mul u v phi
  rw [hcomp]
  exact logicalAction_comp C.frame _ _ (codePreserving_diagonalEnd hu)
    (codePreserving_diagonalEnd hv)

/-- The identity acts logically as the identity. -/
@[simp] theorem logicalAction_one (F : CodeSpec.OrthonormalFrame n 2) :
    logicalAction F (GlobalClassificationBridge.diagonalEnd (1 : LocalPhase n))
      = LinearMap.id := by
  have hone : GlobalClassificationBridge.diagonalEnd (1 : LocalPhase n)
      = LinearMap.id := by
    refine LinearMap.ext fun phi => ?_
    simp [GlobalClassificationBridge.diagonalEnd, diagonalAction_one]
  rw [hone]
  refine LinearMap.ext fun v => ?_
  refine synthesis_injective F ?_
  rw [synthesis_logicalAction F LinearMap.id (fun phi hphi => hphi) v]
  simp

/-! ## Projective triviality is scalarity of the logical matrix -/

/-- A projectively trivial symmetry acts on the logical plane by its scalar. -/
theorem logicalAction_eq_smul_of_isProjectivelyTrivial
    {u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)}
    (h : IsProjectivelyTrivial (CodeProjector.ofFrame C.frame) u) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      logicalAction C.frame
          (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n))
        = lam • (LinearMap.id : Module.End ℂ (Fin 2 → ℂ)) := by
  obtain ⟨lam, hlam, hact⟩ := h
  refine ⟨lam, hlam, ?_⟩
  refine LinearMap.ext fun v => ?_
  refine synthesis_injective C.frame ?_
  rw [synthesis_logicalAction C.frame _ (codePreserving_diagonalEnd u.2) v]
  have hmem := synthesis_mem_codeSpan C.frame v
  have := hact (synthesisLinear C.frame v)
    ((GlobalClassificationBridge.inProjectorRange_ofFrame_iff C.frame _).2 hmem)
  simpa [GlobalClassificationBridge.diagonalEnd, map_smul] using this

/-- Conversely, a symmetry whose logical matrix is a nonzero scalar is
projectively trivial.  Together with the previous theorem this identifies the
kernel of the logical representation with the projectively trivial subgroup --
which is exactly what makes the eigenvalue ratio faithful. -/
theorem isProjectivelyTrivial_of_logicalAction_eq_smul
    {u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)}
    {lam : ℂ} (hlam : lam ≠ 0)
    (h : logicalAction C.frame
        (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n))
      = lam • (LinearMap.id : Module.End ℂ (Fin 2 → ℂ))) :
    IsProjectivelyTrivial (CodeProjector.ofFrame C.frame) u := by
  refine ⟨lam, hlam, fun phi hphi => ?_⟩
  have hmem : phi ∈ CodeSpec.codeSpan C.frame :=
    (GlobalClassificationBridge.inProjectorRange_ofFrame_iff C.frame phi).1 hphi
  obtain ⟨v, rfl⟩ : ∃ v, synthesisLinear C.frame v = phi := by
    refine ⟨analysisLinear C.frame phi, ?_⟩
    rw [synthesis_analysis_eq_projectorAction]
    exact (CodeSpec.mem_codeSpan_iff_projectorAction_eq C.frame phi).1 hmem
  have hsyn := synthesis_logicalAction C.frame
    (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n))
    (codePreserving_diagonalEnd u.2) v
  rw [h] at hsyn
  simpa [GlobalClassificationBridge.diagonalEnd, map_smul] using hsyn.symm

/-! ## A commuting operator preserves an eigenline

In two dimensions this needs no spectral theory.  If `M` has two distinct
eigenvalues on `v` and on its perpendicular, then those two vectors are a
basis, and an operator commuting with `M` cannot move the `v`-line: the
component along the perpendicular would have to satisfy `d * nu = d * mu`. -/

open MainTheory.D3LogicalCoordinateUnitary
open MainTheory.D3LogicalPerpSpan

/-- Taking the canonical perpendicular twice negates. -/
@[simp] theorem perpendicular_perpendicular (v : Fin 2 → ℂ) :
    perpendicular (perpendicular v) = -v := by
  funext i
  fin_cases i
  · simp [perpendicular]
  · simp [perpendicular]

theorem coordinateInner_self_ne_zero {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    coordinateInner v v ≠ 0 := by
  rw [D3LogicalNormalization.coordinateInner_self_eq_normSq]
  exact_mod_cast (D3LogicalNormalization.coordinateNormSq_pos hv).ne'

/-- **Every vector of the plane splits along `v` and its perpendicular.** -/
theorem exists_decomposition {v : Fin 2 → ℂ} (hv : v ≠ 0)
    (z : Fin 2 → ℂ) :
    ∃ c d : ℂ, z = c • v + d • perpendicular v := by
  set w := perpendicular v with hw
  have hwne : w ≠ 0 := perpendicular_ne_zero hv
  have hww : coordinateInner w w ≠ 0 := coordinateInner_self_ne_zero hwne
  set d : ℂ := coordinateInner w z / coordinateInner w w with hd
  have hsub : coordinateInner w (z - d • w)
      = coordinateInner w z - d * coordinateInner w w := by
    simp only [coordinateInner, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have horth : coordinateInner w (z - d • w) = 0 := by
    rw [hsub, hd, div_mul_cancel₀ _ hww, sub_self]
  obtain ⟨c, hc⟩ := eq_smul_perpendicular_of_coordinateInner_eq_zero hwne horth
  refine ⟨-c, d, ?_⟩
  have hcv : z - d • w = c • (-v) := by
    rw [hc, hw, perpendicular_perpendicular]
  have : z = c • (-v) + d • w := by
    rw [← hcv]; ring
  rw [this, hw]
  module

/-- **An operator commuting with a two-eigenvalue operator preserves each
eigenline.**

`M` has eigenvalue `mu` on `v` and `nu` on `perpendicular v`, with `mu ≠ nu`.
Any `A` commuting with `M` sends `v` to a multiple of `v`: writing
`A v = c • v + d • perpendicular v` and applying `M` two ways forces
`d * nu = d * mu`. -/
theorem eq_smul_of_commute
    {M A : Module.End ℂ (Fin 2 → ℂ)}
    {v : Fin 2 → ℂ} (hv : v ≠ 0) {mu nu : ℂ} (hmn : mu ≠ nu)
    (hMv : M v = mu • v)
    (hMw : M (perpendicular v) = nu • perpendicular v)
    (hcomm : M.comp A = A.comp M) :
    ∃ a : ℂ, A v = a • v := by
  obtain ⟨c, d, hz⟩ := exists_decomposition hv (A v)
  have hMAv : M (A v) = mu • A v := by
    have := congrArg (fun T : Module.End ℂ (Fin 2 → ℂ) => T v) hcomm
    simp only [LinearMap.comp_apply] at this
    rw [this, hMv, map_smul]
  have hexpand : M (A v) = (c * mu) • v + (d * nu) • perpendicular v := by
    rw [hz, map_add, map_smul, map_smul, hMv, hMw, smul_smul, smul_smul]
  have hexpand2 : mu • A v
      = (c * mu) • v + (d * mu) • perpendicular v := by
    rw [hz, smul_add, smul_smul, smul_smul, mul_comm mu c, mul_comm mu d]
  have hkey : (d * nu) • perpendicular v = (d * mu) • perpendicular v := by
    have h := hexpand.symm.trans (hMAv.trans hexpand2)
    exact add_left_cancel h
  have hd : d = 0 := by
    have hwne : perpendicular v ≠ 0 := perpendicular_ne_zero hv
    have : (d * nu - d * mu) • perpendicular v = 0 := by
      rw [sub_smul, hkey, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · have : d * (nu - mu) = 0 := by rw [mul_sub]; exact h
      rcases mul_eq_zero.mp this with h' | h'
      · exact h'
      · exact absurd (sub_eq_zero.mp h').symm hmn
    · exact absurd h hwne
  exact ⟨c, by rw [hz, hd, zero_smul, add_zero]⟩

/-! ## A common logical eigenbasis, and the ratio character -/

/-- A vector whose line and whose perpendicular line are preserved by *every*
diagonal symmetry.  This is the common eigenbasis of the abelian group; it is
constructed below from any projectively nontrivial element. -/
structure LogicalDiagonalizer (C : CodeSpec.ExactCode n 2 d) where
  v : Fin 2 → ℂ
  v_ne_zero : v ≠ 0
  preservesFirst : ∀ u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame),
    ∃ a : ℂ, logicalAction C.frame
      (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n)) v = a • v
  preservesSecond : ∀ u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame),
    ∃ b : ℂ, logicalAction C.frame
      (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n))
        (perpendicular v) = b • perpendicular v

namespace LogicalDiagonalizer



/-- The scalar by which a symmetry acts on the first eigenline. -/
noncomputable def first (D : LogicalDiagonalizer C)
    (u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) : ℂ :=
  Classical.choose (D.preservesFirst u)

theorem first_spec (D : LogicalDiagonalizer C)
    (u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) :
    logicalAction C.frame
      (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n)) D.v
      = D.first u • D.v :=
  Classical.choose_spec (D.preservesFirst u)

/-- The scalar by which a symmetry acts on the second eigenline. -/
noncomputable def second (D : LogicalDiagonalizer C)
    (u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) : ℂ :=
  Classical.choose (D.preservesSecond u)

theorem second_spec (D : LogicalDiagonalizer C)
    (u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) :
    logicalAction C.frame
      (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n))
      (perpendicular D.v) = D.second u • perpendicular D.v :=
  Classical.choose_spec (D.preservesSecond u)

/-- Eigenvalues on a nonzero vector are unique. -/
theorem scalar_unique {z : Fin 2 → ℂ} (hz : z ≠ 0) {a b : ℂ}
    (h : a • z = b • z) : a = b := by
  have : (a - b) • z = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp this with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hz

end LogicalDiagonalizer

namespace LogicalDiagonalizer

/-- Both eigenvalue maps are multiplicative. -/
theorem first_mul (D : LogicalDiagonalizer C)
    (u v : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) :
    D.first (u * v) = D.first u * D.first v := by
  refine scalar_unique D.v_ne_zero ?_
  rw [← first_spec D (u * v)]
  have hmul := logicalAction_mul (C := C) u.2 v.2
  have : ((u * v : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame))
      : LocalPhase n) = (u : LocalPhase n) * (v : LocalPhase n) :=
    Subgroup.coe_mul _ u v
  rw [this, hmul]
  simp only [LinearMap.comp_apply]
  rw [first_spec D v, map_smul, first_spec D u, smul_smul, mul_comm]

theorem second_mul (D : LogicalDiagonalizer C)
    (u v : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) :
    D.second (u * v) = D.second u * D.second v := by
  refine scalar_unique (perpendicular_ne_zero D.v_ne_zero) ?_
  rw [← second_spec D (u * v)]
  have hmul := logicalAction_mul (C := C) u.2 v.2
  have : ((u * v : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame))
      : LocalPhase n) = (u : LocalPhase n) * (v : LocalPhase n) :=
    Subgroup.coe_mul _ u v
  rw [this, hmul]
  simp only [LinearMap.comp_apply]
  rw [second_spec D v, map_smul, second_spec D u, smul_smul, mul_comm]

@[simp] theorem first_one (D : LogicalDiagonalizer C) : D.first 1 = 1 := by
  refine scalar_unique D.v_ne_zero ?_
  rw [← first_spec D 1]
  simp

@[simp] theorem second_one (D : LogicalDiagonalizer C) : D.second 1 = 1 := by
  refine scalar_unique (perpendicular_ne_zero D.v_ne_zero) ?_
  rw [← second_spec D 1]
  simp

theorem first_ne_zero (D : LogicalDiagonalizer C)
    (u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) :
    D.first u ≠ 0 := by
  intro h
  have := D.first_mul u u ⁻¹
  rw [mul_inv_cancel, first_one, h, zero_mul] at this
  exact one_ne_zero this

theorem second_ne_zero (D : LogicalDiagonalizer C)
    (u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) :
    D.second u ≠ 0 := by
  intro h
  have := D.second_mul u u ⁻¹
  rw [mul_inv_cancel, second_one, h, zero_mul] at this
  exact one_ne_zero this

end LogicalDiagonalizer

namespace LogicalDiagonalizer

/-- **The phase-ratio character on the symmetry group**: the second logical
eigenvalue divided by the first, exactly as in `thm:rank-two-sslp`. -/
noncomputable def ratio (D : LogicalDiagonalizer C) :
    diagonalSymmetryGroup (CodeProjector.ofFrame C.frame) →* ℂ where
  toFun u := D.second u / D.first u
  map_one' := by simp
  map_mul' u v := by
    simp only [second_mul, first_mul]
    field_simp

/-- A symmetry with ratio one acts as one scalar on the whole logical plane,
hence is projectively trivial.  This is faithfulness of the character. -/
theorem isProjectivelyTrivial_of_ratio_eq_one (D : LogicalDiagonalizer C)
    {u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)}
    (h : D.ratio u = 1) :
    IsProjectivelyTrivial (CodeProjector.ofFrame C.frame) u := by
  have hfirst := D.first_ne_zero u
  have heq : D.second u = D.first u := by
    have : D.second u / D.first u = 1 := h
    field_simp at this
    exact this
  refine isProjectivelyTrivial_of_logicalAction_eq_smul hfirst ?_
  refine LinearMap.ext fun z => ?_
  obtain ⟨c, d, rfl⟩ := exists_decomposition D.v_ne_zero z
  rw [map_add, map_smul, map_smul, first_spec D u, second_spec D u, heq]
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_add]
  rw [smul_smul, smul_smul, smul_smul, smul_smul, mul_comm c, mul_comm d]

/-- The ratio character descends to the intrinsic quotient. -/
noncomputable def intrinsicRatio (D : LogicalDiagonalizer C) :
    IntrinsicProjectiveDiagonalLogicalGroup (CodeProjector.ofFrame C.frame)
      →* ℂ :=
  QuotientGroup.lift _ D.ratio (fun u hu => by
    obtain ⟨lam, hlam, hact⟩ := hu
    have hscal := logicalAction_eq_smul_of_isProjectivelyTrivial
      (C := C) (u := u) ⟨lam, hlam, hact⟩
    obtain ⟨lam', hlam', hlam'eq⟩ := hscal
    have h1 : D.first u = lam' := by
      refine scalar_unique D.v_ne_zero ?_
      rw [← first_spec D u, hlam'eq]
      simp
    have h2 : D.second u = lam' := by
      refine scalar_unique (perpendicular_ne_zero D.v_ne_zero) ?_
      rw [← second_spec D u, hlam'eq]
      simp
    show D.second u / D.first u = 1
    rw [h1, h2, div_self hlam'])

/-- **The descended character is faithful.** -/
theorem intrinsicRatio_injective (D : LogicalDiagonalizer C) :
    Function.Injective D.intrinsicRatio := by
  refine (injective_iff_map_eq_one _).2 ?_
  intro g
  refine QuotientGroup.induction_on g ?_
  intro u hu
  have hr : D.ratio u = 1 := hu
  rw [QuotientGroup.eq_one_iff]
  exact isProjectivelyTrivial_of_ratio_eq_one D hr

end LogicalDiagonalizer

/-! ## Constructing a common eigenbasis from one nontrivial element -/

/-- A diagonal symmetry, as a real gate.  Every local phase is an exponential,
so the two descriptions of the same operation coincide. -/
theorem diagonalEnd_eq_realGateEnd {u : LocalPhase n} {theta : Fin n → ℝ}
    (h : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * ((theta j : ℝ) : ℂ)) = ((u j : ℂ))) :
    GlobalClassificationBridge.diagonalEnd u
      = PhaseSectorBridge.realGateEnd theta := by
  refine LinearMap.ext fun phi => ?_
  exact (SymmetryToEntrance.realGateEnd_eq_diagonalAction u theta h phi).symm

/-- If a symmetry acts with the SAME eigenvalue on a vector and on its
perpendicular, it is a scalar on the whole plane, hence projectively
trivial. -/
theorem isProjectivelyTrivial_of_eigen_eq
    {u : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)}
    {v : Fin 2 → ℂ} (hv : v ≠ 0) {mu : ℂ} (hmu : mu ≠ 0)
    (h1 : logicalAction C.frame
      (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n)) v = mu • v)
    (h2 : logicalAction C.frame
      (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n))
        (perpendicular v) = mu • perpendicular v) :
    IsProjectivelyTrivial (CodeProjector.ofFrame C.frame) u := by
  refine isProjectivelyTrivial_of_logicalAction_eq_smul hmu ?_
  refine LinearMap.ext fun z => ?_
  obtain ⟨c, d, rfl⟩ := exists_decomposition hv z
  rw [map_add, map_smul, map_smul, h1, h2]
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_add]
  rw [smul_smul, smul_smul, smul_smul, smul_smul, mul_comm c, mul_comm d]

/-- Logical matrices of diagonal symmetries commute, because the symmetries
themselves do. -/
theorem commute_logicalAction
    (u v : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame)) :
    (logicalAction C.frame
        (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n))).comp
      (logicalAction C.frame
        (GlobalClassificationBridge.diagonalEnd (v : LocalPhase n)))
      = (logicalAction C.frame
          (GlobalClassificationBridge.diagonalEnd (v : LocalPhase n))).comp
        (logicalAction C.frame
          (GlobalClassificationBridge.diagonalEnd (u : LocalPhase n))) := by
  rw [← logicalAction_mul (C := C) u.2 v.2,
    ← logicalAction_mul (C := C) v.2 u.2]
  congr 2
  exact MainTheory.IntrinsicTransport.localPhase_mul_comm _ _

/-- **A projectively nontrivial symmetry supplies a common eigenbasis.**

Its logical matrix has two distinct eigenvalues -- equal ones would make it a
scalar -- so its eigenlines are one dimensional, and since the group is
abelian every other symmetry commutes with it and therefore preserves both
lines. -/
theorem nonempty_diagonalizer (C : CodeSpec.ExactCode n 2 d)
    (u0 : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame))
    (h0 : ¬ IsProjectivelyTrivial (CodeProjector.ofFrame C.frame) u0) :
    Nonempty (LogicalDiagonalizer C) := by
  classical
  obtain ⟨theta, htheta⟩ :=
    LocalPhaseAngle.exists_angleVector (u0 : LocalPhase n)
  have hend : GlobalClassificationBridge.diagonalEnd (u0 : LocalPhase n)
      = PhaseSectorBridge.realGateEnd theta := diagonalEnd_eq_realGateEnd htheta
  have hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta) := by
    rw [← hend]; exact codePreserving_diagonalEnd u0.2
  obtain ⟨mu, v, hvne, hveigen⟩ :=
    D3LogicalAction.exists_logical_eigenvector C.frame
      (PhaseSectorBridge.realGateEnd theta)
  obtain ⟨nu, hnueigen⟩ :=
    D3LogicalSecondEigenvector.perpendicular_is_logical_eigenvector
      C.frame theta hpres hvne hveigen
  have hmune : mu ≠ 0 :=
    D3LogicalSecondEigenvector.logical_eigenvalue_ne_zero C.frame theta hpres
      hvne hveigen
  have hveigen' : logicalAction C.frame
      (GlobalClassificationBridge.diagonalEnd (u0 : LocalPhase n)) v
      = mu • v := by rw [hend]; exact hveigen
  have hnueigen' : logicalAction C.frame
      (GlobalClassificationBridge.diagonalEnd (u0 : LocalPhase n))
      (perpendicular v) = nu • perpendicular v := by
    rw [hend]; exact hnueigen
  have hdist : mu ≠ nu := by
    intro heq
    exact h0 (isProjectivelyTrivial_of_eigen_eq hvne hmune hveigen'
      (by rw [heq]; exact hnueigen'))
  refine ⟨⟨v, hvne, ?_, ?_⟩⟩
  · intro u
    exact eq_smul_of_commute hvne hdist hveigen' hnueigen'
      (commute_logicalAction u0 u)
  · intro u
    have hperp : perpendicular (perpendicular v) = -v :=
      perpendicular_perpendicular v
    have hsecond : logicalAction C.frame
        (GlobalClassificationBridge.diagonalEnd (u0 : LocalPhase n))
        (perpendicular (perpendicular v)) = mu • perpendicular (perpendicular v) := by
      rw [hperp, map_neg, hveigen', smul_neg]
    exact eq_smul_of_commute (perpendicular_ne_zero hvne) (Ne.symm hdist)
      hnueigen' hsecond (commute_logicalAction u0 u)

/-! ## Cyclicity

With finiteness already unconditional, a faithful character into the complex
numbers is all that `thm:rank-two-sslp`'s "that group is cyclic" needs. -/

/-- **A finite intrinsic group with a common logical eigenbasis is cyclic**,
for any exact rank-two code.

Finiteness is taken as a hypothesis rather than imported, so that this half of
`thm:rank-two-sslp` is available at every `(n, 2, d)` -- the finiteness input
is currently unconditional only at six qubits, and keeping the two separate
makes plain which half is which. -/
theorem isCyclic_of_diagonalizer (C : CodeSpec.ExactCode n 2 d)
    (D : LogicalDiagonalizer C)
    (hfin : Finite (GlobalClassificationBridge.IntrinsicGroup C)) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame)) := by
  haveI := hfin
  exact MainTheory.Cyclic.isCyclic_of_faithful D.intrinsicRatio
    D.intrinsicRatio_injective

/-- **The intrinsic projective diagonal group of an exact six-qubit code is
cyclic**, whenever it is nontrivial -- with no hypotheses beyond the code.

This is `thm:rank-two-sslp`'s "that group is cyclic, say `C_m`".  Finiteness
comes from the bounded-label cover; cyclicity from the phase-ratio character
built on the eigenbasis of any nontrivial element. -/
theorem isCyclic_of_nontrivial (C : CodeSpec.ExactCode n 2 d)
    (u0 : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame))
    (h0 : ¬ IsProjectivelyTrivial (CodeProjector.ofFrame C.frame) u0)
    (hfin : Finite (GlobalClassificationBridge.IntrinsicGroup C)) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame)) := by
  obtain ⟨D⟩ := nonempty_diagonalizer C u0 h0
  exact isCyclic_of_diagonalizer C D hfin

/-- The same conclusion phrased on the intrinsic group directly: some class is
not the identity. -/
theorem isCyclic_of_exists_class_ne_one (C : CodeSpec.ExactCode n 2 d)
    (hfin : Finite (GlobalClassificationBridge.IntrinsicGroup C))
    (h : ∃ g : IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame), g ≠ 1) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame)) := by
  obtain ⟨g, hg⟩ := h
  refine QuotientGroup.induction_on g (fun u hu => ?_) hg
  refine isCyclic_of_nontrivial C u ?_ hfin
  intro htriv
  exact hu ((QuotientGroup.eq_one_iff u).2 htriv)

end MainTheory.LogicalCharacter
