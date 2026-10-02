import QECC.Basic

namespace QECC

open scoped BigOperators

noncomputable section

/-- One local phase, measured in full turns. -/
abbrev LocalPhase := UnitAddCircle

/-- A diagonal product phase on `n` qubits. -/
abbrev PhaseVector (n : ℕ) := Fin n → LocalPhase

/-- The subset-sum phase acquired by a computational-basis string. -/
def supportPhase {n : ℕ} (theta : PhaseVector n) (x : BitString n) : LocalPhase :=
  ∑ j : Fin n, if x j then theta j else 0

/-- A chosen representative in `[0,1)` of a circle-valued phase. -/
def phaseLift {n : ℕ} (theta : PhaseVector n) (j : Fin n) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 (theta j)).1

@[simp] theorem coe_phaseLift {n : ℕ} (theta : PhaseVector n) (j : Fin n) :
    ((phaseLift theta j : ℝ) : LocalPhase) = theta j := by
  change (AddCircle.equivIco (1 : ℝ) 0).symm
    (AddCircle.equivIco (1 : ℝ) 0 (theta j)) = theta j
  exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (theta j)

/-- The real subset sum attached to a real phase vector. -/
def realSupportWeight {n : ℕ} (h : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ j : Fin n, h j * bitReal (x j)

@[simp] theorem realSupportWeight_zero {n : ℕ} (x : BitString n) :
    realSupportWeight (0 : Fin n → ℝ) x = 0 := by
  simp [realSupportWeight]

theorem supportPhase_coe_real {n : ℕ} (h : Fin n → ℝ) (x : BitString n) :
    supportPhase (fun j => ((h j : ℝ) : LocalPhase)) x =
      ((realSupportWeight h x : ℝ) : LocalPhase) := by
  change
    (∑ j : Fin n,
      if x j then
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (h j)
      else 0) =
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
        (∑ j : Fin n, h j * bitReal (x j))
  rw [map_sum]
  congr 1
  funext j
  cases x j <;> simp [bitReal]

theorem supportPhase_lift {n : ℕ} (theta : PhaseVector n) (x : BitString n) :
    ((realSupportWeight (phaseLift theta) x : ℝ) : LocalPhase) = supportPhase theta x := by
  rw [← supportPhase_coe_real]
  congr 1
  funext j
  exact coe_phaseLift theta j

@[simp] theorem supportPhase_zero {n : ℕ} (x : BitString n) :
    supportPhase (0 : PhaseVector n) x = 0 := by
  simp [supportPhase]

@[simp] theorem supportPhase_add {n : ℕ} (theta phi : PhaseVector n) (x : BitString n) :
    supportPhase (theta + phi) x = supportPhase theta x + supportPhase phi x := by
  simp only [supportPhase, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1
  funext j
  split <;> simp_all

@[simp] theorem supportPhase_neg {n : ℕ} (theta : PhaseVector n) (x : BitString n) :
    supportPhase (-theta) x = -supportPhase theta x := by
  simp only [supportPhase, Pi.neg_apply, ← Finset.sum_neg_distrib]
  congr 1
  funext j
  split <;> simp_all

/-- The diagonal product unitary represented by a phase vector. -/
def diagonalGate {n : ℕ} (theta : PhaseVector n) : Operator n :=
  Matrix.diagonal fun x => ((supportPhase theta x).toCircle : ℂ)

/-- The computational-basis string supported at one coordinate. -/
def singletonBit {n : ℕ} (j : Fin n) : BitString n :=
  fun k => decide (k = j)

@[simp] theorem supportPhase_singletonBit {n : ℕ} (theta : PhaseVector n) (j : Fin n) :
    supportPhase theta (singletonBit j) = theta j := by
  simp [supportPhase, singletonBit]

@[simp] theorem diagonalGate_zero {n : ℕ} :
    diagonalGate (0 : PhaseVector n) = 1 := by
  classical
  ext x y
  simp [diagonalGate, Matrix.diagonal_apply, Matrix.one_apply]

@[simp] theorem diagonalGate_add {n : ℕ} (theta phi : PhaseVector n) :
    diagonalGate (theta + phi) = diagonalGate theta * diagonalGate phi := by
  classical
  rw [diagonalGate, diagonalGate, diagonalGate, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  simp [AddCircle.toCircle_add]

/-- Product phases map homomorphically to physical diagonal matrices. -/
def diagonalGateHom (n : ℕ) : Multiplicative (PhaseVector n) →* Operator n where
  toFun theta := diagonalGate theta.toAdd
  map_one' := diagonalGate_zero
  map_mul' theta phi := diagonalGate_add theta.toAdd phi.toAdd

/-- The phase parametrization of diagonal product gates is injective. -/
theorem diagonalGateHom_injective (n : ℕ) : Function.Injective (diagonalGateHom n) := by
  intro theta phi h
  apply Multiplicative.toAdd.injective
  funext j
  apply AddCircle.injective_toCircle one_ne_zero
  have hentry := congrFun (congrFun h (singletonBit j)) (singletonBit j)
  change diagonalGate theta.toAdd (singletonBit j) (singletonBit j) =
    diagonalGate phi.toAdd (singletonBit j) (singletonBit j) at hentry
  simpa [diagonalGate, Matrix.diagonal_apply] using hentry

/-- The matrix order of a physical diagonal gate is the additive order of its phase vector. -/
theorem diagonalGate_order {n : ℕ} (theta : PhaseVector n) :
    orderOf (diagonalGate theta) = addOrderOf theta := by
  exact orderOf_injective (diagonalGateHom n) (diagonalGateHom_injective n)
    (Multiplicative.ofAdd theta)

/-- Negating every phase gives the adjoint physical gate. -/
theorem diagonalGate_conjTranspose {n : ℕ} (theta : PhaseVector n) :
    (diagonalGate theta).conjTranspose = diagonalGate (-theta) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [diagonalGate, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      ↓reduceIte, supportPhase_neg, AddCircle.toCircle_neg, Circle.coe_inv]
    exact (Circle.coe_inv_eq_conj (supportPhase theta x).toCircle).symm
  · simp [diagonalGate, Matrix.conjTranspose_apply, hxy, Ne.symm hxy]

/-- A diagonal product gate is a unitary matrix. -/
def diagonalUnitary {n : ℕ} (theta : PhaseVector n) :
    Matrix.unitaryGroup (BitString n) ℂ := by
  refine ⟨diagonalGate theta, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose, diagonalGate_conjTranspose,
    ← diagonalGate_add, add_neg_cancel, diagonalGate_zero]

namespace CodeProjector

variable {n K : ℕ} (C : CodeProjector n K)

/-- Phase vectors whose diagonal product gate preserves the code projector. -/
def Preserves (theta : PhaseVector n) : Prop :=
  ∀ x y, C.proj x y ≠ 0 → supportPhase theta x = supportPhase theta y

/-- Phase vectors that act as one common phase on the code. -/
def ActsAsScalar (theta : PhaseVector n) : Prop :=
  ∃ c : LocalPhase, ∀ x y, C.proj x y ≠ 0 → supportPhase theta x = c

/-- The edge definition of preservation is exactly commutation with the projector. -/
theorem preserves_iff_commutes (theta : PhaseVector n) :
    C.Preserves theta ↔
      diagonalGate theta * C.proj = C.proj * diagonalGate theta := by
  constructor
  · intro hpres
    classical
    ext x y
    by_cases hxy : C.proj x y = 0
    · simp [diagonalGate, hxy]
    · simp only [diagonalGate, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rw [hpres x y hxy]
      exact mul_comm _ _
  · intro hcomm x y hxy
    have hentry := congrFun (congrFun hcomm x) y
    simp only [diagonalGate, Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
    rw [mul_comm (((supportPhase theta x).toCircle : Circle) : ℂ) (C.proj x y)] at hentry
    have hc : (((supportPhase theta x).toCircle : Circle) : ℂ) =
        (((supportPhase theta y).toCircle : Circle) : ℂ) :=
      mul_left_cancel₀ hxy hentry
    apply AddCircle.injective_toCircle one_ne_zero
    exact Subtype.coe_injective hc

/-- Preservation in edge form is the paper's operator equation `D P D† = P`. -/
theorem preserves_iff_gate_conjugates (theta : PhaseVector n) :
    C.Preserves theta ↔
      diagonalGate theta * C.proj * (diagonalGate theta).conjTranspose = C.proj := by
  rw [C.preserves_iff_commutes]
  constructor
  · intro hcomm
    calc
      diagonalGate theta * C.proj * (diagonalGate theta).conjTranspose =
          (C.proj * diagonalGate theta) * diagonalGate (-theta) := by
            rw [hcomm, diagonalGate_conjTranspose]
      _ = C.proj * (diagonalGate theta * diagonalGate (-theta)) := by
            rw [Matrix.mul_assoc]
      _ = C.proj := by
            rw [← diagonalGate_add, add_neg_cancel, diagonalGate_zero, mul_one]
  · intro hconj
    calc
      diagonalGate theta * C.proj = (diagonalGate theta * C.proj) * 1 := by
            rw [mul_one]
      _ = (diagonalGate theta * C.proj) *
          ((diagonalGate theta).conjTranspose * diagonalGate theta) := by
            rw [diagonalGate_conjTranspose, ← diagonalGate_add, neg_add_cancel,
              diagonalGate_zero]
      _ = (diagonalGate theta * C.proj *
          (diagonalGate theta).conjTranspose) * diagonalGate theta := by
            simp only [Matrix.mul_assoc]
      _ = C.proj * diagonalGate theta := by rw [hconj]

/-- The edge definition of a scalar action is exactly `D P = z P`. -/
theorem actsAsScalar_iff_gate_mul_proj (theta : PhaseVector n) :
    C.ActsAsScalar theta ↔
      ∃ c : LocalPhase, diagonalGate theta * C.proj =
        ((c.toCircle : Circle) : ℂ) • C.proj := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    classical
    ext x y
    by_cases hxy : C.proj x y = 0
    · simp [diagonalGate, hxy]
    · simp only [diagonalGate, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
      rw [hc x y hxy]
  · rintro ⟨c, hgate⟩
    refine ⟨c, fun x y hxy => ?_⟩
    have hentry := congrFun (congrFun hgate x) y
    simp only [diagonalGate, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] at hentry
    have hc : (((supportPhase theta x).toCircle : Circle) : ℂ) =
        ((c.toCircle : Circle) : ℂ) := mul_right_cancel₀ hxy hentry
    apply AddCircle.injective_toCircle one_ne_zero
    exact Subtype.coe_injective hc

/-- A preserving diagonal gate maps the projector range (the code space) to itself. -/
theorem preserves_code_range (theta : PhaseVector n) (hpres : C.Preserves theta)
    (psi : State n) (hpsi : C.proj.mulVec psi = psi) :
    C.proj.mulVec ((diagonalGate theta).mulVec psi) =
      (diagonalGate theta).mulVec psi := by
  have hcomm := (C.preserves_iff_commutes theta).mp hpres
  calc
    C.proj.mulVec ((diagonalGate theta).mulVec psi) =
        (C.proj * diagonalGate theta).mulVec psi := Matrix.mulVec_mulVec _ _ _
    _ = (diagonalGate theta * C.proj).mulVec psi := by rw [hcomm]
    _ = (diagonalGate theta).mulVec (C.proj.mulVec psi) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ = (diagonalGate theta).mulVec psi := by rw [hpsi]

/-- The linear action induced by a preserving gate on the `K`-dimensional code space. -/
def logicalMap (theta : PhaseVector n) (hpres : C.Preserves theta) :
    C.CodeSpace →ₗ[ℂ] C.CodeSpace where
  toFun psi := ⟨(diagonalGate theta).mulVec psi.1, by
    apply (C.mem_codeSpace_iff _).2
    apply C.preserves_code_range theta hpres psi.1
    exact (C.mem_codeSpace_iff _).1 psi.2⟩
  map_add' psi phi := by
    apply Subtype.ext
    simp [Matrix.mulVec_add]
  map_smul' c psi := by
    apply Subtype.ext
    simp [Matrix.mulVec_smul]

@[simp] theorem logicalMap_apply (theta : PhaseVector n) (hpres : C.Preserves theta)
    (psi : C.CodeSpace) :
    (C.logicalMap theta hpres psi).1 = (diagonalGate theta).mulVec psi.1 := rfl

/-- The induced logical action is invertible; its inverse is obtained by negating phases. -/
def logicalEquiv (theta : PhaseVector n) (hpres : C.Preserves theta) :
    C.CodeSpace ≃ₗ[ℂ] C.CodeSpace where
  toLinearMap := C.logicalMap theta hpres
  invFun := C.logicalMap (-theta) (by
    intro x y hxy
    simp [hpres x y hxy])
  left_inv psi := by
    apply Subtype.ext
    change (diagonalGate (-theta)).mulVec ((diagonalGate theta).mulVec psi.1) = psi.1
    rw [Matrix.mulVec_mulVec]
    rw [← diagonalGate_add, neg_add_cancel, diagonalGate_zero, Matrix.one_mulVec]
  right_inv psi := by
    apply Subtype.ext
    change (diagonalGate theta).mulVec ((diagonalGate (-theta)).mulVec psi.1) = psi.1
    rw [Matrix.mulVec_mulVec]
    rw [← diagonalGate_add, add_neg_cancel, diagonalGate_zero, Matrix.one_mulVec]

/-- `ActsAsScalar` means scalar action on every vector in the code space. -/
theorem actsAsScalar_on_code (theta : PhaseVector n) (hscalar : C.ActsAsScalar theta) :
    ∃ c : LocalPhase, ∀ psi : State n, C.proj.mulVec psi = psi →
      (diagonalGate theta).mulVec psi = ((c.toCircle : Circle) : ℂ) • psi := by
  obtain ⟨c, hgate⟩ := (C.actsAsScalar_iff_gate_mul_proj theta).mp hscalar
  refine ⟨c, fun psi hpsi => ?_⟩
  calc
    (diagonalGate theta).mulVec psi =
        (diagonalGate theta).mulVec (C.proj.mulVec psi) := by rw [hpsi]
    _ = (diagonalGate theta * C.proj).mulVec psi := Matrix.mulVec_mulVec _ _ _
    _ = (((c.toCircle : Circle) : ℂ) • C.proj).mulVec psi := by rw [hgate]
    _ = ((c.toCircle : Circle) : ℂ) • C.proj.mulVec psi := Matrix.smul_mulVec _ _ _
    _ = ((c.toCircle : Circle) : ℂ) • psi := by rw [hpsi]

theorem preserves_zero : C.Preserves 0 := by
  intro x y _
  simp

theorem preserves_add {theta phi : PhaseVector n}
    (htheta : C.Preserves theta) (hphi : C.Preserves phi) :
    C.Preserves (theta + phi) := by
  intro x y hxy
  simp [htheta x y hxy, hphi x y hxy]

theorem preserves_neg {theta : PhaseVector n} (htheta : C.Preserves theta) :
    C.Preserves (-theta) := by
  intro x y hxy
  simp [htheta x y hxy]

/-- The additive group of code-preserving diagonal product phases. -/
def preservingPhases : AddSubgroup (PhaseVector n) where
  carrier := C.Preserves
  zero_mem' := C.preserves_zero
  add_mem' := fun htheta hphi => C.preserves_add htheta hphi
  neg_mem' := fun htheta => C.preserves_neg htheta

theorem actsAsScalar_zero : C.ActsAsScalar 0 := by
  refine ⟨0, ?_⟩
  simp

theorem actsAsScalar_add {theta phi : PhaseVector n}
    (htheta : C.ActsAsScalar theta) (hphi : C.ActsAsScalar phi) :
    C.ActsAsScalar (theta + phi) := by
  rcases htheta with ⟨c, hc⟩
  rcases hphi with ⟨d, hd⟩
  refine ⟨c + d, fun x y hxy => ?_⟩
  simp [hc x y hxy, hd x y hxy]

theorem actsAsScalar_neg {theta : PhaseVector n} (htheta : C.ActsAsScalar theta) :
    C.ActsAsScalar (-theta) := by
  rcases htheta with ⟨c, hc⟩
  exact ⟨-c, fun x y hxy => by simp [hc x y hxy]⟩

theorem preserves_of_actsAsScalar {theta : PhaseVector n}
    (htheta : C.ActsAsScalar theta) : C.Preserves theta := by
  rcases htheta with ⟨c, hc⟩
  intro x y hxy
  have hyx : C.proj y x ≠ 0 := by
    intro hyx0
    apply hxy
    have hherm := congrFun (congrFun C.hermitian x) y
    simpa [Matrix.conjTranspose_apply, hyx0] using hherm.symm
  exact (hc x y hxy).trans (hc y x hyx).symm

/-- Scalar actions form the kernel of the projective logical action. -/
def scalarPhases : AddSubgroup C.preservingPhases where
  carrier := fun theta => C.ActsAsScalar theta.1
  zero_mem' := C.actsAsScalar_zero
  add_mem' := fun htheta hphi => C.actsAsScalar_add htheta hphi
  neg_mem' := fun htheta => C.actsAsScalar_neg htheta

/-- The projective diagonal logical group in the chosen product basis. -/
abbrev ProjectiveDiagonalGroup := C.preservingPhases ⧸ C.scalarPhases

/-- A real diagonal Hamiltonian built from the local number operators. -/
def weightedNumberOp (h : Fin n → ℝ) : Operator n :=
  Matrix.diagonal fun x => (realSupportWeight h x : ℂ)

theorem weightedNumberOp_eq_sum (h : Fin n → ℝ) :
    weightedNumberOp h = ∑ j : Fin n, (h j : ℂ) • numberOp j := by
  classical
  ext x y
  simp [weightedNumberOp, realSupportWeight, numberOp, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.diagonal_apply]

/-- Exact equality of all edge subset sums makes the diagonal Hamiltonian commute with `P`. -/
theorem weightedNumberOp_commutes (h : Fin n → ℝ)
    (hedge : ∀ x y, C.proj x y ≠ 0 → realSupportWeight h x = realSupportWeight h y) :
    weightedNumberOp h * C.proj = C.proj * weightedNumberOp h := by
  classical
  ext x y
  by_cases hxy : C.proj x y = 0
  · simp [weightedNumberOp, hxy]
  · simp only [weightedNumberOp, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [hedge x y hxy]
    exact mul_comm _ _

/-- Compressing a weighted number operator to a detecting code gives a scalar. -/
theorem weightedNumberOp_compression (h : Fin n → ℝ) (mu : Fin n → ℝ)
    (hmu : ∀ j, C.proj * numberOp j * C.proj = (mu j : ℂ) • C.proj) :
    C.proj * weightedNumberOp h * C.proj =
      ((∑ j : Fin n, h j * mu j : ℝ) : ℂ) • C.proj := by
  classical
  rw [weightedNumberOp_eq_sum h]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul, hmu, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rfl

/-- The infinitesimal step: an exact edge-kernel direction acts projectively as a scalar. -/
theorem actsAsScalar_of_exact_edges (h : Fin n → ℝ)
    (hdetect : C.DetectsNumberOps)
    (hedge : ∀ x y, C.proj x y ≠ 0 → realSupportWeight h x = realSupportWeight h y) :
    C.ActsAsScalar (fun j => ((h j : ℝ) : LocalPhase)) := by
  classical
  rcases hdetect with ⟨mu, hmu⟩
  let c : ℝ := ∑ j : Fin n, h j * mu j
  have hcomm := C.weightedNumberOp_commutes h hedge
  have hcomp := C.weightedNumberOp_compression h mu hmu
  have hscalar : weightedNumberOp h * C.proj = (c : ℂ) • C.proj := by
    calc
      weightedNumberOp h * C.proj
          = weightedNumberOp h * (C.proj * C.proj) := by rw [C.idempotent]
      _ = (weightedNumberOp h * C.proj) * C.proj := by
            rw [Matrix.mul_assoc]
      _ = (C.proj * weightedNumberOp h) * C.proj := by rw [hcomm]
      _ = C.proj * weightedNumberOp h * C.proj := rfl
      _ = (c : ℂ) • C.proj := hcomp
  refine ⟨((c : ℝ) : LocalPhase), fun x y hxy => ?_⟩
  have hentry := congrFun (congrFun hscalar x) y
  simp only [weightedNumberOp, Matrix.diagonal_mul] at hentry
  have hwc : (realSupportWeight h x : ℂ) = (c : ℂ) := by
    exact mul_right_cancel₀ hxy hentry
  have hw : realSupportWeight h x = c := by exact_mod_cast hwc
  rw [supportPhase_coe_real, hw]

end CodeProjector

end

end QECC
