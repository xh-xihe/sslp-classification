import QECC.FirstTheorem

namespace QECC

open scoped BigOperators

noncomputable section

/-- The residue acquired by a computational-basis string under a modular phase vector. -/
def subsetSum {n q : ℕ} (a : Fin n → ZMod q) (x : BitString n) : ZMod q :=
  ∑ j : Fin n, if x j then a j else 0

@[simp] theorem subsetSum_zero {n q : ℕ} (x : BitString n) :
    subsetSum (0 : Fin n → ZMod q) x = 0 := by
  simp [subsetSum]

@[simp] theorem subsetSum_add {n q : ℕ} (a c : Fin n → ZMod q)
    (x : BitString n) :
    subsetSum (a + c) x = subsetSum a x + subsetSum c x := by
  simp only [subsetSum, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases x j <;> simp

@[simp] theorem subsetSum_neg {n q : ℕ} (a : Fin n → ZMod q)
    (x : BitString n) :
    subsetSum (-a) x = -subsetSum a x := by
  simp only [subsetSum, Pi.neg_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases x j <;> simp

@[simp] theorem subsetSum_singletonBit {n q : ℕ} (a : Fin n → ZMod q)
    (j : Fin n) :
    subsetSum a (singletonBit j) = a j := by
  simp [subsetSum, singletonBit]

/-- The embedding of a residue into the phase circle, with positivity supplying
the nonzero-modulus instance required by `ZMod.toAddCircle`. -/
def zmodPhase (q : ℕ) (hq : 0 < q) (b : ZMod q) : LocalPhase := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact ZMod.toAddCircle b

/-- The complex unit scalar corresponding to a residue modulo `q`. -/
def zmodPhaseScalar (q : ℕ) (hq : 0 < q) (b : ZMod q) : ℂ :=
  (((zmodPhase q hq b).toCircle : Circle) : ℂ)

@[simp] theorem zmodPhase_zero (q : ℕ) (hq : 0 < q) :
    zmodPhase q hq 0 = 0 := by
  letI : NeZero q := ⟨hq.ne'⟩
  simp [zmodPhase]

@[simp] theorem zmodPhase_add (q : ℕ) (hq : 0 < q) (b c : ZMod q) :
    zmodPhase q hq (b + c) = zmodPhase q hq b + zmodPhase q hq c := by
  letI : NeZero q := ⟨hq.ne'⟩
  simp [zmodPhase]

/-- Modular subset sums agree with the circle-valued subset sums used by
`diagonalGate`. -/
theorem supportPhase_phaseHom {n q : ℕ} (hq : 0 < q)
    (a : Fin n → ZMod q) (x : BitString n) :
    supportPhase (phaseHom n q hq a) x = zmodPhase q hq (subsetSum a x) := by
  letI : NeZero q := ⟨hq.ne'⟩
  simp only [supportPhase, subsetSum, phaseHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, zmodPhase]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases x j <;> simp

/-- The fiber of the modular subset-sum map over `b`. -/
def subsetSumFiber {n q : ℕ} (a : Fin n → ZMod q) (b : ZMod q) :
    Set (BitString n) :=
  {x | subsetSum a x = b}

@[simp] theorem mem_subsetSumFiber {n q : ℕ} {a : Fin n → ZMod q}
    {b : ZMod q} {x : BitString n} :
    x ∈ subsetSumFiber a b ↔ subsetSum a x = b :=
  Iff.rfl

theorem mem_own_subsetSumFiber {n q : ℕ} (a : Fin n → ZMod q)
    (x : BitString n) :
    x ∈ subsetSumFiber a (subsetSum a x) :=
  rfl

/-- Distinct subset-sum fibers are disjoint. -/
theorem subsetSumFiber_disjoint {n q : ℕ} (a : Fin n → ZMod q)
    {b c : ZMod q} (hbc : b ≠ c) :
    Disjoint (subsetSumFiber a b) (subsetSumFiber a c) := by
  rw [Set.disjoint_left]
  intro x hxb hxc
  exact hbc (hxb.symm.trans hxc)

/-- The subset-sum fibers partition the computational basis. -/
theorem iUnion_subsetSumFiber {n q : ℕ} (a : Fin n → ZMod q) :
    ⋃ b : ZMod q, subsetSumFiber a b = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.2 ⟨subsetSum a x, rfl⟩

/-- Each computational-basis string belongs to a unique subset-sum fiber. -/
theorem existsUnique_mem_subsetSumFiber {n q : ℕ} (a : Fin n → ZMod q)
    (x : BitString n) :
    ∃! b : ZMod q, x ∈ subsetSumFiber a b := by
  refine ⟨subsetSum a x, rfl, ?_⟩
  intro b hb
  exact hb.symm

/-- State vectors whose computational-basis support lies in one subset-sum fiber. -/
def fiberSubspace {n q : ℕ} (a : Fin n → ZMod q) (b : ZMod q) :
    Submodule ℂ (State n) where
  carrier := {psi | ∀ x, subsetSum a x ≠ b → psi x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro psi phi hpsi hphi x hx
    simp [hpsi x hx, hphi x hx]
  smul_mem' := by
    intro c psi hpsi x hx
    simp [hpsi x hx]

@[simp] theorem mem_fiberSubspace {n q : ℕ} {a : Fin n → ZMod q}
    {b : ZMod q} {psi : State n} :
    psi ∈ fiberSubspace a b ↔ ∀ x, subsetSum a x ≠ b → psi x = 0 :=
  Iff.rfl

/-- Coordinate projector onto the span of the basis strings in one subset-sum fiber. -/
def fiberProjector {n q : ℕ} (a : Fin n → ZMod q) (b : ZMod q) : Operator n :=
  Matrix.diagonal fun x ↦ if subsetSum a x = b then 1 else 0

@[simp] theorem fiberProjector_mulVec_apply {n q : ℕ}
    (a : Fin n → ZMod q) (b : ZMod q) (psi : State n) (x : BitString n) :
    (fiberProjector a b).mulVec psi x =
      if subsetSum a x = b then psi x else 0 := by
  classical
  simp [fiberProjector, Matrix.mulVec]

theorem fiberProjector_mulVec_eq_self_iff {n q : ℕ}
    (a : Fin n → ZMod q) (b : ZMod q) (psi : State n) :
    (fiberProjector a b).mulVec psi = psi ↔ psi ∈ fiberSubspace a b := by
  constructor
  · intro h x hx
    have hxentry := congrFun h x
    simpa [fiberProjector_mulVec_apply, hx] using hxentry.symm
  · intro h
    funext x
    by_cases hx : subsetSum a x = b
    · simp [fiberProjector_mulVec_apply, hx]
    · simp [fiberProjector_mulVec_apply, hx, h x hx]

@[simp] theorem fiberProjector_idempotent {n q : ℕ}
    (a : Fin n → ZMod q) (b : ZMod q) :
    fiberProjector a b * fiberProjector a b = fiberProjector a b := by
  classical
  unfold fiberProjector
  rw [Matrix.diagonal_mul_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases hx : subsetSum a x = b <;> simp [hx]
  · simp [Matrix.diagonal_apply_ne _ hxy]

@[simp] theorem fiberProjector_conjTranspose {n q : ℕ}
    (a : Fin n → ZMod q) (b : ZMod q) :
    (fiberProjector a b).conjTranspose = fiberProjector a b := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [fiberProjector, Matrix.conjTranspose_apply]
  · simp [fiberProjector, Matrix.conjTranspose_apply, hxy, Ne.symm hxy]

/-- Coordinate projectors onto distinct fibers have zero product. -/
theorem fiberProjector_mul_eq_zero {n q : ℕ} (a : Fin n → ZMod q)
    {b c : ZMod q} (hbc : b ≠ c) :
    fiberProjector a b * fiberProjector a c = 0 := by
  classical
  unfold fiberProjector
  rw [Matrix.diagonal_mul_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases hxb : subsetSum a x = b
    · simp [hxb, hbc]
    · simp [hxb]
  · simp [Matrix.diagonal_apply_ne _ hxy]

/-- The range of the coordinate projector is precisely the corresponding fiber
subspace. -/
theorem range_fiberProjector_mulVecLin {n q : ℕ}
    (a : Fin n → ZMod q) (b : ZMod q) :
    LinearMap.range (fiberProjector a b).mulVecLin = fiberSubspace a b := by
  ext psi
  constructor
  · rintro ⟨phi, rfl⟩
    rw [← fiberProjector_mulVec_eq_self_iff]
    change (fiberProjector a b).mulVec ((fiberProjector a b).mulVec phi) =
      (fiberProjector a b).mulVec phi
    rw [Matrix.mulVec_mulVec, fiberProjector_idempotent]
  · intro hpsi
    refine ⟨psi, ?_⟩
    exact (fiberProjector_mulVec_eq_self_iff a b psi).2 hpsi

/-- A vector supported in two distinct fibers is zero. -/
theorem eq_zero_of_mem_fiberSubspace_of_mem_fiberSubspace {n q : ℕ}
    (a : Fin n → ZMod q) {b c : ZMod q} (hbc : b ≠ c)
    {psi : State n} (hb : psi ∈ fiberSubspace a b)
    (hc : psi ∈ fiberSubspace a c) :
    psi = 0 := by
  funext x
  by_cases hxb : subsetSum a x = b
  · have hxc : subsetSum a x ≠ c := by
      intro hx
      exact hbc (hxb.symm.trans hx)
    simpa using hc x hxc
  · simpa using hb x hxb

/-- For positive modulus, the coordinate projectors over all subset-sum fibers
resolve the identity. -/
theorem sum_fiberProjector {n q : ℕ} [NeZero q] (a : Fin n → ZMod q) :
    ∑ b : ZMod q, fiberProjector a b = 1 := by
  classical
  ext x y
  simp only [Matrix.sum_apply, fiberProjector]
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply, ↓reduceIte]
    rw [Finset.sum_eq_single (subsetSum a x)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · simp only [Matrix.diagonal_apply_ne _ hxy, Finset.sum_const_zero,
      Matrix.one_apply, if_neg hxy]

/-- The computational-basis vector at `x`. -/
def computationalBasisState {n : ℕ} (x : BitString n) : State n :=
  fun y ↦ if y = x then 1 else 0

@[simp] theorem computationalBasisState_apply_self {n : ℕ} (x : BitString n) :
    computationalBasisState x x = 1 := by
  simp [computationalBasisState]

/-- A diagonal product gate acts on a computational-basis state by its subset-sum
phase. -/
theorem diagonalGate_mulVec_computationalBasisState {n : ℕ}
    (theta : PhaseVector n) (x : BitString n) :
    (diagonalGate theta).mulVec (computationalBasisState x) =
      (((supportPhase theta x).toCircle : Circle) : ℂ) • computationalBasisState x := by
  classical
  funext y
  by_cases hyx : y = x
  · subst y
    simp [diagonalGate, Matrix.mulVec, computationalBasisState]
  · simp [diagonalGate, Matrix.mulVec, computationalBasisState, hyx]

/-- Modular form of the diagonal action on a computational-basis state. -/
theorem diagonalGate_phaseHom_mulVec_computationalBasisState {n q : ℕ}
    (hq : 0 < q) (a : Fin n → ZMod q) (x : BitString n) :
    (diagonalGate (phaseHom n q hq a)).mulVec (computationalBasisState x) =
      zmodPhaseScalar q hq (subsetSum a x) • computationalBasisState x := by
  rw [diagonalGate_mulVec_computationalBasisState,
    supportPhase_phaseHom hq a x]
  rfl

/-- On the coordinate subspace supported in one subset-sum fiber, the modular
diagonal gate is multiplication by the corresponding scalar. -/
theorem diagonalGate_phaseHom_mulVec_of_mem_fiberSubspace {n q : ℕ}
    (hq : 0 < q) (a : Fin n → ZMod q) (b : ZMod q)
    (psi : State n) (hpsi : psi ∈ fiberSubspace a b) :
    (diagonalGate (phaseHom n q hq a)).mulVec psi =
      zmodPhaseScalar q hq b • psi := by
  classical
  funext x
  by_cases hx : subsetSum a x = b
  · simp [diagonalGate, Matrix.mulVec, zmodPhaseScalar,
      supportPhase_phaseHom hq a x, hx]
  · have hzero := hpsi x hx
    simp [diagonalGate, Matrix.mulVec, hzero]

end

end QECC
