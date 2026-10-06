import QECC.CodeTransport
import QECC.SubsetSum

namespace QECC

open scoped BigOperators

noncomputable section

/-- Flipping the computational bit at `j` changes the sign of its modular
coefficient. -/
def xorCoefficient {n q : ℕ} (t : BitString n) (a : Fin n → ZMod q) :
    Fin n → ZMod q :=
  fun j ↦ if t j then -a j else a j

@[simp] theorem xorCoefficient_apply_false {n q : ℕ} (t : BitString n)
    (a : Fin n → ZMod q) (j : Fin n) (ht : t j = false) :
    xorCoefficient t a j = a j := by
  simp [xorCoefficient, ht]

@[simp] theorem xorCoefficient_apply_true {n q : ℕ} (t : BitString n)
    (a : Fin n → ZMod q) (j : Fin n) (ht : t j = true) :
    xorCoefficient t a j = -a j := by
  simp [xorCoefficient, ht]

/-- Sign change on selected coordinates is an additive equivalence and is its
own inverse. -/
def xorCoefficientEquiv {n q : ℕ} (t : BitString n) :
    (Fin n → ZMod q) ≃+ (Fin n → ZMod q) where
  toFun := xorCoefficient t
  invFun := xorCoefficient t
  left_inv a := by
    funext j
    cases ht : t j <;> simp [xorCoefficient, ht]
  right_inv a := by
    funext j
    cases ht : t j <;> simp [xorCoefficient, ht]
  map_add' a c := by
    funext j
    cases ht : t j <;> simp [xorCoefficient, ht, add_comm]

@[simp] theorem xorCoefficientEquiv_apply {n q : ℕ} (t : BitString n)
    (a : Fin n → ZMod q) :
    xorCoefficientEquiv t a = xorCoefficient t a :=
  rfl

/-- XOR translates the subset sum by the sum on the flipped string and changes
the signs of precisely the flipped coefficients. -/
theorem subsetSum_xorEquiv {n q : ℕ} (a : Fin n → ZMod q)
    (t x : BitString n) :
    subsetSum a (xorEquiv t x) =
      subsetSum (xorCoefficient t a) x + subsetSum a t := by
  simp only [subsetSum, xorEquiv_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases Bool.eq_false_or_eq_true (x j) with hx | hx <;>
    rcases Bool.eq_false_or_eq_true (t j) with ht | ht <;>
    simp [xorCoefficient, hx, ht]

/-- Pulling a fiber back along bitwise XOR shifts its label by the constant
subset sum on the flipped string. -/
theorem preimage_subsetSumFiber_xorEquiv {n q : ℕ}
    (a : Fin n → ZMod q) (t : BitString n) (b : ZMod q) :
    xorEquiv t ⁻¹' subsetSumFiber a b =
      subsetSumFiber (xorCoefficient t a) (b - subsetSum a t) := by
  ext x
  simp only [Set.mem_preimage, mem_subsetSumFiber]
  rw [subsetSum_xorEquiv]
  constructor <;> intro h
  · exact eq_sub_of_add_eq h
  · exact add_eq_of_eq_sub h

/-- Equivalently, XOR sends an old fiber to the translated fiber for the
sign-flipped coefficient vector. -/
theorem image_subsetSumFiber_xorEquiv {n q : ℕ}
    (a : Fin n → ZMod q) (t : BitString n) (b : ZMod q) :
    xorEquiv t '' subsetSumFiber a b =
      subsetSumFiber (xorCoefficient t a) (b - subsetSum a t) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply eq_sub_of_add_eq
    rw [← subsetSum_xorEquiv]
    have hinvol : xorEquiv t (xorEquiv t x) = x := by
      funext j
      simp
    rw [hinvol]
    exact hx
  · intro hy
    refine ⟨xorEquiv t y, ?_, ?_⟩
    calc
      subsetSum a (xorEquiv t y) =
          subsetSum (xorCoefficient t a) y + subsetSum a t :=
        subsetSum_xorEquiv a t y
      _ = (b - subsetSum a t) + subsetSum a t := by rw [hy]
      _ = b := by abel
    funext j
    simp

@[simp] theorem xorEquiv_self {n : ℕ} (t : BitString n) :
    xorEquiv t t = 0 := by
  funext j
  change (t j ^^ t j) = false
  simp

/-- XOR by a string in the `b` fiber sends that entire fiber to the zero fiber. -/
theorem image_subsetSumFiber_xorEquiv_eq_zero_of_mem {n q : ℕ}
    (a : Fin n → ZMod q) (t : BitString n) (b : ZMod q)
    (ht : t ∈ subsetSumFiber a b) :
    xorEquiv t '' subsetSumFiber a b =
      subsetSumFiber (xorCoefficient t a) 0 := by
  rw [image_subsetSumFiber_xorEquiv, ht, sub_self]

/-- Circle-valued form of the translated subset-sum formula. -/
theorem supportPhase_phaseHom_xorEquiv {n q : ℕ} (hq : 0 < q)
    (a : Fin n → ZMod q) (t x : BitString n) :
    supportPhase (phaseHom n q hq a) (xorEquiv t x) =
      zmodPhase q hq (subsetSum a t) +
        supportPhase (phaseHom n q hq (xorCoefficient t a)) x := by
  rw [supportPhase_phaseHom, supportPhase_phaseHom, subsetSum_xorEquiv,
    zmodPhase_add]
  abel

namespace CodeProjector

variable {n K q : ℕ}

/-- A preserving modular phase remains preserving after local-X reindexing and
the corresponding coefficient sign changes. -/
theorem reindex_xor_preserves_phaseHom (C : CodeProjector n K) (hq : 0 < q)
    (a : Fin n → ZMod q) (t : BitString n)
    (hpres : C.Preserves (phaseHom n q hq a)) :
    (C.reindex (xorEquiv t)).Preserves
      (phaseHom n q hq (xorCoefficient t a)) := by
  intro x y hxy
  have hold : C.proj (xorEquiv t x) (xorEquiv t y) ≠ 0 := by
    simpa using hxy
  have hphase := hpres (xorEquiv t x) (xorEquiv t y) hold
  rw [supportPhase_phaseHom_xorEquiv,
    supportPhase_phaseHom_xorEquiv] at hphase
  exact add_left_cancel hphase

end CodeProjector

/-- Reindexing a modular diagonal gate by local bit flips gives the gate with
sign-flipped coefficients, up to the common phase contributed by the flipped
string. -/
theorem reindexOperator_xor_diagonalGate_phaseHom {n q : ℕ} (hq : 0 < q)
    (a : Fin n → ZMod q) (t : BitString n) :
    reindexOperator (xorEquiv t) (diagonalGate (phaseHom n q hq a)) =
      zmodPhaseScalar q hq (subsetSum a t) •
        diagonalGate (phaseHom n q hq (xorCoefficient t a)) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [reindexOperator, Matrix.reindex_apply, Matrix.submatrix_apply,
      xorEquiv_symm, diagonalGate, Matrix.diagonal_apply_eq, Matrix.smul_apply,
      smul_eq_mul]
    rw [supportPhase_phaseHom_xorEquiv]
    simp [zmodPhaseScalar, AddCircle.toCircle_add]
  · have he : xorEquiv t x ≠ xorEquiv t y := (xorEquiv t).injective.ne hxy
    simp [reindexOperator, Matrix.reindex_apply, diagonalGate, hxy, he]

/-- Selected sign changes preserve the exact additive order of a residue vector. -/
theorem addOrderOf_xorCoefficient {n q : ℕ} (t : BitString n)
    (a : Fin n → ZMod q) :
    addOrderOf (xorCoefficient t a) = addOrderOf a := by
  refine addOrderOf_injective
    (xorCoefficientEquiv (q := q) t).toAddMonoidHom ?_ a
  intro u v h
  exact (xorCoefficientEquiv (q := q) t).injective h

theorem xorCoefficient_primitive {n q : ℕ} (t : BitString n)
    (a : Fin n → ZMod q) (ha : addOrderOf a = q) :
    addOrderOf (xorCoefficient t a) = q := by
  rw [addOrderOf_xorCoefficient, ha]

/-- The physical modular diagonal gates before and after selected sign changes
have the same exact matrix order. -/
theorem orderOf_diagonalGate_xorCoefficient {n q : ℕ} (hq : 0 < q)
    (t : BitString n) (a : Fin n → ZMod q) :
    orderOf (diagonalGate (phaseHom n q hq (xorCoefficient t a))) =
      orderOf (diagonalGate (phaseHom n q hq a)) := by
  rw [diagonalGate_order, diagonalGate_order]
  rw [addOrderOf_injective (phaseHom n q hq) (phaseHom_injective n q hq),
    addOrderOf_injective (phaseHom n q hq) (phaseHom_injective n q hq),
    addOrderOf_xorCoefficient]

/-- Reindex a modular coefficient vector along a permutation of physical
coordinates. -/
def permuteCoefficient {n q : ℕ} (sigma : Equiv.Perm (Fin n))
    (a : Fin n → ZMod q) : Fin n → ZMod q :=
  fun j ↦ a (sigma.symm j)

/-- Coordinate reindexing is an additive equivalence on coefficient vectors. -/
def permuteCoefficientEquiv {n q : ℕ} (sigma : Equiv.Perm (Fin n)) :
    (Fin n → ZMod q) ≃+ (Fin n → ZMod q) where
  toFun := permuteCoefficient sigma
  invFun := permuteCoefficient sigma.symm
  left_inv a := by
    funext j
    simp [permuteCoefficient]
  right_inv a := by
    funext j
    simp [permuteCoefficient]
  map_add' a c := by
    funext j
    simp [permuteCoefficient]

@[simp] theorem permuteCoefficientEquiv_apply {n q : ℕ}
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) :
    permuteCoefficientEquiv sigma a = permuteCoefficient sigma a :=
  rfl

/-- Simultaneously permuting the coefficients and the coordinates leaves the
subset sum unchanged. -/
theorem subsetSum_permuteCoefficient_coordinateEquiv {n q : ℕ}
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) (x : BitString n) :
    subsetSum (permuteCoefficient sigma a) (coordinateEquiv sigma x) =
      subsetSum a x := by
  change (∑ j : Fin n, if x (sigma.symm j) then a (sigma.symm j) else 0) =
    ∑ j : Fin n, if x j then a j else 0
  simpa using
    (Equiv.sum_comp sigma.symm (fun j : Fin n ↦ if x j then a j else 0))

/-- Form of coefficient transport matching `reindexOperator`, which evaluates
the old operator at inverse-reindexed basis labels. -/
theorem subsetSum_coordinateEquiv_symm {n q : ℕ}
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) (x : BitString n) :
    subsetSum a ((coordinateEquiv sigma).symm x) =
      subsetSum (permuteCoefficient sigma a) x := by
  have h := subsetSum_permuteCoefficient_coordinateEquiv sigma a
    ((coordinateEquiv sigma).symm x)
  simpa using h.symm

/-- Circle-valued form of coordinate transport. -/
theorem supportPhase_phaseHom_coordinateEquiv_symm {n q : ℕ} (hq : 0 < q)
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q)
    (x : BitString n) :
    supportPhase (phaseHom n q hq a) ((coordinateEquiv sigma).symm x) =
      supportPhase (phaseHom n q hq (permuteCoefficient sigma a)) x := by
  rw [supportPhase_phaseHom, supportPhase_phaseHom,
    subsetSum_coordinateEquiv_symm]

/-- A coordinate permutation sends each fiber to the fiber with permuted
coefficients and the same label. -/
theorem image_subsetSumFiber_coordinateEquiv {n q : ℕ}
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) (b : ZMod q) :
    coordinateEquiv sigma '' subsetSumFiber a b =
      subsetSumFiber (permuteCoefficient sigma a) b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [subsetSum_permuteCoefficient_coordinateEquiv] using hx
  · intro hy
    refine ⟨(coordinateEquiv sigma).symm y, ?_, by simp⟩
    simpa [subsetSum_coordinateEquiv_symm] using hy

namespace CodeProjector

variable {n K q : ℕ}

/-- A preserving modular phase remains preserving after coordinate reindexing
and coefficient permutation. -/
theorem reindex_coordinate_preserves_phaseHom (C : CodeProjector n K)
    (hq : 0 < q) (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a)) :
    (C.reindex (coordinateEquiv sigma)).Preserves
      (phaseHom n q hq (permuteCoefficient sigma a)) := by
  intro x y hxy
  have hold : C.proj ((coordinateEquiv sigma).symm x)
      ((coordinateEquiv sigma).symm y) ≠ 0 := by
    simpa using hxy
  have hphase := hpres ((coordinateEquiv sigma).symm x)
    ((coordinateEquiv sigma).symm y) hold
  rwa [supportPhase_phaseHom_coordinateEquiv_symm,
    supportPhase_phaseHom_coordinateEquiv_symm] at hphase

end CodeProjector

/-- Coordinate reindexing transports a modular diagonal gate exactly to the
gate with permuted coefficients. -/
theorem reindexOperator_coordinate_diagonalGate_phaseHom {n q : ℕ}
    (hq : 0 < q) (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) :
    reindexOperator (coordinateEquiv sigma) (diagonalGate (phaseHom n q hq a)) =
      diagonalGate (phaseHom n q hq (permuteCoefficient sigma a)) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [reindexOperator, Matrix.reindex_apply, Matrix.submatrix_apply,
      diagonalGate, Matrix.diagonal_apply_eq]
    rw [supportPhase_phaseHom, supportPhase_phaseHom,
      subsetSum_coordinateEquiv_symm]
  · have he : (coordinateEquiv sigma).symm x ≠
        (coordinateEquiv sigma).symm y :=
      (coordinateEquiv sigma).symm.injective.ne hxy
    simp [reindexOperator, Matrix.reindex_apply, diagonalGate, hxy, he]

/-- Coordinate permutations preserve the exact additive order of a residue
vector. -/
theorem addOrderOf_permuteCoefficient {n q : ℕ}
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) :
    addOrderOf (permuteCoefficient sigma a) = addOrderOf a := by
  refine addOrderOf_injective
    (permuteCoefficientEquiv (q := q) sigma).toAddMonoidHom ?_ a
  intro u v h
  exact (permuteCoefficientEquiv (q := q) sigma).injective h

theorem permuteCoefficient_primitive {n q : ℕ}
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q)
    (ha : addOrderOf a = q) :
    addOrderOf (permuteCoefficient sigma a) = q := by
  rw [addOrderOf_permuteCoefficient, ha]

/-- The physical modular diagonal gates before and after coordinate permutation
have the same exact matrix order. -/
theorem orderOf_diagonalGate_permuteCoefficient {n q : ℕ} (hq : 0 < q)
    (sigma : Equiv.Perm (Fin n)) (a : Fin n → ZMod q) :
    orderOf (diagonalGate (phaseHom n q hq (permuteCoefficient sigma a))) =
      orderOf (diagonalGate (phaseHom n q hq a)) := by
  rw [diagonalGate_order, diagonalGate_order]
  rw [addOrderOf_injective (phaseHom n q hq) (phaseHom_injective n q hq),
    addOrderOf_injective (phaseHom n q hq) (phaseHom_injective n q hq),
    addOrderOf_permuteCoefficient]

/-- Every modular coefficient vector can be coordinate-permuted so that its
canonical numerators are nondecreasing. -/
theorem exists_permuteCoefficient_monotone_val {n q : ℕ}
    (a : Fin n → ZMod q) :
    ∃ sigma : Equiv.Perm (Fin n),
      Monotone (fun j ↦ (permuteCoefficient sigma a j).val) := by
  let f : Fin n → ℕ := fun j ↦ (a j).val
  refine ⟨(Tuple.sort f).symm, ?_⟩
  simpa [permuteCoefficient, f, Function.comp_def] using Tuple.monotone_sort f

end

end QECC
