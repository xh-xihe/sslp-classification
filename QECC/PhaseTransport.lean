import QECC.CodeTransport

namespace QECC

open scoped BigOperators

noncomputable section

/-- Sign change of circle-valued physical phases under a local bit flip. -/
def xorPhase {n : ℕ} (t : BitString n) (theta : PhaseVector n) :
    PhaseVector n :=
  fun j => if t j then -theta j else theta j

/-- Selected phase sign changes form an additive equivalence and are
involutive. -/
def xorPhaseEquiv {n : ℕ} (t : BitString n) :
    PhaseVector n ≃+ PhaseVector n where
  toFun := xorPhase t
  invFun := xorPhase t
  left_inv theta := by
    funext j
    cases ht : t j <;> simp [xorPhase, ht]
  right_inv theta := by
    funext j
    cases ht : t j <;> simp [xorPhase, ht]
  map_add' theta phi := by
    funext j
    cases ht : t j <;> simp [xorPhase, ht, add_comm]

@[simp] theorem xorPhaseEquiv_apply {n : ℕ} (t : BitString n)
    (theta : PhaseVector n) :
    xorPhaseEquiv t theta = xorPhase t theta :=
  rfl

@[simp] theorem xorPhase_involutive {n : ℕ} (t : BitString n)
    (theta : PhaseVector n) :
    xorPhase t (xorPhase t theta) = theta :=
  (xorPhaseEquiv t).left_inv theta

/-- Relabelling a bit string by XOR adds the phase on the translating string
and changes the signs of the selected physical coordinates. -/
theorem supportPhase_xorEquiv {n : ℕ} (theta : PhaseVector n)
    (t x : BitString n) :
    supportPhase theta (xorEquiv t x) =
      supportPhase theta t + supportPhase (xorPhase t theta) x := by
  simp only [supportPhase, xorEquiv_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases Bool.eq_false_or_eq_true (x j) with hx | hx <;>
    rcases Bool.eq_false_or_eq_true (t j) with ht | ht <;>
    simp [xorPhase, hx, ht]

/-- Local-X reindexing conjugates a diagonal gate to the sign-changed phase
vector, up to the common phase contributed by the translating string. -/
theorem reindexOperator_xor_diagonalGate {n : ℕ}
    (theta : PhaseVector n) (t : BitString n) :
    reindexOperator (xorEquiv t) (diagonalGate theta) =
      (((supportPhase theta t).toCircle : Circle) : ℂ) •
        diagonalGate (xorPhase t theta) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [reindexOperator, Matrix.reindex_apply, Matrix.submatrix_apply,
      xorEquiv_symm, diagonalGate, Matrix.diagonal_apply_eq,
      Matrix.smul_apply, smul_eq_mul]
    rw [supportPhase_xorEquiv]
    simp [AddCircle.toCircle_add]
  · have he : xorEquiv t x ≠ xorEquiv t y :=
      (xorEquiv t).injective.ne hxy
    simp [reindexOperator, Matrix.reindex_apply, diagonalGate, hxy, he]

/-- Selected phase sign changes preserve exact additive order. -/
theorem addOrderOf_xorPhase {n : ℕ} (t : BitString n)
    (theta : PhaseVector n) :
    addOrderOf (xorPhase t theta) = addOrderOf theta := by
  refine addOrderOf_injective (xorPhaseEquiv t).toAddMonoidHom ?_ theta
  intro u v h
  exact (xorPhaseEquiv t).injective h

/-- Consequently, local-X sign changes preserve exact physical gate order. -/
theorem orderOf_diagonalGate_xorPhase {n : ℕ} (t : BitString n)
    (theta : PhaseVector n) :
    orderOf (diagonalGate (xorPhase t theta)) =
      orderOf (diagonalGate theta) := by
  rw [diagonalGate_order, diagonalGate_order, addOrderOf_xorPhase]

namespace CodeProjector

variable {n K : ℕ}

/-- Reindexing twice by the same local bit flip returns the original code. -/
@[simp] theorem reindex_xor_involutive (C : CodeProjector n K)
    (t : BitString n) :
    (C.reindex (xorEquiv t)).reindex (xorEquiv t) = C := by
  cases C
  rw [CodeProjector.mk.injEq]
  ext x y
  simp [reindex, reindexOperator, Matrix.reindex_apply, xorEquiv]

/-- A preserving circle-valued phase remains preserving after local-X
reindexing and the corresponding coordinate sign changes. -/
theorem reindex_xor_preserves (C : CodeProjector n K)
    (theta : PhaseVector n) (t : BitString n)
    (hpres : C.Preserves theta) :
    (C.reindex (xorEquiv t)).Preserves (xorPhase t theta) := by
  intro x y hxy
  have hold : C.proj (xorEquiv t x) (xorEquiv t y) ≠ 0 := by
    simpa using hxy
  have hphase := hpres (xorEquiv t x) (xorEquiv t y) hold
  rw [supportPhase_xorEquiv, supportPhase_xorEquiv] at hphase
  exact add_left_cancel hphase

/-- Preservation is equivalent before and after local-X reindexing. -/
theorem reindex_xor_preserves_iff (C : CodeProjector n K)
    (theta : PhaseVector n) (t : BitString n) :
    (C.reindex (xorEquiv t)).Preserves (xorPhase t theta) ↔
      C.Preserves theta := by
  constructor
  · intro h
    have hback := (C.reindex (xorEquiv t)).reindex_xor_preserves
      (xorPhase t theta) t h
    simpa using hback
  · exact fun h => C.reindex_xor_preserves theta t h

/-- A scalar logical action remains scalar after local-X reindexing. -/
theorem reindex_xor_actsAsScalar (C : CodeProjector n K)
    (theta : PhaseVector n) (t : BitString n)
    (hscalar : C.ActsAsScalar theta) :
    (C.reindex (xorEquiv t)).ActsAsScalar (xorPhase t theta) := by
  obtain ⟨c, hc⟩ := hscalar
  refine ⟨c - supportPhase theta t, fun x y hxy => ?_⟩
  have hold : C.proj (xorEquiv t x) (xorEquiv t y) ≠ 0 := by
    simpa using hxy
  have hx := hc (xorEquiv t x) (xorEquiv t y) hold
  rw [supportPhase_xorEquiv] at hx
  rw [← hx]
  abel

/-- Scalar logical action is equivalent before and after local-X
reindexing. -/
theorem reindex_xor_actsAsScalar_iff (C : CodeProjector n K)
    (theta : PhaseVector n) (t : BitString n) :
    (C.reindex (xorEquiv t)).ActsAsScalar (xorPhase t theta) ↔
      C.ActsAsScalar theta := by
  constructor
  · intro h
    have hback := (C.reindex (xorEquiv t)).reindex_xor_actsAsScalar
      (xorPhase t theta) t h
    simpa using hback
  · exact fun h => C.reindex_xor_actsAsScalar theta t h

end CodeProjector

end

end QECC
