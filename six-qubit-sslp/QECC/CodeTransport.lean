import QECC.FirstTheorem

namespace QECC

noncomputable section

/-- Relabel computational-basis strings by bitwise XOR with `t`. -/
def xorEquiv {n : ℕ} (t : BitString n) : BitString n ≃ BitString n where
  toFun x := fun j => x j ^^ t j
  invFun x := fun j => x j ^^ t j
  left_inv x := by
    funext j
    simp
  right_inv x := by
    funext j
    simp

@[simp] theorem xorEquiv_apply {n : ℕ} (t x : BitString n) (j : Fin n) :
    xorEquiv t x j = (x j ^^ t j) := rfl

@[simp] theorem xorEquiv_symm {n : ℕ} (t : BitString n) :
    (xorEquiv t).symm = xorEquiv t := by
  ext x j
  rfl

/-- Relabel bit strings by a permutation of their coordinates. -/
def coordinateEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) : BitString n ≃ BitString n where
  toFun x := fun j => x (σ.symm j)
  invFun x := fun j => x (σ j)
  left_inv x := by
    funext j
    simp
  right_inv x := by
    funext j
    simp

@[simp] theorem coordinateEquiv_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : BitString n) (j : Fin n) :
    coordinateEquiv σ x j = x (σ.symm j) := rfl

/-- Reindex an operator along a computational-basis equivalence. -/
def reindexOperator {n : ℕ} (e : BitString n ≃ BitString n) (A : Operator n) : Operator n :=
  Matrix.reindex e e A

namespace CodeProjector

variable {n K : ℕ}

/-- Transport a code projector along a permutation of the computational basis. -/
def reindex (C : CodeProjector n K) (e : BitString n ≃ BitString n) :
    CodeProjector n K where
  proj := reindexOperator e C.proj
  hermitian := by
    change (Matrix.reindex e e C.proj).conjTranspose = Matrix.reindex e e C.proj
    rw [Matrix.conjTranspose_reindex, C.hermitian]
  idempotent := by
    change (Matrix.reindexAlgEquiv ℂ ℂ e) C.proj *
      (Matrix.reindexAlgEquiv ℂ ℂ e) C.proj =
      (Matrix.reindexAlgEquiv ℂ ℂ e) C.proj
    rw [← map_mul, C.idempotent]
  rank_eq := by
    change Matrix.rank (Matrix.reindex e e C.proj) = K
    rw [Matrix.rank_reindex]
    exact C.rank_eq

@[simp] theorem reindex_proj_apply (C : CodeProjector n K)
    (e : BitString n ≃ BitString n) (x y : BitString n) :
    (C.reindex e).proj x y = C.proj (e.symm x) (e.symm y) := rfl

@[simp] theorem reindex_refl (C : CodeProjector n K) :
    C.reindex (Equiv.refl _) = C := by
  cases C
  rfl

end CodeProjector

end

end QECC
