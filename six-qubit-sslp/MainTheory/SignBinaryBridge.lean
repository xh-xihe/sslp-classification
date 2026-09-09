import MainTheory.BinaryBeta

/-! The bordered sign matrix and the actual sharp binary inverse denominator. -/

namespace MainTheory.SignBinaryBridge

open Matrix SharpClearing BinaryBeta
open scoped BigOperators

def signLiftBlock {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℤ :=
  Matrix.fromBlocks 1 (fun _ _ => 1) (fun _ _ => 1) (fun i j => 1 - 2 * C i j)

def borderEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n+1) :=
  finSumFinEquiv.trans (finCongr (Nat.one_add n))

def signLift {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
  Matrix.reindex (borderEquiv n) (borderEquiv n) (signLiftBlock C)

theorem det_signLiftBlock {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) :
    (signLiftBlock C).det = (-2 : ℤ)^n * C.det := by
  rw [signLiftBlock, Matrix.det_fromBlocks_one₁₁]
  have he : (fun i j => 1 - 2 * C i j) -
      (fun (_ : Fin n) (_ : Fin 1) => (1 : ℤ)) * (fun _ (_ : Fin n) => (1 : ℤ)) =
      (-2 : ℤ) • C := by
    ext i j
    change (1 - 2 * C i j) - (∑ _ : Fin 1, (1 : ℤ) * 1) = -2 * C i j
    simp only [Fin.sum_univ_one, mul_one]
    ring
  rw [he, Matrix.det_smul, Fintype.card_fin]

theorem det_signLift {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) :
    (signLift C).det = (-2 : ℤ)^n * C.det := by
  rw [signLift, Matrix.det_reindex_self, det_signLiftBlock]

theorem signLift_isSign {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (hC : IsZeroOne C) :
    ∀ i j, signLift C i j = 1 ∨ signLift C i j = -1 := by
  intro i j
  change signLiftBlock C ((borderEquiv n).symm i) ((borderEquiv n).symm j) = 1 ∨
    signLiftBlock C ((borderEquiv n).symm i) ((borderEquiv n).symm j) = -1
  generalize (borderEquiv n).symm i = a
  generalize (borderEquiv n).symm j = b
  rcases a with a | a <;> rcases b with b | b
  · left; simp [signLiftBlock, Subsingleton.elim a b]
  · left; rfl
  · left; rfl
  · rcases hC a b with h | h <;> simp [signLiftBlock, h]

theorem cleared_binary_of_block {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (J : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℤ) (q : ℤ)
    (hJ : signLiftBlock C * J = (2*q) • 1) :
    C * (-J.submatrix Sum.inr Sum.inr) = q • 1 := by
  ext i j
  have h0 := congrArg (fun M => M (Sum.inl 0) (Sum.inr j)) hJ
  have h1 := congrArg (fun M => M (Sum.inr i) (Sum.inr j)) hJ
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_one,
    signLiftBlock, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Sum.inr.injEq, reduceCtorEq, ↓reduceIte, one_mul, mul_zero] at h0 h1
  have hs : (∑ l, (1 - 2 * C i l) * J (Sum.inr l) (Sum.inr j)) =
      (∑ l, J (Sum.inr l) (Sum.inr j)) - 2 * ∑ l, C i l * J (Sum.inr l) (Sum.inr j) := by
    simp_rw [sub_mul, one_mul, mul_assoc]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hs] at h1
  simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.submatrix_apply,
    mul_neg, Finset.sum_neg_distrib, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  nlinarith

theorem cleared_binary_of_signLift {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (J : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (q : ℤ)
    (hJ : signLift C * J = (2*q) • 1) :
    ∃ B : Matrix (Fin n) (Fin n) ℤ, C * B = q • 1 := by
  let e := borderEquiv n
  have h := congrArg (fun M => M.submatrix e e) hJ
  have he : signLift C = (signLiftBlock C).submatrix e.symm e.symm := rfl
  dsimp only at h
  rw [he, ← Matrix.submatrix_mul_equiv _ _ e e e] at h
  have hr : ((2*q) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)).submatrix e e =
      (2*q) • (1 : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℤ) := by
    ext i j
    change (2*q) * (if e i = e j then 1 else 0) = (2*q) * (if i = j then 1 else 0)
    simp only [e.injective.eq_iff]
  rw [hr] at h
  have hb : signLiftBlock C * J.submatrix e e = (2*q) • 1 := by
    simpa only [Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] using h
  exact ⟨_, cleared_binary_of_block C _ q hb⟩

end MainTheory.SignBinaryBridge
