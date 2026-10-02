import MainTheory.DiagonalLogicalOrder
import MainTheory.DiagonalLocalKernel

/-! # Actual logical matrices and classes in the intrinsic diagonal quotient -/

namespace MainTheory.DiagonalLogicalMatrixBridge

open CodeSpec ClassificationLevels GlobalClassificationBridge PauliKernelBTrace
open DiagonalLogicalOrder LocalTensorKernel

noncomputable section

set_option maxHeartbeats 1000000

variable {n K d : ℕ}

theorem logicalMatrix_unitary (F : OrthonormalFrame n K) (u : LocalPhase n)
    (Q : Matrix (Fin K) (Fin K) ℂ)
    (hQ : diagonalKernel u * frameMatrix F = frameMatrix F * Q) :
    Q.conjTranspose * Q = 1 ∧ Q * Q.conjTranspose = 1 := by
  have hD : (diagonalKernel u).conjTranspose * diagonalKernel u = 1 := by
    rw [← DiagonalLocalKernel.tensor_diagonal]
    exact (tensorKernel_unitary _ (DiagonalLocalKernel.local_unitary u)).1
  have hleft : Q.conjTranspose * Q = 1 := by
    calc
      _ = (frameMatrix F * Q).conjTranspose * (frameMatrix F * Q) := by
        simp only [Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
        rw [Matrix.mul_assoc Q.conjTranspose, KLCodeBridge.frameMatrix_gram,
          Matrix.mul_one]
      _ = (diagonalKernel u * frameMatrix F).conjTranspose *
          (diagonalKernel u * frameMatrix F) := by rw [hQ]
      _ = 1 := by
        simp only [Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
        rw [Matrix.mul_assoc (frameMatrix F).conjTranspose, hD, Matrix.mul_one,
          KLCodeBridge.frameMatrix_gram]
  exact ⟨hleft, mul_eq_one_comm.1 hleft⟩

theorem projectivelyTrivial_iff_scalar (F : OrthonormalFrame n K)
    (v : diagonalSymmetryGroup (CodeProjector.ofFrame F)) (Q : Matrix (Fin K) (Fin K) ℂ)
    (hQ : diagonalKernel v.val * frameMatrix F = frameMatrix F * Q) :
    IsProjectivelyTrivial (CodeProjector.ofFrame F) v ↔
      ∃ c : ℂ, c ≠ 0 ∧ Q = c • 1 := by
  rw [isProjectivelyTrivial_iff_sameProjectiveOnCode, sameProjectiveOnCode_iff_frame]
  constructor
  · rintro ⟨c, hc, hframe⟩
    have hscalar : diagonalKernel v.val * frameMatrix F = c • frameMatrix F := by
      ext x k
      have hk := congrFun (hframe k) x
      simpa [diagonalEnd_apply, diagonalAction, Matrix.mul_apply,
        diagonalKernel, frameMatrix] using hk
    have h := congrArg (fun M => (frameMatrix F).conjTranspose * M) hscalar
    dsimp only at h
    rw [hQ, ← Matrix.mul_assoc, KLCodeBridge.frameMatrix_gram, Matrix.one_mul,
      Matrix.mul_smul, KLCodeBridge.frameMatrix_gram] at h
    exact ⟨c, hc, h⟩
  · rintro ⟨c, hc, hscalar⟩
    refine ⟨c, hc, fun k => ?_⟩
    have h := hQ
    rw [hscalar, Matrix.mul_smul, Matrix.mul_one] at h
    funext x
    have hx := congrFun (congrFun h x) k
    simpa [diagonalEnd_apply, diagonalAction, Matrix.mul_apply, diagonalKernel,
      frameMatrix] using hx

/-- A non-scalar fifth root of a nonzero scalar supplies an order-five quotient element. -/
theorem exists_intrinsic_order_five (C : ExactCode n K d) (u : LocalPhase n)
    (Q : Matrix (Fin K) (Fin K) ℂ)
    (hQ : diagonalKernel u * frameMatrix C.frame = frameMatrix C.frame * Q)
    (hfive : ∃ c : ℂ, c ≠ 0 ∧ Q ^ 5 = c • 1)
    (hnonscalar : ¬ ∃ c : ℂ, Q = c • 1) :
    ∃ g : IntrinsicGroup C, orderOf g = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let v : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame) :=
    ⟨u, symmetry_of_intertwining C.frame u Q (logicalMatrix_unitary C.frame u Q hQ).2 hQ⟩
  let g : IntrinsicGroup C := intrinsicClass (CodeProjector.ofFrame C.frame) v
  refine ⟨g, orderOf_eq_prime ?_ ?_⟩
  · change intrinsicClass (CodeProjector.ofFrame C.frame) (v ^ 5) = 1
    apply (intrinsicClass_eq_one_iff _ _).2
    have hp : diagonalKernel (v ^ 5).val * frameMatrix C.frame = frameMatrix C.frame * Q ^ 5 := by
      simpa only [Subgroup.coe_pow] using intertwining_pow C.frame v.val Q hQ 5
    apply (projectivelyTrivial_iff_scalar C.frame (v ^ 5) (Q ^ 5) hp).2
    exact hfive
  · intro hg
    have ht := (intrinsicClass_eq_one_iff _ _).1 hg
    obtain ⟨c, _, hc⟩ := (projectivelyTrivial_iff_scalar C.frame v Q hQ).1 ht
    exact hnonscalar ⟨c, hc⟩

end

end MainTheory.DiagonalLogicalMatrixBridge
