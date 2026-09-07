import MainTheory.ZDetectionHypothesis
import MainTheory.FrameDistanceOne

/-! # From the diagonal quotient's finite lift to a scalar logical matrix power -/

namespace MainTheory.DiagonalLogicalOrder

open CodeSpec ClassificationLevels GlobalClassificationBridge PauliKernelBTrace

noncomputable section

variable {n K : ℕ}

theorem diagonalKernel_one : diagonalKernel (1 : LocalPhase n) = 1 := by
  ext x y
  simp [diagonalKernel, Matrix.one_apply]

theorem diagonalKernel_mul (u v : LocalPhase n) :
    diagonalKernel (u * v) = diagonalKernel u * diagonalKernel v := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [diagonalKernel, Matrix.mul_apply, diagonalValue_mul]
  · simp [diagonalKernel, Matrix.mul_apply, hxy]

theorem diagonalKernel_pow (u : LocalPhase n) (m : ℕ) :
    diagonalKernel (u ^ m) = diagonalKernel u ^ m := by
  induction m with
  | zero => simp [diagonalKernel_one]
  | succ m hm => rw [pow_succ, diagonalKernel_mul, hm, pow_succ]

theorem codePreserving_of_intertwining (F : OrthonormalFrame n K) (u : LocalPhase n)
    (Q : Matrix (Fin K) (Fin K) ℂ) (hQ : diagonalKernel u * frameMatrix F = frameMatrix F * Q) :
    CodePreserving F (diagonalEnd u) := by
  classical
  intro phi hphi
  induction hphi using Submodule.span_induction with
  | mem phi hphi =>
    obtain ⟨k, rfl⟩ := hphi
    have hk : diagonalAction u (F.vec k) = ∑ l, Q l k • F.vec l := by
      rw [← kernelAction_diagonalKernel]
      funext x
      simpa only [Matrix.mul_apply, frameMatrix, kernelAction, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun (congrFun hQ x) k
    change diagonalAction u (F.vec k) ∈ codeSpan F
    rw [hk]
    apply Submodule.sum_mem
    intro l _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  | zero =>
    change (diagonalEnd u) 0 ∈ codeSpan F
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (codeSpan F).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (codeSpan F).smul_mem c ih

theorem symmetry_of_intertwining (F : OrthonormalFrame n K) (u : LocalPhase n)
    (Q : Matrix (Fin K) (Fin K) ℂ) (hQU : Q * Q.conjTranspose = 1)
    (hQ : diagonalKernel u * frameMatrix F = frameMatrix F * Q) :
    PreservesProjectorRange (CodeProjector.ofFrame F) u := by
  have hD : diagonalKernel u⁻¹ * diagonalKernel u = 1 := by
    rw [← diagonalKernel_mul, inv_mul_cancel, diagonalKernel_one]
  have hinv : diagonalKernel u⁻¹ * frameMatrix F = frameMatrix F * Q.conjTranspose := by
    calc
      _ = diagonalKernel u⁻¹ * (frameMatrix F * Q) * Q.conjTranspose := by
        simp only [Matrix.mul_assoc, hQU, Matrix.mul_one]
      _ = frameMatrix F * Q.conjTranspose := by
        rw [← hQ, ← Matrix.mul_assoc, hD, Matrix.one_mul]
  constructor
  · intro phi hphi
    exact (inProjectorRange_ofFrame_iff F _).2
      (codePreserving_of_intertwining F u Q hQ phi ((inProjectorRange_ofFrame_iff F _).1 hphi))
  · intro phi hphi
    exact (inProjectorRange_ofFrame_iff F _).2
      (codePreserving_of_intertwining F u⁻¹ Q.conjTranspose hinv phi
        ((inProjectorRange_ofFrame_iff F _).1 hphi))

theorem intertwining_pow (F : OrthonormalFrame n K) (u : LocalPhase n)
    (Q : Matrix (Fin K) (Fin K) ℂ) (hQ : diagonalKernel u * frameMatrix F = frameMatrix F * Q)
    (m : ℕ) : diagonalKernel (u ^ m) * frameMatrix F = frameMatrix F * Q ^ m := by
  rw [diagonalKernel_pow]
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ, Matrix.mul_assoc, hQ, ← Matrix.mul_assoc, hm, Matrix.mul_assoc, ← pow_succ]

/-- Every logical matrix realized by a diagonal symmetry of a code detecting
the `Z_j` has a uniformly bounded positive power that is scalar. -/
theorem exists_bounded_scalar_power (F : OrthonormalFrame n K) (hK : 0 < K)
    (hZ : ZDetection.ZDetectsFrame F) (u : LocalPhase n)
    (Q : Matrix (Fin K) (Fin K) ℂ) (hQU : Q * Q.conjTranspose = 1)
    (hQ : diagonalKernel u * frameMatrix F = frameMatrix F * Q) :
    ∃ m : ℕ, 0 < m ∧ m ≤ BetaExists.betaOf (n + K - 1) ∧ ∃ c : ℂ, Q ^ m = c • 1 := by
  let C := FrameDistanceOne.codeOfFrame F hK
  let v : diagonalSymmetryGroup (exactCodeProjector C) := ⟨u, symmetry_of_intertwining F u Q hQU hQ⟩
  let g := intrinsicClass (exactCodeProjector C) v
  have hex : ∃ m : ℕ, 0 < m ∧ m ≤ BetaExists.betaOf (n + K - 1) ∧ g ^ m = 1 := by
    by_cases hg : g = 1
    · exact ⟨1, by omega, BetaExists.betaOf_pos _, by simp [hg]⟩
    · obtain ⟨q, _, _, hm, hmq, _, hqB⟩ :=
        ZDetection.quantitative_projective_group_of_zDetects (BetaExists.betaBound_betaOf _)
          C hZ g hg
      exact ⟨orderOf g, by omega, hmq.trans hqB, pow_orderOf_eq_one g⟩
  obtain ⟨m, hm, hmB, hgm⟩ := hex
  have htriv : IsProjectivelyTrivial (exactCodeProjector C) (v ^ m) := by
    apply (intrinsicClass_eq_one_iff _ _).1
    change g ^ m = 1
    exact hgm
  obtain ⟨c, _, hc⟩ := htriv
  have hscalar : diagonalKernel (u ^ m) * frameMatrix F = c • frameMatrix F := by
    ext x k
    have hk := hc (F.vec k) (by
      change kernelAction (CodeProjector.ofFrame F).kernel (F.vec k) = F.vec k
      rw [kernelAction_ofFrame, projectorAction_vec])
    change diagonalAction (u ^ m) (F.vec k) = c • F.vec k at hk
    rw [← kernelAction_diagonalKernel] at hk
    simpa only [Matrix.mul_apply, frameMatrix, kernelAction, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul] using congrFun hk x
  have h := congrArg (fun M => (frameMatrix F).conjTranspose * M) hscalar
  dsimp only at h
  rw [intertwining_pow F u Q hQ m, ← Matrix.mul_assoc, KLCodeBridge.frameMatrix_gram,
    Matrix.one_mul, Matrix.mul_smul, KLCodeBridge.frameMatrix_gram] at h
  exact ⟨m, hm, hmB, c, h⟩

end

end MainTheory.DiagonalLogicalOrder
