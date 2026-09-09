import MainTheory.TwoSpinorNormalization

set_option autoImplicit false

namespace MainTheory.TwoSpinorNormalization

theorem standard_form (u v : Vec)
    (hu : Complex.normSq (u 0) + Complex.normSq (u 1) = 1)
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = 1) :
    ∃ (T : Mat) (lambda : ℂ) (c : ℝ),
      T * T.conjTranspose = 1 ∧ T.conjTranspose * T = 1 ∧
      Complex.normSq lambda = 1 ∧ 0 ≤ c ∧ c ≤ 1 ∧
      (fun i => lambda * (T.mulVec u i)) = ![1,0] ∧
      T.mulVec v = ![(c : ℂ),(Real.sqrt (1-c^2) : ℂ)] := by
  let Q := basisMatrix u
  let w := Q.mulVec v
  obtain ⟨a,ha,haw⟩ := exists_phase_correction (w 0)
  obtain ⟨b,hb,hbw⟩ := exists_phase_correction (w 1)
  let D : Mat := Matrix.diagonal ![a,b]
  let T : Mat := D * Q
  have hQ : Q * Q.conjTranspose = 1 := basis_unitary u hu
  have hD : D * D.conjTranspose = 1 := diagonal_unitary a b ha hb
  have hT : T * T.conjTranspose = 1 := by
    dsimp only [T]
    rw [Matrix.conjTranspose_mul]
    calc
      (D*Q)*(Q.conjTranspose*D.conjTranspose) =
        D*(Q*Q.conjTranspose)*D.conjTranspose := by noncomm_ring
      _ = 1 := by rw [hQ,Matrix.mul_one,hD]
  have hn : ‖w 0‖^2 + ‖w 1‖^2 = 1 := by
    simpa only [Complex.normSq_eq_norm_sq] using basis_preserves_norm u v hu hv
  have hc0 : 0 ≤ ‖w 0‖ := norm_nonneg _
  have hc1 : ‖w 0‖ ≤ 1 := by nlinarith [sq_nonneg ‖w 1‖]
  have hr : Real.sqrt (1-‖w 0‖^2) = ‖w 1‖ := by
    rw [show 1-‖w 0‖^2 = ‖w 1‖^2 by linarith,Real.sqrt_sq (norm_nonneg _)]
  refine ⟨T,star a,‖w 0‖,hT,mul_eq_one_comm.mp hT,?_,hc0,hc1,?_,?_⟩
  · simpa using ha
  · have hQu : Q.mulVec u = ![1,0] := basis_sends_first u hu
    funext i
    dsimp only [T]
    rw [← Matrix.mulVec_mulVec,hQu]
    fin_cases i <;> simp [D,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    change star a * a = 1
    rw [SixQubit.star_mul_self,ha]
    rfl
  · change (D*Q).mulVec v = _
    rw [← Matrix.mulVec_mulVec]
    change D.mulVec w = _
    rw [hr]
    funext i
    fin_cases i
    · simpa [D,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using haw
    · simpa [D,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using hbw

end MainTheory.TwoSpinorNormalization
