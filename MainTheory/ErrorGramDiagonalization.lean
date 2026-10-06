import MainTheory.FiniteKrausChannel

/-! # Diagonalizing the actual Knill--Laflamme error Gram matrix -/

namespace MainTheory.ErrorGramDiagonalization

open FiniteKrausChannel
open scoped ComplexOrder

noncomputable section

variable {I H L : Type*} [Fintype I] [Fintype H] [Fintype L]
  [DecidableEq I] [DecidableEq L]

set_option linter.unusedSectionVars false

def mix (U : Matrix I I ℂ) (F : I → Matrix H L ℂ) : I → Matrix H L ℂ :=
  fun i => ∑ j, U j i • F j

theorem mix_gram (U : Matrix I I ℂ) (F : I → Matrix H L ℂ) (c : Matrix I I ℂ)
    (hF : ∀ i j, (F i).conjTranspose * F j = c i j • 1) (i j : I) :
    (mix U F i).conjTranspose * mix U F j = (U.conjTranspose * c * U) i j • 1 := by
  simp only [mix, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, hF, smul_smul]
  ext k l
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases hkl : k = l
  · subst l
    simp only [if_true, mul_one, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  · simp [hkl]

theorem action_mix (U : Matrix I I ℂ) (hU : U * U.conjTranspose = 1)
    (F : I → Matrix H L ℂ) (X : Matrix L L ℂ) :
    action (mix U F) X = action F X := by
  classical
  have hrow (j k : I) : (∑ i, U j i * star (U k i)) = if j = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrFun (congrFun hU j) k
  calc
    action (mix U F) X = ∑ i, ∑ j, ∑ k,
        (U j i * star (U k i)) • (F j * X * (F k).conjTranspose) := by
      simp only [action, mix, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
        Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
        Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_comm]
    _ = ∑ j, ∑ k, (∑ i, U j i * star (U k i)) • (F j * X * (F k).conjTranspose) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = action F X := by simp only [hrow]; simp [action]

theorem gram_posSemidef [Nonempty L] (F : I → Matrix H L ℂ) (c : Matrix I I ℂ)
    (hF : ∀ i j, (F i).conjTranspose * F j = c i j • 1) : c.PosSemidef := by
  let k : L := Classical.choice inferInstance
  let M : Matrix H I ℂ := fun x i => F i x k
  have hc : c = M.conjTranspose * M := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, M] using
      (congrFun (congrFun (hF i j) k) k).symm
  rw [hc]
  exact Matrix.posSemidef_conjTranspose_mul_self M

/-- A unitary change of Kraus labels makes the actual error images mutually
orthogonal, with nonnegative squared lengths given by the KL eigenvalues. -/
theorem exists_diagonal_errors [Nonempty L]
    (F : I → Matrix H L ℂ) (c : Matrix I I ℂ)
    (hF : ∀ i j, (F i).conjTranspose * F j = c i j • 1) :
    ∃ U : Matrix I I ℂ, ∃ w : I → ℝ,
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      (∀ i, 0 ≤ w i) ∧
      (∀ i j, (mix U F i).conjTranspose * mix U F j =
        if i = j then (w i : ℂ) • 1 else 0) ∧
      (∀ X, action (mix U F) X = action F X) := by
  have hc := gram_posSemidef F c hF
  let U : Matrix I I ℂ := hc.isHermitian.eigenvectorUnitary
  have hU : U.conjTranspose * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * U.conjTranspose = 1 := Unitary.coe_mul_star_self _
  have hd : U.conjTranspose * c * U = Matrix.diagonal (fun i => (hc.isHermitian.eigenvalues i : ℂ)) := by
    simpa only [Unitary.conjStarAlgAut_star_apply, U, Function.comp_apply] using
      hc.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  refine ⟨U, hc.isHermitian.eigenvalues, hU, hU', hc.eigenvalues_nonneg, ?_, action_mix U hU' F⟩
  intro i j
  rw [mix_gram U F c hF, hd]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

end

end MainTheory.ErrorGramDiagonalization
