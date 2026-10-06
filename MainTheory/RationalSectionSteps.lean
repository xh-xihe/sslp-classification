import QECC.RationalSection

/-! The displayed computations for the specific rational-section witness. -/
namespace MainTheory.RationalSectionSteps

open Matrix
open scoped BigOperators
noncomputable section

theorem cast_num_mulVec_div_den {c : Type*} [Fintype c]
    (G : Matrix c c ℚ) (d : c → ℤ) :
    (fun i => ((G.num *ᵥ d) i : ℝ) / (G.den : ℝ)) =
      G.map ((Rat.castHom ℝ) : ℚ → ℝ) *ᵥ (fun j => (d j : ℝ)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have he : ((G.num i j : ℤ) : ℝ) / (G.den : ℝ) = ((G i j : ℚ) : ℝ) := by
    exact_mod_cast G.num_div_den i j
  rw [← div_mul_eq_mul_div, he]
  rfl

theorem rational_section_chain {c : Type*} [Fintype c] [DecidableEq c]
    (B G : Matrix c c ℚ) (hG : B * G * B = B)
    (t : c → ℝ) (d : c → ℤ)
    (hd : B.map ((Rat.castHom ℝ) : ℚ → ℝ) *ᵥ t = fun j => (d j : ℝ)) :
    let Br := B.map ((Rat.castHom ℝ) : ℚ → ℝ)
    let Gr := G.map ((Rat.castHom ℝ) : ℚ → ℝ)
    let a := G.num *ᵥ d
    Br *ᵥ (fun j => (a j : ℝ) / (G.den : ℝ)) =
        Br *ᵥ (Gr *ᵥ (fun j => (d j : ℝ))) ∧
      Br *ᵥ (Gr *ᵥ (fun j => (d j : ℝ))) = (Br * Gr * Br) *ᵥ t ∧
      (Br * Gr * Br) *ᵥ t = Br *ᵥ t := by
  dsimp only
  refine ⟨congrArg _ (cast_num_mulVec_div_den G d), ?_, ?_⟩
  · rw [← hd, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · have he := congrArg (fun M : Matrix c c ℚ =>
      M.map ((Rat.castHom ℝ) : ℚ → ℝ)) hG
    change (B * G * B).map ((Rat.castHom ℝ) : ℚ → ℝ) =
      B.map ((Rat.castHom ℝ) : ℚ → ℝ) at he
    rw [Matrix.map_mul, Matrix.map_mul] at he
    rw [he]

theorem gram_quadratic_form {r c : Type*} [Fintype r] [Fintype c]
    (A : Matrix r c ℝ) (v : c → ℝ) :
    dotProduct v ((A.transpose * A) *ᵥ v) = ∑ i, (A *ᵥ v) i ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, pow_two]

theorem gram_euclidean_norm {r c : Type*} [Fintype r] [Fintype c]
    (A : Matrix r c ℝ) (v : c → ℝ) :
    dotProduct v ((A.transpose * A) *ᵥ v) =
      ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℝ r)‖ ^ 2 := by
  rw [gram_quadratic_form, EuclideanSpace.norm_sq_eq]
  simp

end
end MainTheory.RationalSectionSteps
