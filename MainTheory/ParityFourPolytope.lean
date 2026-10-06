import MainTheory.ParityFourMoments
import MainTheory.LPDimension

/-! The actual affine dimension of the nonnegative parity-four moment polytope. -/

namespace MainTheory.ParityFour

open scoped Matrix BigOperators

noncomputable section

def equationMatrixZ : Matrix (Fin 12) (Fin 16) ℤ :=
  ParityFourMatrix.matrixZ.submatrix (Fin.castAdd 4) id

def equationRightInverseZ : Matrix (Fin 16) (Fin 12) ℤ :=
  ParityFourMatrix.inverseZ.submatrix id (Fin.castAdd 4)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem equationMatrix_scaled_right_inverse :
    equationMatrixZ * equationRightInverseZ = 16 • (1 : Matrix (Fin 12) (Fin 12) ℤ) := by
  decide

def equationMatrix : Matrix (Fin 12) (Fin 16) ℝ := equationMatrixZ.map (Int.castRingHom ℝ)

def equationRhs : Fin 12 → ℝ := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem equationMatrix_rank : equationMatrix.rank = 12 := by
  have hmap : equationMatrix * equationRightInverseZ.map (Int.castRingHom ℝ) =
      16 • (1 : Matrix (Fin 12) (Fin 12) ℝ) := by
    rw [equationMatrix, ← Matrix.map_mul, equationMatrix_scaled_right_inverse]
    ext i j
    by_cases hij : i = j <;>
      norm_num [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply, hij]
  have hmul : equationMatrix * ((1/16 : ℝ) •
      equationRightInverseZ.map (Int.castRingHom ℝ)) = 1 := by
    rw [Matrix.mul_smul, hmap]
    ext i j
    by_cases hij : i = j <;>
      norm_num [Matrix.smul_apply, Matrix.one_apply, Matrix.ofNat_apply, hij]
  have hlo := Matrix.rank_mul_le_left equationMatrix
    ((1/16 : ℝ) • equationRightInverseZ.map (Int.castRingHom ℝ))
  rw [hmul, Matrix.rank_one] at hlo
  have hhi := Matrix.rank_le_height equationMatrix
  norm_num at hlo
  omega

theorem equationMatrix_mulVec_points (p : Cube → ℝ) (r : Fin 12) :
    equationMatrix.mulVec (fun k => p (point k)) r = momentVector p (Fin.castAdd 4 r) := by
  have h := congrFun (matrix_mulVec_points p) (Fin.castAdd 4 r)
  exact h

theorem equation_constraints_iff (p : Cube → ℝ) :
    equationMatrix.mulVec (fun k => p (point k)) = equationRhs ↔ MomentEquations p := by
  constructor
  · intro h
    have he (r : Fin 12) := congrFun h r
    simp only [equationMatrix_mulVec_points] at he
    refine ⟨he 0, he 1, ?_⟩
    intro z hz
    have hm : z = point 0 ∨ (∃ i, z = SS.stdBasis i) ∨ ∃ j, z = pairMask j := by
      have hh : ∀ z : Cube, SS.hammingWt z ≤ 2 →
          z = point 0 ∨ (∃ i, z = SS.stdBasis i) ∨ ∃ j, z = pairMask j := by decide
      exact hh z hz
    have hs : ∀ i : Fin 4, difference p (SS.stdBasis i) = 0 := by
      intro i
      fin_cases i
      · exact he 2
      · exact he 3
      · exact he 4
      · exact he 5
    have hp : ∀ j : Fin 6, difference p (pairMask j) = 0 := by
      intro j
      fin_cases j
      · exact he 6
      · exact he 7
      · exact he 8
      · exact he 9
      · exact he 10
      · exact he 11
    rcases hm with rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
    · have hc (x : Cube) : character (point 0) x = 1 := by
        have hb : ∀ x : Cube, SS.bdot (point 0) x = false := by decide
        simp [character, hb]
      have hf (b) : moment p b (point 0) = mass p b := by
        simp only [moment, hc, mul_one, mass]
      rw [hf, hf, show mass p false = 1 from he 0, show mass p true = 1 from he 1]
    · exact sub_eq_zero.mp (hs i)
    · exact sub_eq_zero.mp (hp j)
  · intro h
    rw [momentEquations_probability p h]
    funext r
    rw [equationMatrix_mulVec_points, probability_momentVector]
    fin_cases r <;> rfl

def momentPolytope : Set (Fin 16 → ℝ) := LPDimension.feasibleSet equationMatrix equationRhs

theorem momentPolytope_iff (p : Cube → ℝ) :
    (fun k => p (point k)) ∈ momentPolytope ↔ (∀ x, 0 ≤ p x) ∧ MomentEquations p := by
  change (_ ∧ _) ↔ _
  rw [equation_constraints_iff]
  constructor
  · rintro ⟨he, hn⟩
    refine ⟨?_, he⟩
    intro x
    obtain ⟨k, rfl⟩ := pointEquiv.surjective x
    exact hn k
  · rintro ⟨hn, he⟩
    exact ⟨he, fun k => hn _⟩

/-- The dimension is the affine-hull dimension of the actual nonnegative LP. -/
theorem momentPolytope_affine_dimension :
    Module.finrank ℝ (affineSpan ℝ momentPolytope).direction = 4 := by
  have he : equationMatrix.mulVec (fun _ => (1/8 : ℝ)) = equationRhs := by
    have h := (equation_constraints_iff (probability (fun _ => 0))).2
      (probability_momentEquations _)
    simpa [probability] using h
  have h := LPDimension.finrank_eq_card_sub_rank_of_positive equationMatrix equationRhs
    (fun _ => (1/8 : ℝ)) he (by intro i; norm_num)
  simpa [momentPolytope, equationMatrix_rank] using h

end
end MainTheory.ParityFour
