import Mathlib

/-! # A six-dimensional Gram matrix with at most two active coordinates -/

namespace SixQubit.Orbit8RaisingGram

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

def normalMatrix (u : Fin 6 → ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => (if i = j then (1/2 : ℂ) - 6 * (Complex.normSq (u i) : ℂ) else 0)
    + 3 * u i * star (u j)

def reflected (u : Fin 6 → ℂ) (a : Fin 6) : Fin 6 → ℂ :=
  fun i => if i = a then u i else -u i

private theorem outside_pair_product_zero (u : Fin 6 → ℂ)
    (hcard : (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ 2)
    (a i j : Fin 6) (ha : u a ≠ 0) (hi : i ≠ a) (hj : j ≠ a) (hij : i ≠ j) :
    u i = 0 ∨ u j = 0 := by
  by_contra h
  push_neg at h
  have hsub : ({a, i, j} : Finset (Fin 6)) ⊆
      Finset.univ.filter (fun k => u k ≠ 0) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl <;> simp [ha, h.1, h.2]
  have hle := Finset.card_le_card hsub
  have hthree : ({a, i, j} : Finset (Fin 6)).card = 3 := by
    simp [hij, Ne.symm hi, Ne.symm hj]
  omega

/-- A sign change at the non-anchor active coordinate turns the diagonal
correction into one rank-one matrix. -/
theorem normalMatrix_eq_rank_one (u : Fin 6 → ℂ)
    (hcard : (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ 2)
    (a : Fin 6) (ha : u a ≠ 0) :
    normalMatrix u = (1/2 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) -
      (3 : ℂ) • Matrix.vecMulVec (reflected u a) (fun i => star (reflected u a i)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = a <;>
      simp only [normalMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.vecMulVec_apply, Matrix.one_apply]
    all_goals simp [reflected, hi, star_neg]
    all_goals have hn : (starRingEnd ℂ) (u i) * u i = (Complex.normSq (u i) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    all_goals simp only [hi] at hn
    all_goals linear_combination (6 : ℂ) * hn
  · by_cases hi : i = a
    · subst i
      simp [normalMatrix, Matrix.smul_apply, Matrix.vecMulVec_apply, reflected,
        hij, Ne.symm hij]
      ring
    · by_cases hj : j = a
      · subst j
        simp [normalMatrix, Matrix.smul_apply, Matrix.vecMulVec_apply, reflected,
          hi]
        ring
      · rcases outside_pair_product_zero u hcard a i j ha hi hj hij with hz | hz <;>
          simp [normalMatrix, Matrix.smul_apply, Matrix.vecMulVec_apply, reflected,
            hij, hi, hj, hz]

theorem reflected_mass (u : Fin 6 → ℂ) (a : Fin 6) :
    (∑ i, Complex.normSq (reflected u a i)) = ∑ i, Complex.normSq (u i) := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = a <;> simp [reflected, hi]

private theorem outer_square (v : Fin 6 → ℂ)
    (hmass : (∑ i, Complex.normSq (v i)) = (1/6 : ℝ)) :
    Matrix.vecMulVec v (fun i => star (v i)) *
      Matrix.vecMulVec v (fun i => star (v i)) =
        (1/6 : ℂ) • Matrix.vecMulVec v (fun i => star (v i)) := by
  have hdot : (∑ i, star (v i) * v i) = (1/6 : ℂ) := by
    calc
      _ = ∑ i, (Complex.normSq (v i) : ℂ) :=
        Finset.sum_congr rfl fun i _ => Complex.normSq_eq_conj_mul_self.symm
      _ = _ := by rw [← Complex.ofReal_sum, hmass]; norm_num
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    _ = v i * (∑ k, star (v k) * v k) * star (v j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hdot]; ring

theorem rank_one_complement_square (v : Fin 6 → ℂ)
    (hmass : (∑ i, Complex.normSq (v i)) = (1/6 : ℝ)) :
    let G := (1/2 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) -
      (3 : ℂ) • Matrix.vecMulVec v (fun i => star (v i))
    G * G = (1/2 : ℂ) • G := by
  dsimp only
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_smul, outer_square v hmass]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem rank_one_complement_charpoly (v : Fin 6 → ℂ)
    (hmass : (∑ i, Complex.normSq (v i)) = (1/6 : ℝ)) :
    ((1/2 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) -
      (3 : ℂ) • Matrix.vecMulVec v (fun i => star (v i))).charpoly =
        Polynomial.X * (Polynomial.X - Polynomial.C (1/2 : ℂ)) ^ 5 := by
  let A := Matrix.vecMulVec (fun i => (-3 : ℂ) * v i) (fun i => star (v i))
  have hM : (1/2 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) -
      (3 : ℂ) • Matrix.vecMulVec v (fun i => star (v i)) =
      A - Matrix.scalar (Fin 6) (-1/2 : ℂ) := by
    ext i j
    by_cases hij : i = j <;>
      simp [A, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.scalar_apply,
        hij] <;> ring
  have hdot : (fun i => (-3 : ℂ) * v i) ⬝ᵥ (fun i => star (v i)) = (-1/2 : ℂ) := by
    unfold dotProduct
    have hterm : ∀ i, (-3 : ℂ) * v i * star (v i) =
        (-3 : ℂ) * (Complex.normSq (v i) : ℂ) := by
      intro i
      rw [mul_assoc]
      exact congrArg ((-3 : ℂ) * ·) (Complex.mul_conj _)
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    have hm : (∑ i, (Complex.normSq (v i) : ℂ)) = (1/6 : ℂ) := by
      rw [← Complex.ofReal_sum, hmass]
      norm_num
    rw [hm]
    norm_num
  rw [hM, Matrix.charpoly_sub_scalar]
  dsimp only [A]
  rw [Matrix.charpoly_vecMulVec, hdot]
  norm_num only [Fintype.card_fin, Nat.reduceSub]
  simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.smul_eq_C_mul, Polynomial.mul_comp, Polynomial.C_comp]
  simp only [Polynomial.C_neg, Polynomial.C_div, Polynomial.C_ofNat]
  ring

/-- Both conclusions with the eigenvalue multiplicities retained by the
characteristic polynomial. -/
theorem normalMatrix_square_and_charpoly (u : Fin 6 → ℂ)
    (hmass : (∑ i, Complex.normSq (u i)) = (1/6 : ℝ))
    (hcard : (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ 2) :
    normalMatrix u * normalMatrix u = (1/2 : ℂ) • normalMatrix u ∧
      (normalMatrix u).charpoly =
        Polynomial.X * (Polynomial.X - Polynomial.C (1/2 : ℂ)) ^ 5 := by
  have hu : ∃ a, u a ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hmass
  obtain ⟨a, ha⟩ := hu
  rw [normalMatrix_eq_rank_one u hcard a ha]
  have hm : (∑ i, Complex.normSq (reflected u a i)) = (1/6 : ℝ) := by
    rw [reflected_mass, hmass]
  exact ⟨rank_one_complement_square (reflected u a) hm,
    rank_one_complement_charpoly (reflected u a) hm⟩

end

end SixQubit.Orbit8RaisingGram
