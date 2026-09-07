import MainTheory.SmithEquivalence

namespace MainTheory.SmithExistence

open Matrix

noncomputable section

/-- The elementary two-coordinate Smith step, with explicit integral
inverses. It replaces a pair by its gcd and product/gcd. -/
theorem diagonal_pair_step (g x y u v : ℤ) (h : u * x + v * y = 1) :
    IntegralEquivalent (Matrix.diagonal ![g * x, g * y])
      (Matrix.diagonal ![g, g * x * y]) := by
  let U : Matrix (Fin 2) (Fin 2) ℤ := !![u, v; -y, x]
  let Ui : Matrix (Fin 2) (Fin 2) ℤ := !![x, -v; y, u]
  let V : Matrix (Fin 2) (Fin 2) ℤ := !![1, -v * y; 1, u * x]
  let Vi : Matrix (Fin 2) (Fin 2) ℤ := !![u * x, v * y; -1, 1]
  have hU : U * Ui = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, Ui, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]
  have hUi : Ui * U = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, Ui, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]
  have hV : V * Vi = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, Vi, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]
  have hVi : Vi * V = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V, Vi, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]
  refine ⟨⟨U, Ui, hU, hUi⟩, ⟨V, Vi, hV, hVi⟩, ?_⟩
  change U * Matrix.diagonal ![g*x,g*y] * V = Matrix.diagonal ![g,g*x*y]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, V, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · linear_combination g * h
  · ring
  · ring
  · linear_combination g * x * y * h

theorem diagonal_gcd_pair (a b : ℕ) (ha : 0 < a) :
    IntegralEquivalent (Matrix.diagonal ![(a : ℤ), (b : ℤ)])
      (Matrix.diagonal ![(Nat.gcd a b : ℤ), (Nat.lcm a b : ℤ)]) := by
  let g := Nat.gcd a b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨x, hx⟩ := Nat.gcd_dvd_left a b
  obtain ⟨y, hy⟩ := Nat.gcd_dvd_right a b
  have hxZ : (a : ℤ) = (g : ℤ) * (x : ℤ) := by exact_mod_cast hx
  have hyZ : (b : ℤ) = (g : ℤ) * (y : ℤ) := by exact_mod_cast hy
  have hbez := Int.gcd_eq_gcd_ab (a : ℤ) (b : ℤ)
  have hcop : Int.gcdA a b * (x : ℤ) + Int.gcdB a b * (y : ℤ) = 1 := by
    have hgg : Int.gcd (a : ℤ) (b : ℤ) = g := by simp [g]
    rw [hgg] at hbez
    have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
    apply mul_left_cancel₀ hgZ
    linear_combination -hbez - (Int.gcdA a b) * hxZ - (Int.gcdB a b) * hyZ
  have hlcm : (Nat.lcm a b : ℤ) = (g : ℤ) * (x : ℤ) * (y : ℤ) := by
    have hp := Nat.gcd_mul_lcm a b
    have hpZ : (g : ℤ) * (Nat.lcm a b : ℤ) = (a : ℤ) * (b : ℤ) := by exact_mod_cast hp
    rw [hxZ, hyZ] at hpZ
    have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
    apply mul_left_cancel₀ hgZ
    linear_combination hpZ
  rw [hxZ, hyZ, hlcm]
  exact diagonal_pair_step g x y (Int.gcdA a b) (Int.gcdB a b) hcop

end

end MainTheory.SmithExistence
