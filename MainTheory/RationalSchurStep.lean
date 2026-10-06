import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Field

/-! Exact rational Schur elimination is a congruence and preserves positivity. -/

namespace MainTheory.RationalSchurStep

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def residual (d : ℚ) (b : ι → ℚ) (A : Matrix ι ι ℚ) : Matrix ι ι ℚ :=
  fun i j => A i j-b i*b j/d

def energy (A : Matrix ι ι ℚ) (y : ι → ℚ) : ℚ :=
  ∑ i,∑ j,A i j*y i*y j

theorem residual_energy (d : ℚ) (b : ι → ℚ) (A : Matrix ι ι ℚ) (y : ι → ℚ) :
    energy (residual d b A) y=energy A y-(∑ i,b i*y i)^2/d := by
  unfold energy residual
  simp_rw [sub_mul,Finset.sum_sub_distrib]
  simp_rw [div_mul_eq_mul_div]
  simp_rw [← Finset.sum_div]
  congr 2
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem completed_square (d : ℚ) (hd : d≠0) (b : ι → ℚ)
    (A : Matrix ι ι ℚ) (x : ℚ) (y : ι → ℚ) :
    d*x^2+2*x*(∑ i,b i*y i)+energy A y=
      d*(x+(∑ i,b i*y i)/d)^2+energy (residual d b A) y := by
  rw [residual_energy]
  field_simp
  ring

theorem positive_pivot (d : ℚ) (hd : 0<d) (b : ι → ℚ)
    (A : Matrix ι ι ℚ) (hA : ∀ y,y≠0 → 0<energy (residual d b A) y)
    (x : ℚ) (y : ι → ℚ) (hxy : x≠0 ∨ y≠0) :
    0<d*x^2+2*x*(∑ i,b i*y i)+energy A y := by
  rw [completed_square d (ne_of_gt hd)]
  by_cases hy : y=0
  · subst y
    have hx := hxy.resolve_right (not_ne_iff.mpr rfl)
    simpa [energy,residual] using mul_pos hd (sq_pos_of_ne_zero hx)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (le_of_lt hd) (sq_nonneg _)) (hA y hy)

end MainTheory.RationalSchurStep
