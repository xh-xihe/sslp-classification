import Mathlib

/-! # Positive cubic moments of actual complex vectors

The Gram entries are constructed from complex amplitudes, rather than supplied
as abstract positive coordinates. Any finite average, including one over a
finite symmetry group, preserves positivity. The orbit-specific identification
of entries with reduced coordinates is a separate obligation.
-/

namespace MainTheory.FiniteCubicMoments

open scoped Matrix BigOperators

noncomputable section

variable {G I B : Type*} [Fintype G] [Fintype I]

def realFeatures (v : G → I → ℂ) : Matrix (G × Bool) I ℝ :=
  fun gb i => if gb.2 then (v gb.1 i).im else (v gb.1 i).re

def realGram (v : G → I → ℂ) : Matrix I I ℝ :=
  (realFeatures v)ᴴ * realFeatures v

theorem realGram_posSemidef (v : G → I → ℂ) : (realGram v).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype I] in
theorem realGram_apply (v : G → I → ℂ) (i j : I) :
    realGram v i j = ∑ g, (star (v g i) * v g j).re := by
  classical
  simp only [realGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_trivial, realFeatures, Fintype.sum_prod_type, Fintype.sum_bool,
    Bool.false_eq_true, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro g _
  simp [Complex.mul_re, add_comm]

theorem realGram_quadratic_form (v : G → I → ℂ) (a : I → ℝ) :
    a ⬝ᵥ (realGram v *ᵥ a) =
      ∑ g, Complex.normSq (∑ i, (a i : ℂ) * v g i) := by
  classical
  unfold realGram
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose]
  simp only [star_trivial, dotProduct, realFeatures, Matrix.mulVec,
    Fintype.sum_prod_type, Fintype.sum_bool,
    Bool.false_eq_true, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  simp_rw [mul_comm (a _) _]
  ring

def cubic (triple : I → B × B × B) (w : G → B → ℂ) : G → I → ℂ :=
  fun g i => w g (triple i).1 * w g (triple i).2.1 * w g (triple i).2.2

def cubicMoment (triple : I → B × B × B) (w : G → B → ℂ) : Matrix I I ℝ :=
  realGram (cubic triple w)

theorem cubicMoment_posSemidef (triple : I → B × B × B) (w : G → B → ℂ) :
    (cubicMoment triple w).PosSemidef := realGram_posSemidef _

omit [Fintype I] in
theorem cubicMoment_apply (triple : I → B × B × B) (w : G → B → ℂ) (i j : I) :
    cubicMoment triple w i j = ∑ g,
      (star (w g (triple i).1 * w g (triple i).2.1 * w g (triple i).2.2) *
        (w g (triple j).1 * w g (triple j).2.1 * w g (triple j).2.2)).re :=
  realGram_apply _ _ _

theorem cubic_square_nonneg (triple : I → B × B × B) (w : G → B → ℂ)
    (a : I → ℝ) : 0 ≤ a ⬝ᵥ (cubicMoment triple w *ᵥ a) := by
  simpa using (cubicMoment_posSemidef triple w).dotProduct_mulVec_nonneg a

end
end MainTheory.FiniteCubicMoments
