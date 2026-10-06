import Mathlib

/-!
# Orbit 7: two-component spinor algebra

The structural converse eventually reduces a two-qubit marginal to two pure
two-component spinors.  This file records the division-free Bloch-vector and
parallelogram identities needed to turn that statement into the low-weight
enumerator bound.  It is independent of the orbit support combinatorics.
-/

namespace SixQubit.Orbit7Spinor

noncomputable section

def bx (a b : ℂ) : ℂ := star a * b + star b * a
def by' (a b : ℂ) : ℂ := Complex.I * (star a * b - star b * a)
def bz (a b : ℂ) : ℂ := (Complex.normSq a - Complex.normSq b : ℝ)

/-- The squared Bloch-vector length of a (not necessarily normalized) pure
spinor is the square of its norm. -/
theorem bloch_norm (a b : ℂ) :
    Complex.normSq (bx a b) + Complex.normSq (by' a b) +
      Complex.normSq (bz a b) =
        (Complex.normSq a + Complex.normSq b)^2 := by
  norm_num [bx, by', bz, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.star_def]
  ring

lemma normSq_add_sub (z w : ℂ) :
    Complex.normSq (z+w) + Complex.normSq (z-w) =
      2*Complex.normSq z + 2*Complex.normSq w := by
  norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im]
  ring

/-- Sum/difference Bloch vectors obey the exact six-coordinate identity used
for the rank-two pair marginal. -/
theorem two_spinor_bloch (a₀ a₁ b₀ b₁ : ℂ) :
    (Complex.normSq (bx a₀ a₁ + bx b₀ b₁) +
      Complex.normSq (bx a₀ a₁ - bx b₀ b₁)) +
    (Complex.normSq (by' a₀ a₁ + by' b₀ b₁) +
      Complex.normSq (by' a₀ a₁ - by' b₀ b₁)) +
    (Complex.normSq (bz a₀ a₁ + bz b₀ b₁) +
      Complex.normSq (bz a₀ a₁ - bz b₀ b₁)) =
      2*(Complex.normSq a₀ + Complex.normSq a₁)^2 +
      2*(Complex.normSq b₀ + Complex.normSq b₁)^2 := by
  rw [normSq_add_sub, normSq_add_sub, normSq_add_sub]
  linear_combination
    2 * bloch_norm a₀ a₁ + 2 * bloch_norm b₀ b₁

end

end SixQubit.Orbit7Spinor
