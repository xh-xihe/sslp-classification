import Orbit2.Analytic

namespace Orbit2
open scoped BigOperators

/-- The n=6 binary quantum Krawtchouk matrix, in weight order 0,...,6. -/
def krawtchouk : Matrix (Fin 7) (Fin 7) ℤ := ![![1, 1, 1, 1, 1, 1, 1], ![18, 14, 10, 6, 2, (-2), (-6)], ![135, 75, 31, 3, (-9), (-5), 15], ![540, 180, 12, (-28), (-4), 20, (-20)], ![1215, 135, (-81), (-9), 31, (-25), 15], ![1458, (-162), (-54), 54, (-30), 14, (-6)], ![729, (-243), 81, (-27), 9, (-3), 1]]

/-- The integer table is checked against the defining binomial formula. -/
theorem krawtchouk_formula (w j : Fin 7) :
    krawtchouk w j = ∑ k : Fin 7, if k.val ≤ w.val then
      (-1 : ℤ)^k.val * 3^(w.val-k.val) *
        (Nat.choose j.val k.val : ℤ) * (Nat.choose (6-j.val) (w.val-k.val) : ℤ)
      else 0 := by decide +kernel +revert

/-- Correct factor K/2ⁿ=2/64=1/32 for a rank-two six-qubit code.
Its applicability to code enumerators is a separate operator-theoretic theorem. -/
noncomputable def macTransform (A : Fin 7 → ℝ) (w : Fin 7) : ℝ :=
  (∑ j, (krawtchouk w j : ℝ) * A j) / 32

theorem macWilliams_normal_form (A : Fin 7 → ℝ)
    (hA : A 0 = 1)
    (h₀ : macTransform A 0 = A 0)
    (h₁ : macTransform A 1 = A 1)
    (h₂ : macTransform A 2 = A 2) :
    A = macWilliams (A 1) (A 2) (A 3) := by
  norm_num [macTransform, krawtchouk, Fin.sum_univ_succ, Fin.succ, Matrix.cons_val_two] at h₀ h₁ h₂
  change (A 0 + (A 1 + (A 2 + (A 3 + (A 4 + (A 5 + A 6)))))) / 32 = A 0 at h₀
  change (18*A 0 + (14*A 1 + (10*A 2 + (6*A 3 + (2*A 4 + (-(2*A 5) + -(6*A 6))))))) / 32 = A 1 at h₁
  change (135*A 0 + (75*A 1 + (31*A 2 + (3*A 3 + (-(9*A 4) + (-(5*A 5) + 15*A 6)))))) / 32 = A 2 at h₂
  have h4 : A 4 = 15-4*A 2-3*A 3 := by linarith
  have h5 : A 5 = 12+3*A 1+4*A 2+3*A 3 := by linarith
  have h6 : A 6 = 4-4*A 1-A 2-A 3 := by linarith
  ext i
  fin_cases i <;> simp [macWilliams, hA, h4, h5, h6]

/-- Exact spin-flip scalar identity after substituting the normal form. -/
theorem alternating_shadow_identity (x y z : ℝ) :
    (∑ w : Fin 7, (-1 : ℝ)^w.val * macWilliams x y z w) / 16 =
      (1/2 : ℝ) * (1-x-y-z) := by
  norm_num [macWilliams, Fin.sum_univ_succ, Fin.succ]
  ring

end Orbit2
