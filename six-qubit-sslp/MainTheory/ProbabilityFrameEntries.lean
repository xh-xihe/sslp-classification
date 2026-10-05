import MainTheory.ProbabilityFrames

/-! Actual projector edges of positive two-state probability frames. -/
namespace MainTheory.ProbabilityFrameEntries

open MainTheory.CodeSpec
noncomputable section
variable {n : ℕ}

theorem entry (p : Fin 2 → SS.BitString n → ℝ)
    (hp : ∀ k x, 0 ≤ p k x) (hsum : ∀ k, ∑ x, p k x = 1)
    (hdis : ∀ k l, k ≠ l → ∀ x, p k x = 0 ∨ p l x = 0)
    (x y : SS.BitString n) :
    (MainTheory.QECCFrameBridge.ofFrame
      (MainTheory.ProbabilityFrames.frame p hp hsum hdis)).proj x y =
        ((Real.sqrt (p 0 x) * Real.sqrt (p 0 y) +
          Real.sqrt (p 1 x) * Real.sqrt (p 1 y) : ℝ) : ℂ) := by
  simp [MainTheory.QECCFrameBridge.ofFrame, MainTheory.ClassificationLevels.CodeProjector.ofFrame,
    projectorKernel, MainTheory.ProbabilityFrames.frame, MainTheory.ProbabilityFrames.state,
    Fin.sum_univ_two]

theorem nonzero_iff (p : Fin 2 → SS.BitString n → ℝ)
    (hp : ∀ k x, 0 ≤ p k x) (hsum : ∀ k, ∑ x, p k x = 1)
    (hdis : ∀ k l, k ≠ l → ∀ x, p k x = 0 ∨ p l x = 0)
    (x y : SS.BitString n) :
    (MainTheory.QECCFrameBridge.ofFrame
      (MainTheory.ProbabilityFrames.frame p hp hsum hdis)).proj x y ≠ 0 ↔
      (p 0 x ≠ 0 ∧ p 0 y ≠ 0) ∨ (p 1 x ≠ 0 ∧ p 1 y ≠ 0) := by
  rw [entry, ne_eq, Complex.ofReal_eq_zero,
    add_eq_zero_iff_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  simp only [mul_eq_zero, Real.sqrt_eq_zero (hp 0 x), Real.sqrt_eq_zero (hp 0 y),
    Real.sqrt_eq_zero (hp 1 x), Real.sqrt_eq_zero (hp 1 y)]
  tauto

end
end MainTheory.ProbabilityFrameEntries
