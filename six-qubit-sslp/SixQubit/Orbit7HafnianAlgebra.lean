import SixQubit.Orbit7PairSum

/-!
# Orbit 7: division-free algebra for the full-support hafnian chart

The physical gauge reduction is kept elsewhere.  This file verifies the
algebra used after the four edges through one vertex have been scaled to
one.  In particular, the canonical `K_5` hafnian chart is derived rather
than postulated.
-/

namespace SixQubit.Orbit7Universal

noncomputable section

/-- Solving the four triangle hafnians and the remaining four-vertex
hafnian gives the usual cubic-root chart.  The statement uses no chosen
root of unity: the root `omega` is produced from the input amplitudes. -/
theorem normalized_hafnian_form
    (x12 x13 x14 x23 x24 x34 : ℂ)
    (hx12 : x12 ≠ 0)
    (h123 : x12 + x13 + x23 = 0)
    (h124 : x12 + x14 + x24 = 0)
    (h134 : x13 + x14 + x34 = 0)
    (h234 : x23 + x24 + x34 = 0)
    (h0 : x12*x34 + x13*x24 + x14*x23 = 0) :
    ∃ tau omega : ℂ,
      tau ≠ 0 ∧ 1 + omega + omega^2 = 0 ∧
      x12 = tau ∧ x34 = tau ∧
      x13 = tau*omega ∧ x24 = tau*omega ∧
      x14 = tau*omega^2 ∧ x23 = tau*omega^2 := by
  have hs : x12 + x13 + x14 = 0 := by
    linear_combination (-1 / 2 : ℂ) * (h234 - h123 - h124 - h134)
  have h23 : x23 = x14 := by linear_combination h123 - hs
  have h24 : x24 = x13 := by linear_combination h124 - hs
  have h34 : x34 = x12 := by linear_combination h134 - hs
  have hquad : x12^2 + x12*x13 + x13^2 = 0 := by
    rw [h23, h24, h34] at h0
    have hx14 : x14 = -x12-x13 := by linear_combination hs
    rw [hx14] at h0
    linear_combination (1 / 2 : ℂ) * h0
  refine ⟨x12, x13 / x12, hx12, ?_, rfl, h34, ?_, ?_, ?_, ?_⟩
  · field_simp
    linear_combination hquad
  · field_simp
  · rw [h24]
    field_simp
  · have hx14 : x14 = -x12-x13 := by linear_combination hs
    rw [hx14]
    field_simp
    linear_combination -hquad
  · rw [h23]
    have hx14 : x14 = -x12-x13 := by linear_combination hs
    rw [hx14]
    field_simp
    linear_combination -hquad

/-- The four-variable product pattern used after the second tangent
equation has only two possibilities: at most one coordinate is nonzero, or
all four coordinates coincide.  This is the division-free core of the
"one exceptional vertex" step. -/
theorem equal_pair_products
    (x0 x1 x2 x3 : ℂ)
    (h01_02 : x0*x1 = x0*x2)
    (h01_03 : x0*x1 = x0*x3)
    (h01_12 : x0*x1 = x1*x2)
    (h01_13 : x0*x1 = x1*x3)
    (h01_23 : x0*x1 = x2*x3) :
    (x0 = 0 ∧ x1 = 0 ∧ x2 = 0) ∨
      (x0 = 0 ∧ x1 = 0 ∧ x3 = 0) ∨
      (x0 = 0 ∧ x2 = 0 ∧ x3 = 0) ∨
      (x1 = 0 ∧ x2 = 0 ∧ x3 = 0) ∨
      (x0 = x1 ∧ x0 = x2 ∧ x0 = x3) := by
  by_cases h0 : x0 = 0
  · subst x0
    simp only [zero_mul] at h01_12 h01_13 h01_23
    by_cases h1 : x1 = 0
    · rcases mul_eq_zero.mp h01_23.symm with h2 | h3
      · exact Or.inl ⟨rfl, h1, h2⟩
      · exact Or.inr (Or.inl ⟨rfl, h1, h3⟩)
    · have h2 : x2 = 0 := (mul_eq_zero.mp h01_12.symm).resolve_left h1
      have h3 : x3 = 0 := (mul_eq_zero.mp h01_13.symm).resolve_left h1
      exact Or.inr (Or.inr (Or.inl ⟨rfl, h2, h3⟩))
  · have hx12 : x1 = x2 := by
      apply (mul_left_cancel₀ h0)
      exact h01_02
    have hx13 : x1 = x3 := by
      apply (mul_left_cancel₀ h0)
      exact h01_03
    by_cases h1 : x1 = 0
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h1, hx12 ▸ h1, hx13 ▸ h1⟩)))
    · have hx01 : x0 = x1 := by
        rw [← hx12] at h01_12
        exact (mul_right_cancel₀ h1) h01_12
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hx01, hx01.trans hx12, hx01.trans hx13⟩)))

end

end SixQubit.Orbit7Universal
