import MainTheory.QECCFrameBridge

/-! Actual orthonormal states from disjoint normalized probability supports. -/
namespace MainTheory.ProbabilityFrames

open scoped BigOperators
noncomputable section
variable {n K : ℕ}

def state (p : Fin K → SS.BitString n → ℝ) (k : Fin K) : SS.State n ℂ :=
  fun x => (Real.sqrt (p k x) : ℂ)

theorem state_normSq (p : Fin K → SS.BitString n → ℝ)
    (hp : ∀ k x, 0 ≤ p k x) (k : Fin K) (x : SS.BitString n) :
    Complex.normSq (state p k x) = p k x := by
  rw [state, Complex.normSq_ofReal, Real.mul_self_sqrt (hp k x)]

theorem state_eq_zero (p : Fin K → SS.BitString n → ℝ)
    (hp : ∀ k x, 0 ≤ p k x) (k : Fin K) (x : SS.BitString n) :
    state p k x = 0 ↔ p k x = 0 := by
  rw [state, Complex.ofReal_eq_zero, Real.sqrt_eq_zero (hp k x)]

theorem orthonormal (p : Fin K → SS.BitString n → ℝ)
    (hp : ∀ k x, 0 ≤ p k x) (hsum : ∀ k, ∑ x, p k x = 1)
    (hdis : ∀ k l, k ≠ l → ∀ x, p k x = 0 ∨ p l x = 0) :
    ∀ k l, SS.innerC (state p k) (state p l) = if k = l then 1 else 0 := by
  intro k l
  by_cases hkl : k = l
  · subst l
    rw [if_pos rfl]
    have he (x : SS.BitString n) :
        star (state p k x) * state p k x = (p k x : ℂ) := by
      rw [state, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hp k x)]
    simp only [SS.innerC, he]
    rw [← Complex.ofReal_sum, hsum k]
    norm_num
  · rw [if_neg hkl]
    apply Finset.sum_eq_zero
    intro x _
    rcases hdis k l hkl x with hk | hl
    · rw [(state_eq_zero p hp k x).mpr hk, star_zero, zero_mul]
    · rw [(state_eq_zero p hp l x).mpr hl, mul_zero]

def frame (p : Fin K → SS.BitString n → ℝ)
    (hp : ∀ k x, 0 ≤ p k x) (hsum : ∀ k, ∑ x, p k x = 1)
    (hdis : ∀ k l, k ≠ l → ∀ x, p k x = 0 ∨ p l x = 0) :
    MainTheory.CodeSpec.OrthonormalFrame n K :=
  ⟨state p, orthonormal p hp hsum hdis⟩

end
end MainTheory.ProbabilityFrames
