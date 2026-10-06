import MainTheory.WImages

/-! Normalize the six-qubit enumerator without unfolding Pauli sums. -/
namespace MainTheory.EnumeratorLineAlgebra

theorem normalized_line (a : ℕ → ℝ)
    (h0 : a 0 = 4) (h3 : a 3 = 0) (h12 : a 1 + a 2 + a 3 = 4)
    (h4 : a 4 = 60 - 4 * a 2 - 3 * a 3)
    (h5 : a 5 = 48 + 3 * a 1 + 4 * a 2 + 3 * a 3)
    (h6 : a 6 = 16 - 4 * a 1 - a 2 - a 3)
    (h1n : 0 ≤ a 1) (h2n : 0 ≤ a 2) :
    0 ≤ a 1 / 4 ∧ a 1 / 4 ≤ 1 ∧
      (fun w : Fin 7 => a w / 4) = WImages.FI (a 1 / 4) := by
  have h2 : a 2 = 4 - a 1 := by linarith
  refine ⟨by positivity, by linarith, ?_⟩
  ext w
  fin_cases w <;> simp [WImages.FI, h0, h3, h2, h4, h5, h6] <;> ring

end MainTheory.EnumeratorLineAlgebra
