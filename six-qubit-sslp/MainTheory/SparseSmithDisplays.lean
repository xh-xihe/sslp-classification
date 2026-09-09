import MainTheory.D3FreshSparseAssembly
import MainTheory.BetaExists

namespace MainTheory.SparseSmithDisplays

open MainTheory.D3SparseRationalization MainTheory.SharpClearing

theorem row_difference_zero {n r : ℕ} (P : Data n r) (theta : Fin n → ℝ)
    (htheta : (P.row.map (Int.castRingHom ℝ)).mulVec theta = fun i => (P.rhs i : ℝ)) :
    (P.row.map (Int.castRingHom ℝ)).mulVec (P.fullSolutionReal - theta) = 0 := by
  rw [Matrix.mulVec_sub, P.row_values_agree theta htheta, sub_self]

theorem selectedSolution_smith_integral {n r : ℕ} [NeZero r]
    (P : Data n r) (W : SmithWitness P.minor) :
    ∃ z : Fin r → ℤ, ∀ i, (W.lastFactor : ℚ) * P.selectedSolution i = (z i : ℚ) :=
  W.lastFactor_universallyClears P.rhs

theorem sparse_smith_beta_chain {n r : ℕ} [NeZero r] (P : Data n r)
    (W : SmithWitness P.minor) (hbinary : MainTheory.BinaryBeta.IsZeroOne P.minor)
    (hr : r ≤ n) :
    P.order ∣ W.lastFactor ∧ P.order ≤ W.lastFactor ∧
      W.lastFactor ≤ MainTheory.BetaExists.betaOf r ∧
      MainTheory.BetaExists.betaOf r ≤ MainTheory.BetaExists.betaOf n := by
  have hd : P.order ∣ W.lastFactor := by
    rw [← inverseDenominator_eq_smithLastFactor W]
    exact P.order_dvd_inverseDenominator
  refine ⟨hd, Nat.le_of_dvd W.lastFactor_pos hd, ?_, ?_⟩
  · rw [← inverseDenominator_eq_smithLastFactor W]
    exact (MainTheory.BetaExists.le_betaAt hbinary).trans
      (Finset.le_sup (f := MainTheory.BetaExists.betaAt)
        (Finset.mem_range.mpr (by omega)))
  · apply Finset.sup_le
    intro s hs
    exact Finset.le_sup (f := MainTheory.BetaExists.betaAt)
      (Finset.mem_range.mpr (by have := Finset.mem_range.mp hs; omega))

end MainTheory.SparseSmithDisplays
