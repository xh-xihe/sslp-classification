import MainTheory.Orbit3ScalarPlane
import SixQubit.ParityLogicalState

/-! # Actual scalar and spin zero equations for the orbit-3 logical superposition -/

namespace MainTheory.Orbit3QuadraticZeros

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3ScalarEqualities
open MainTheory.Orbit3ScalarPlane MainTheory.PauliCategoryAverages
open MainTheory.OrderTwoLabelScalars MainTheory.OrderTwoScalarBridge
open MainTheory.PhysicalPauliCategories MainTheory.Orbit3CategoryBridge
open SixQubit.Generated SixQubit.ParityLogicalState
open SixQubit.ParityPauliScalars
open SS.MacWilliams SS.Shadow
open SS.ShadowTwisted
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem zero_category_trace (W : Encoder) (c : Fin 5) (P : SS.PauliString 6)
    (hc : category P = Orbit3Scalar.categories (Orbit3Scalar.zeroIndex c)) :
    trProj W.states P = 0 := by
  have hm : mass W.states (Orbit3Scalar.categories (Orbit3Scalar.zeroIndex c)) = 0 :=
    MainTheory.Orbit3ScalarEqualities.zero_categories W c
  have ha := individual_zero_of_mass_zero W.states _ hm P hc
  unfold a at ha
  apply Complex.normSq_eq_zero.mp
  linarith

theorem zero_category_quadratic (W : Encoder) (c : Fin 5) (P : SS.PauliString 6)
    (hc : category P = Orbit3Scalar.categories (Orbit3Scalar.zeroIndex c)) :
    mel (superposition W.states) (superposition W.states) P = 0 := by
  apply superposition_trace_zero W.states (orbit3_parity W) P _ (zero_category_trace W c P hc)
  have heven : (Orbit3Scalar.categories (Orbit3Scalar.zeroIndex c)).2.2 % 2 = 0 := by
    have h := Orbit3CategoryRows.even_columns (Orbit3Scalar.zeroIndex c)
    rw [(Orbit3CategoryRows.column_category _).1] at h
    exact h
  rw [chi_bdot, ← activeMask_eq, category_parity, hc, heven]
  rfl

theorem alternating_trace_zero (W : Encoder) :
    (∑ P : SS.PauliString 6, (-1 : ℝ) ^ P.wt * Complex.normSq (trProj W.states P)) = 0 := by
  rw [alt_sum_as_Aco]
  have hA0 := SixQubit.Pin.Aco_zero W.states W.normalized
  obtain ⟨h4, h5, h6⟩ := macwilliams_six W.states W.hasDistance hA0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, one_mul]
  norm_num
  rw [h4, h5, h6, hA0]
  have hp := unnormalized_low_plane W
  linarith

theorem spin_pair_norm_sum_zero (W : Encoder) :
    (∑ k : Fin 2, ∑ l : Fin 2, Complex.normSq (Tf W.states k l)) = 0 := by
  have he := alt_sum_eq_core W.states
  rw [(core_eq_nonneg_real W.states).1] at he
  have hz : (∑ P : SS.PauliString 6,
      (((-1 : ℝ) ^ P.wt * Complex.normSq (trProj W.states P) : ℝ) : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, alternating_trace_zero]
    rfl
  rw [hz] at he
  have hr := congrArg Complex.re he
  norm_num at hr
  simpa only [Fin.sum_univ_two] using hr

theorem spin_pair_zero (W : Encoder) (k l : Fin 2) : Tf W.states k l = 0 := by
  have hb : Complex.normSq (Tf W.states k l) ≤
      ∑ b : Fin 2, Complex.normSq (Tf W.states k b) :=
    Finset.single_le_sum (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ l)
  have ha : (∑ b : Fin 2, Complex.normSq (Tf W.states k b)) ≤
      ∑ a : Fin 2, ∑ b : Fin 2, Complex.normSq (Tf W.states a b) :=
    Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
      (Finset.mem_univ k)
  rw [spin_pair_norm_sum_zero] at ha
  apply Complex.normSq_eq_zero.mp
  have hn := Complex.normSq_nonneg (Tf W.states k l)
  linarith

theorem superposition_spin_zero (W : Encoder) :
    (∑ u : SS.BitString 6, (psign u : ℂ) *
      superposition W.states u * superposition W.states (SS.complement u)) = 0 := by
  have ht (u : SS.BitString 6) :
      (psign u : ℂ) * superposition W.states u * superposition W.states (SS.complement u) =
      ((psign u : ℂ) * W.states 0 u * W.states 0 (SS.complement u) +
        (psign u : ℂ) * W.states 0 u * W.states 1 (SS.complement u)) +
      (psign u : ℂ) * W.states 1 u * W.states 0 (SS.complement u) +
      (psign u : ℂ) * W.states 1 u * W.states 1 (SS.complement u) := by
    simp only [superposition]
    ring
  simp_rw [ht, Finset.sum_add_distrib]
  change (Tf W.states 0 0 + Tf W.states 0 1) + Tf W.states 1 0 + Tf W.states 1 1 = 0
  rw [spin_pair_zero, spin_pair_zero, spin_pair_zero, spin_pair_zero]
  simp

end
end MainTheory.Orbit3QuadraticZeros
