import MainTheory.Orbit3ScalarEqualities

/-! # Saturation of the actual orbit-3 shadow bound -/

namespace MainTheory.Orbit3ScalarPlane

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3ScalarEqualities
open MainTheory.Orbit3CategoryBridge MainTheory.PhysicalPauliCategories
open MainTheory.OrderTwoLabelScalars MainTheory.RationalLinearCertificate
open SixQubit.Generated
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def lowMass (W : Encoder) : ℝ := ∑ c : Fin 24,
  if (Orbit3Scalar.categories c).1 + (Orbit3Scalar.categories c).2.1 +
    (Orbit3Scalar.categories c).2.2 ∈ ([1, 2, 3] : List ℕ) then y W c else 0

def lowRow (c : Fin 24) : ℚ :=
  if (Orbit3Scalar.categories c).1 + (Orbit3Scalar.categories c).2.1 +
    (Orbit3Scalar.categories c).2.2 ∈ ([1, 2, 3] : List ℕ) then 1 else 0

theorem lowMass_evaluate (W : Encoder) : lowMass W = evaluate lowRow (y W) := by
  unfold lowMass evaluate lowRow
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> norm_num

theorem three_weights (n : ℕ) (v : ℝ) :
    (if n ∈ ([1, 2, 3] : List ℕ) then v else 0) =
      (if n = 1 then v else 0) + (if n = 2 then v else 0) + (if n = 3 then v else 0) := by
  by_cases h1 : n = 1
  · subst n; simp
  by_cases h2 : n = 2
  · subst n; simp
  by_cases h3 : n = 3
  · subst n; simp
  simp [h1, h2, h3]

theorem weight_mass (W : Encoder) (j : ℕ) :
    (∑ P : SS.PauliString 6, if P.wt = j then a W.states P else 0) =
      SS.MacWilliams.Aco W.states j / 4 := by
  unfold a
  have hr (P : SS.PauliString 6) :
      (if P.wt = j then Complex.normSq (SS.MacWilliams.trProj W.states P) / 4 else 0) =
      (if P.wt = j then Complex.normSq (SS.MacWilliams.trProj W.states P) else 0) / 4 := by
    by_cases h : P.wt = j <;> simp [h]
  simp_rw [hr]
  rw [← Finset.sum_div]
  unfold SS.MacWilliams.Aco
  rw [Finset.sum_filter]

theorem lowMass_eq_Aco (W : Encoder) : lowMass W =
    (SS.MacWilliams.Aco W.states 1 + SS.MacWilliams.Aco W.states 2 +
      SS.MacWilliams.Aco W.states 3) / 4 := by
  rw [lowMass_evaluate]
  have hf (P : SS.PauliString 6) (c : Fin 24)
      (hc : categoryIndex P = Orbit3CategoryRows.columnCode c) :
      (if P.wt ∈ ([1, 2, 3] : List ℕ) then (1 : ℝ) else 0) = (lowRow c : ℝ) := by
    rw [category_weight, (category_column_iff P c).mpr hc]
    unfold lowRow
    split_ifs <;> norm_num
  rw [actual_evaluation W lowRow _ hf]
  simp only [ite_mul, one_mul, zero_mul]
  simp_rw [three_weights]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, weight_mass, weight_mass, weight_mass]
  ring

theorem unnormalized_low_plane (W : Encoder) :
    SS.MacWilliams.Aco W.states 1 + SS.MacWilliams.Aco W.states 2 +
      SS.MacWilliams.Aco W.states 3 = 4 := by
  have hlo := MainTheory.Orbit3ScalarEqualities.low_mass_bound W
  change 1 ≤ lowMass W at hlo
  rw [lowMass_eq_Aco] at hlo
  have hup := SS.Shadow.shadow_bound W.states W.hasDistance
    (SixQubit.Pin.Aco_zero W.states W.normalized)
  linarith

theorem low_plane (W : Encoder) : lowMass W = 1 := by
  rw [lowMass_eq_Aco, unnormalized_low_plane]
  norm_num

end
end MainTheory.Orbit3ScalarPlane
