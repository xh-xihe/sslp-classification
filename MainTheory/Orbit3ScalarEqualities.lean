import MainTheory.Orbit3CategoryShift

/-! # Actual orbit-3 realization of every scalar equality row -/

namespace MainTheory.Orbit3ScalarEqualities

open MainTheory.OrderTwoLabelScalars MainTheory.PauliCategoryAverages
open MainTheory.PhysicalPauliCategories MainTheory.Orbit3CategoryBridge
open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3CategoryShift
open MainTheory.RationalLinearCertificate
open SixQubit.Generated SixQubit.Generated.Orbit3CategoryRows
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem evaluate_add (r s : Fin n → ℚ) (v : Fin n → ℝ) :
    evaluate (fun c => r c + s c) v = evaluate r v + evaluate s v := by
  unfold evaluate
  simp_rw [Rat.cast_add, add_mul, Finset.sum_add_distrib]

theorem evaluate_sub (r s : Fin n → ℚ) (v : Fin n → ℝ) :
    evaluate (fun c => r c - s c) v = evaluate r v - evaluate s v := by
  unfold evaluate
  simp_rw [Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]

theorem evaluate_div (r : Fin n → ℚ) (d : ℚ) (v : Fin n → ℝ) :
    evaluate (fun c => r c / d) v = evaluate r v / (d : ℝ) := by
  unfold evaluate
  simp_rw [Rat.cast_div, div_mul_eq_mul_div]
  rw [Finset.sum_div]

theorem evaluate_selector (W : Encoder) (e : Fin 42) :
    evaluate (selector e) (y W) = mass W.states (errorCategory e) := by
  have hf (P : SS.PauliString 6) (c : Fin 24) (hc : categoryIndex P = columnCode c) :
      (if category P = errorCategory e then (1 : ℝ) else 0) = (selector e c : ℝ) := by
    have he : category P = errorCategory e ↔ columnCode c = e := by
      rw [← categoryIndex_correct P, errorCategory_injective.eq_iff, hc]
    by_cases h : columnCode c = e <;> simp [selector, he, h]
  rw [actual_evaluation W (selector e) _ hf]
  unfold mass
  simp only [ite_mul, one_mul, zero_mul]

theorem identity_category_iff (P : SS.PauliString 6) :
    category P = errorCategory 0 ↔ P.wt = 0 := by
  rw [identity_category]
  have hw := category_weight P
  constructor
  · intro hc
    rw [hc] at hw
    simpa using hw
  · intro hz
    have h0 : (category P).1 = 0 := by omega
    have h1 : (category P).2.1 = 0 := by omega
    have h2 : (category P).2.2 = 0 := by omega
    exact Prod.ext h0 (Prod.ext h1 h2)

theorem identity_mass (W : Encoder) : mass W.states (errorCategory 0) = 1 := by
  unfold mass a
  simp_rw [identity_category_iff]
  have hr (P : SS.PauliString 6) :
      (if P.wt = 0 then Complex.normSq (SS.MacWilliams.trProj W.states P) / 4 else 0) =
      (if P.wt = 0 then Complex.normSq (SS.MacWilliams.trProj W.states P) else 0) / 4 := by
    by_cases h : P.wt = 0 <;> simp [h]
  simp_rw [hr]
  rw [← Finset.sum_div]
  have hA := SixQubit.Pin.Aco_zero W.states W.normalized
  unfold SS.MacWilliams.Aco at hA
  rw [Finset.sum_filter] at hA
  rw [hA]
  norm_num

theorem low_weight_average (W : Encoder) (e : Fin 42)
    (hwt : (errorCategory e).1 + (errorCategory e).2.1 + (errorCategory e).2.2 ≤ 2) :
    evaluate (Orbit3CategoryRows.fourier e) (y W) =
      mass W.states (errorCategory e) / errorSize e := by
  rw [b_average_eq]
  unfold average mass
  congr 1
  apply Finset.sum_congr rfl
  intro P _
  by_cases hc : category P = errorCategory e
  · have hp : P.wt ≤ 2 := by rw [category_weight, hc]; exact hwt
    simp [hc, orbit3_low_weight W P hp]
  · simp [hc]

theorem shadow_zero_average (W : Encoder) (e : Fin 42)
    (hk : (errorCategory e).2.2 % 2 = 1)
    (hodd : ((errorCategory e).1 + (errorCategory e).2.1 + (errorCategory e).2.2) % 2 = 1) :
    evaluate (spin e) (y W) = 0 := by
  rw [shadow_average_eq]
  have hr (P : SS.PauliString 6) :
      (if category P = errorCategory e then shadow W.states P else 0) = 0 := by
    by_cases hc : category P = errorCategory e
    · have hpar : SS.bdot MainTheory.OrderTwoScalarBridge.orbit3Mask P.x = true := by
        rw [← activeMask_eq, category_parity, hc, hk]
        rfl
      have hw : P.wt % 2 = 1 := by rw [category_weight, hc]; exact hodd
      rw [if_pos hc, orbit3_shadow_odd_zero W P hpar hw]
    · exact if_neg hc
  unfold average
  simp_rw [hr]
  simp

theorem diagonal_average (W : Encoder) (e : Fin 42)
    (hk : (errorCategory e).2.2 % 2 = 0) :
    evaluate (Orbit3CategoryRows.fourier e) (y W) =
      (mass W.states (errorCategory e) + mass W.states (errorCategory (complement e))) /
        errorSize e := by
  rw [b_average_eq]
  have hr (P : SS.PauliString 6) :
      (if category P = errorCategory e then b W.states P else 0) =
      (if category P = errorCategory e then a W.states P else 0) +
      (if category P = errorCategory e then a W.states (shift P) else 0) := by
    by_cases hc : category P = errorCategory e
    · have hpar : SS.bdot MainTheory.OrderTwoScalarBridge.orbit3Mask P.x = false := by
        rw [← activeMask_eq, category_parity, hc, hk]
        rfl
      simpa only [if_pos hc, shift] using orbit3_diagonal W P hpar
    · simp [hc]
  unfold average
  simp_rw [hr]
  rw [Finset.sum_add_distrib, shifted_mass]
  rfl

theorem equality_rows (W : Encoder) (i : Fin 43) :
    evaluate (Orbit3Scalar.equalities i) (y W) = (Orbit3Scalar.rhs i : ℝ) := by
  have hr : Orbit3Scalar.equalities i = equalityFormula i := by
    funext c
    exact equality_formula i c
  rw [hr, rhs_formula]
  have hc := equality_conditions i
  generalize hk : equalityKind i = k
  fin_cases k
  · have hrow : equalityFormula i = selector 0 := by
      funext c
      simp [equalityFormula, hk]
    rw [hrow, evaluate_selector, identity_mass]
    norm_num
  · have hrow : equalityFormula i = fun c => Orbit3CategoryRows.fourier (equalityError i) c -
        (selector (equalityError i) c + selector (complement (equalityError i)) c) /
          (errorSize (equalityError i) : ℚ) := by
      funext c
      simp [equalityFormula, hk]
    rw [hrow, evaluate_sub, evaluate_div, evaluate_add, evaluate_selector, evaluate_selector,
      diagonal_average W _ (hc.2.1 hk)]
    norm_num
  · have hrow : equalityFormula i = fun c => Orbit3CategoryRows.fourier (equalityError i) c -
        selector (equalityError i) c / (errorSize (equalityError i) : ℚ) := by
      funext c
      simp [equalityFormula, hk]
    rw [hrow, evaluate_sub, evaluate_div, evaluate_selector,
      low_weight_average W _ (hc.2.2.1 hk)]
    norm_num
  · have hrow : equalityFormula i = spin (equalityError i) := by
      funext c
      simp [equalityFormula, hk]
    rw [hrow, shadow_zero_average W _ (hc.2.2.2 hk).1 (hc.2.2.2 hk).2]
    norm_num

theorem zero_categories (W : Encoder) (c : Fin 5) : y W (Orbit3Scalar.zeroIndex c) = 0 :=
  Orbit3Scalar.zero_categories (y W) (equality_rows W) (positive_rows W) (y_nonneg W) c

theorem low_mass_bound (W : Encoder) :
    1 ≤ ∑ c : Fin 24,
      if (Orbit3Scalar.categories c).1 + (Orbit3Scalar.categories c).2.1 +
        (Orbit3Scalar.categories c).2.2 ∈ ([1, 2, 3] : List ℕ) then y W c else 0 :=
  Orbit3Scalar.low_mass_bound (y W) (equality_rows W) (positive_rows W) (y_nonneg W)

end
end MainTheory.Orbit3ScalarEqualities
