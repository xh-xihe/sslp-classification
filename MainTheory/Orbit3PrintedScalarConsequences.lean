import MainTheory.Orbit3PrintedScalarPlane

/-! The surviving low-weight categories and the literal fifth scalar dual.
Neither result appeals to the final sextic obstruction.
-/

namespace MainTheory.Orbit3PrintedScalarConsequences
noncomputable section
open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3CategoryBridge
open MainTheory.PhysicalPauliCategories MainTheory.OrderTwoLabelScalars
open MainTheory.RationalLinearCertificate SixQubit.Generated
open scoped BigOperators
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

def weightRow (j : ℕ) (c : Fin 24) : ℚ :=
  if (Orbit3Scalar.categories c).1 + (Orbit3Scalar.categories c).2.1 +
    (Orbit3Scalar.categories c).2.2 = j then 1 else 0

theorem weight_sum (W : Encoder) (j : ℕ) :
    evaluate (weightRow j) (y W) = SS.MacWilliams.Aco W.states j / 4 := by
  have hf (P : SS.PauliString 6) (c : Fin 24)
      (hc : categoryIndex P = Orbit3CategoryRows.columnCode c) :
      (if P.wt = j then (1 : ℝ) else 0) = (weightRow j c : ℝ) := by
    rw [category_weight, (category_column_iff P c).mpr hc]
    unfold weightRow
    split_ifs <;> norm_num
  rw [actual_evaluation W (weightRow j) _ hf]
  simp only [ite_mul, one_mul, zero_mul]
  exact MainTheory.Orbit3ScalarPlane.weight_mass W j

theorem remaining (W : Encoder) :
    SS.MacWilliams.Aco W.states 1 / 4 = y W 12 ∧
    SS.MacWilliams.Aco W.states 2 / 4 = y W 2 + y W 13 ∧
    SS.MacWilliams.Aco W.states 3 / 4 = y W 18 := by
  have h1 := (weight_sum W 1).symm
  have h2 := (weight_sum W 2).symm
  have h3 := (weight_sum W 3).symm
  have z1 := MainTheory.Orbit3ScalarEqualities.zero_categories W 0
  have z6 := MainTheory.Orbit3ScalarEqualities.zero_categories W 1
  have z7 := MainTheory.Orbit3ScalarEqualities.zero_categories W 2
  have z14 := MainTheory.Orbit3ScalarEqualities.zero_categories W 3
  have z3 := MainTheory.Orbit3ScalarEqualities.zero_categories W 4
  change y W 1 = 0 at z1
  change y W 6 = 0 at z6
  change y W 7 = 0 at z7
  change y W 14 = 0 at z14
  change y W 3 = 0 at z3
  norm_num [evaluate, weightRow, Orbit3Scalar.categories, Fin.sum_univ_succ, Fin.succ,
    z1,z6,z7,z14,z3] at h1 h2 h3
  change SS.MacWilliams.Aco W.states 2 / 4 = y W 2 + (y W 6 + y W 13) at h2
  rw [z6, zero_add] at h2
  change SS.MacWilliams.Aco W.states 3 / 4 = y W 3 + (y W 7 + (y W 14 + y W 18)) at h3
  rw [z3, z7, z14, zero_add, zero_add, zero_add] at h3
  exact ⟨h1,h2,h3⟩

theorem fifth_dual_coefficients : ∀ c : Fin 24,
    -(if c = 3 then (1 : ℚ) else 0) =
      10 * Orbit3Scalar.equalities 5 c - 10 * Orbit3Scalar.equalities 6 c := by
  decide +kernel

theorem fifth_dual_identity (v : Fin 24 → ℝ) :
    -v 3 = 10 * evaluate (Orbit3Scalar.equalities 5) v -
      10 * evaluate (Orbit3Scalar.equalities 6) v := by
  have h : ∀ c : Fin 24,
      -(if c = 3 then (1 : ℝ) else 0) =
      10 * (Orbit3Scalar.equalities 5 c : ℝ) -
      10 * (Orbit3Scalar.equalities 6 c : ℝ) := by
    intro c
    have hc := congrArg (fun q : ℚ => (q : ℝ)) (fifth_dual_coefficients c)
    by_cases he : c = 3 <;> simp [he] at hc ⊢ <;> exact hc
  have hs : (∑ c : Fin 24, -(if c = 3 then (1 : ℝ) else 0) * v c) =
      ∑ c : Fin 24, (10 * (Orbit3Scalar.equalities 5 c : ℝ) -
        10 * (Orbit3Scalar.equalities 6 c : ℝ)) * v c :=
    Finset.sum_congr rfl (fun c _ => congrArg (fun x : ℝ => x * v c) (h c))
  simpa only [neg_mul, ite_mul, one_mul, zero_mul, Finset.sum_neg_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, evaluate] using hs

theorem fifth_dual_row_metadata :
    Orbit3CategoryRows.equalityKind 5 = 1 ∧
    Orbit3CategoryRows.equalityKind 6 = 2 ∧
    Orbit3CategoryRows.errorCategory (Orbit3CategoryRows.equalityError 5) = (0,2,0) ∧
    Orbit3CategoryRows.errorCategory (Orbit3CategoryRows.equalityError 6) = (0,2,0) ∧
    Orbit3Scalar.categories 3 = (0,3,0) := by decide +kernel

end
end MainTheory.Orbit3PrintedScalarConsequences
