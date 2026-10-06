import Orbit2.QuarticCoefficients

namespace Orbit2.Quartic
open Orbit2.TensorPauli

theorem cCoeff_offblock (u v x y : Fin 32)
    (h : product (basis u) (basis v) ≠ product (basis x) (basis y)) :
    cCoeff u v x y = 0 := by
  have hn : product (basis x) (basis u) ≠ product (basis y) (basis v) :=
    fun he => h (pair_exchange _ _ _ _ he)
  simp [cCoeff, hn]

theorem gCoeff_offblock (u v x y : Fin 32)
    (h : product (basis u) (basis v) ≠ product (basis x) (basis y)) :
    gCoeff u v x y = 0 := by
  have hn : ¬ (u = x ∧ v = y) := by
    rintro ⟨rfl,rfl⟩; exact h rfl
  simp [gCoeff, wordTrace_four_zero _ _ _ _ h, hn]

theorem jCoeff_offblock (u v x y : Fin 32)
    (h : product (basis u) (basis v) ≠ product (basis x) (basis y)) :
    jCoeff u v x y = 0 := by
  have hn : ∀ site ax, ¬ (product (basis x) (basis v) = single site ax ∧
      product (basis u) (basis y) = single site ax) := by
    intro site ax he
    exact h (cross_exchange _ _ _ _ (he.1.trans he.2.symm))
  simp [jCoeff, wordTrace_four_zero _ _ _ _ h, hn]

/-- The character gate discards only coefficients already equal to zero. -/
theorem rawCoefficient_offblock (u v x y : Fin 32)
    (h : product (basis u) (basis v) ≠ product (basis x) (basis y)) :
    rawCoefficient u v x y = 0 := by
  simp [rawCoefficient, cCoeff_offblock _ _ _ _ h, jCoeff_offblock _ _ _ _ h,
    jCoeff_offblock _ _ _ _ h.symm, gCoeff_offblock _ _ _ _ h,
    gCoeff_offblock _ _ _ _ h.symm]

theorem gatedCoefficient_eq_raw (u v x y : Fin 32) :
    gatedCoefficient u v x y = rawCoefficient u v x y := by
  by_cases h : product (basis u) (basis v) = product (basis x) (basis y)
  · simp [gatedCoefficient, h]
  · simp [gatedCoefficient, h, rawCoefficient_offblock _ _ _ _ h]

def monomialCharacter (r : Fin 528) : Label 4 :=
  product (basis (monomials r).1) (basis (monomials r).2)

theorem orders_character (r : Fin 528) (uv : Fin 32 × Fin 32) (h : uv ∈ orders r) :
    product (basis uv.1) (basis uv.2) = monomialCharacter r := by
  unfold orders at h
  dsimp only at h
  split_ifs at h
  · simp only [List.mem_singleton] at h
    subst uv; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl
    · rfl
    · exact product_comm _ _

private theorem sum_map_zero {α : Type*} (xs : List α) (f : α → ℤ)
    (h : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy])), zero_add]

theorem twiceCoefficient_offblock (r c : Fin 528)
    (h : monomialCharacter r ≠ monomialCharacter c) : twiceCoefficient r c = 0 := by
  unfold twiceCoefficient
  apply sum_map_zero
  intro uv huv
  apply sum_map_zero
  intro xy hxy
  have hn : product (basis uv.1) (basis uv.2) ≠ product (basis xy.1) (basis xy.2) := by
    rw [orders_character r uv huv, orders_character c xy hxy]
    exact h
  simp [gatedCoefficient, hn]

end Orbit2.Quartic
