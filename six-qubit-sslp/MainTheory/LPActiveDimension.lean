import MainTheory.LPDimension

/-! # The actual active-face LP dimension formula -/

namespace MainTheory.LPDimension

open scoped BigOperators

noncomputable section

variable {r c : Type*} [Fintype c] [DecidableEq c]

/-- Insert zero at the coordinates outside the proposed active set. -/
def extendActive (U : Finset c) : (U → ℝ) →ₗ[ℝ] (c → ℝ) where
  toFun x j := if h : j ∈ U then x ⟨j, h⟩ else 0
  map_add' x y := by ext j; by_cases hj : j ∈ U <;> simp [hj]
  map_smul' a x := by ext j; by_cases hj : j ∈ U <;> simp [hj]

omit [Fintype c] in
@[simp] theorem extendActive_apply_mem (U : Finset c) (x : U → ℝ) (j : U) :
    extendActive U x j = x j := by simp [extendActive, j.property]

omit [Fintype c] in
theorem extendActive_injective (U : Finset c) : Function.Injective (extendActive U) := by
  intro x y h
  funext j
  simpa using congrFun h j

theorem mulVec_extendActive (A : Matrix r c ℝ) (U : Finset c) (x : U → ℝ) :
    A.mulVec (extendActive U x) = (A.submatrix id (↑)).mulVec x := by
  funext i
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ U)
    (fun j => A i j * extendActive U x j)
  have hz : ∀ j : {j // j ∉ U}, extendActive U x j = 0 := by
    intro j
    simp [extendActive, j.property]
  have hf : (Subtype.fintype (fun j => j ∈ U)) = Finset.Subtype.fintype U := Subsingleton.elim _ _
  rw [hf] at hs
  simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq,
    extendActive_apply_mem, hz, mul_zero, Finset.sum_const_zero, add_zero] using hs.symm

/-- A verified active set identifies the full feasible set with its restricted coordinates. -/
theorem feasibleSet_eq_extendActive_image (A : Matrix r c ℝ) (b : r → ℝ) (U : Finset c)
    (hzero : ∀ p ∈ feasibleSet A b, ∀ j ∉ U, p j = 0) :
    feasibleSet A b = extendActive U '' feasibleSet (A.submatrix id (↑)) b := by
  ext p
  constructor
  · intro hp
    let q : U → ℝ := fun j => p j
    have he : extendActive U q = p := by
      funext j
      by_cases hj : j ∈ U
      · simp [extendActive, hj, q]
      · simp [extendActive, hj, hzero p hp j hj]
    refine ⟨q, ⟨?_, fun j => hp.2 j⟩, he⟩
    rw [← mulVec_extendActive, he]
    exact hp.1
  · rintro ⟨q, hq, rfl⟩
    constructor
    · rw [mulVec_extendActive]
      exact hq.1
    · intro j
      by_cases hj : j ∈ U
      · simpa [extendActive, hj] using hq.2 ⟨j, hj⟩
      · simp [extendActive, hj]

/-- Nonnegativity and a full-support active witness give the stated affine dimension. -/
theorem finrank_eq_active_card_sub_rank (A : Matrix r c ℝ) (b : r → ℝ) (U : Finset c)
    (hzero : ∀ p ∈ feasibleSet A b, ∀ j ∉ U, p j = 0)
    (p : c → ℝ) (hp : p ∈ feasibleSet A b) (hpos : ∀ j ∈ U, 0 < p j) :
    Module.finrank ℝ (affineSpan ℝ (feasibleSet A b)).direction =
      U.card - (A.submatrix id ((↑) : U → c)).rank := by
  have heq := feasibleSet_eq_extendActive_image A b U hzero
  have hdir : (affineSpan ℝ (feasibleSet A b)).direction =
      Submodule.map (extendActive U)
        (affineSpan ℝ (feasibleSet (A.submatrix id ((↑) : U → c)) b)).direction := by
    rw [heq, direction_affineSpan, direction_affineSpan]
    exact (extendActive U).toAffineMap.map_vectorSpan.symm
  rw [hdir, ← (Submodule.equivMapOfInjective (extendActive U) (extendActive_injective U)
    (affineSpan ℝ (feasibleSet (A.submatrix id ((↑) : U → c)) b)).direction).finrank_eq]
  have hp' : (fun j : U => p j) ∈ feasibleSet (A.submatrix id ((↑) : U → c)) b := by
    have hmem : p ∈ extendActive U '' feasibleSet (A.submatrix id ((↑) : U → c)) b :=
      heq ▸ hp
    obtain ⟨q, hq, hqp⟩ := hmem
    have hqeq : q = fun j : U => p j := by
      funext j
      simpa using congrFun hqp j
    rwa [hqeq] at hq
  simpa using finrank_eq_card_sub_rank_of_positive (A.submatrix id ((↑) : U → c)) b
    (fun j => p j) hp'.1 (fun j => hpos j j.property)

/-- Active variables are determined by positive feasible primal witnesses. -/
def activeVariables (A : Matrix r c ℝ) (b : r → ℝ) : Finset c := by
  classical
  exact Finset.univ.filter fun j => j ∈ ActiveFace.Active (feasibleSet A b)

omit [DecidableEq c] in
@[simp] theorem mem_activeVariables (A : Matrix r c ℝ) (b : r → ℝ) (j : c) :
    j ∈ activeVariables A b ↔ ∃ p ∈ feasibleSet A b, 0 < p j := by
  classical
  simp [activeVariables, ActiveFace.Active]

omit [DecidableEq c] in
theorem feasibleSet_convex (A : Matrix r c ℝ) (b : r → ℝ) :
    Convex ℝ (feasibleSet A b) := by
  intro x hx y hy a e ha he hae
  constructor
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx.1, hy.1,
      ← add_smul, hae, one_smul]
  · intro j
    exact add_nonneg (mul_nonneg ha (hx.2 j)) (mul_nonneg he (hy.2 j))

/-- Equation `six:eq:lpdim`, using the intrinsic active set of the nonnegative polytope. -/
theorem dimension_eq_active_card_sub_rank [Nonempty c]
    (A : Matrix r c ℝ) (b : r → ℝ) (hne : (feasibleSet A b).Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (feasibleSet A b)).direction =
      (activeVariables A b).card -
        (A.submatrix id ((↑) : activeVariables A b → c)).rank := by
  obtain ⟨p, hp, hpos⟩ := ActiveFace.exists_positive_iff_active (feasibleSet A b)
    (feasibleSet_convex A b) hne (fun _ h => h.2)
  apply finrank_eq_active_card_sub_rank A b (activeVariables A b) ?_ p hp ?_
  · intro q hq j hj
    apply le_antisymm _ (hq.2 j)
    by_contra hh
    exact hj ((mem_activeVariables A b j).2 ⟨q, hq, lt_of_not_ge hh⟩)
  · intro j hj
    apply (hpos j).2
    exact (mem_activeVariables A b j).1 hj

end

end MainTheory.LPDimension
