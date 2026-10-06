import MainTheory.ExactLP
import MainTheory.Rationalize
import MainTheory.LPActiveDimension

/-!
# Rational and real nonnegative feasibility

A real feasible point with inclusion-minimal positive support is unique on
that support. Rationalizing this restricted equality system therefore
preserves every coordinate, including its nonnegativity.
-/

namespace MainTheory.ExactLP

open scoped BigOperators
open MainTheory.LPDimension MainTheory.ActiveFace

noncomputable section

variable {r c : Type*} [Fintype c]

private theorem reduce_support (A : Matrix r c ℝ) (b : r → ℝ) (p v : c → ℝ)
    (hp : p ∈ feasibleSet A b) (hv : A.mulVec v = 0)
    (hout : ∀ j, p j = 0 → v j = 0) (hpos : ∃ j, 0 < v j) :
    ∃ q ∈ feasibleSet A b, (positiveSupport q).card < (positiveSupport p).card := by
  classical
  let S := Finset.univ.filter fun j => 0 < v j
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image (fun j => p j / v j) (by
    obtain ⟨j, hj⟩ := hpos
    exact ⟨j, by simp [S, hj]⟩)
  have hvi : 0 < v i := by simpa [S] using hi
  have hpi : 0 < p i := by
    apply (hp.2 i).lt_of_ne'
    intro hz
    exact hvi.ne' (hout i hz)
  let a := p i / v i
  have ha : 0 < a := div_pos hpi hvi
  let q := p - a • v
  have hq : q ∈ feasibleSet A b := by
    constructor
    · dsimp [q]
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hp.1, hv, smul_zero, sub_zero]
    · intro j
      change 0 ≤ p j - a * v j
      by_cases hj : 0 < v j
      · apply sub_nonneg.mpr
        exact (le_div_iff₀ hj).mp (hmin j (by simp [S, hj]))
      · exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hj)).trans (hp.2 j))
  have hqi : q i = 0 := by simp [q, a, hvi.ne']
  have hsub : positiveSupport q ⊆ positiveSupport p := by
    intro j hj
    have hqj : 0 < q j := by simpa [positiveSupport] using hj
    have hpj : 0 < p j := by
      apply (hp.2 j).lt_of_ne'
      intro hz
      have := hout j hz
      simp [q, hz, this] at hqj
    simpa [positiveSupport] using hpj
  refine ⟨q, hq, Finset.card_lt_card ?_⟩
  exact (Finset.ssubset_iff_subset_ne).mpr ⟨hsub, fun he => by
    have hip : i ∈ positiveSupport p := by simp [positiveSupport, hpi]
    rw [← he] at hip
    simp [positiveSupport, hqi] at hip⟩

private theorem kernel_zero_at_minimal_support (A : Matrix r c ℝ) (b : r → ℝ)
    (p : c → ℝ) (hp : p ∈ feasibleSet A b)
    (hmin : ∀ q ∈ feasibleSet A b, (positiveSupport p).card ≤ (positiveSupport q).card)
    (v : c → ℝ) (hv : A.mulVec v = 0) (hout : ∀ j, p j = 0 → v j = 0) : v = 0 := by
  classical
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hne (funext hh)
  have hreduce : ∃ q ∈ feasibleSet A b,
      (positiveSupport q).card < (positiveSupport p).card := by
    by_cases hpos : 0 < v j
    · exact reduce_support A b p v hp hv hout ⟨j, hpos⟩
    · apply reduce_support A b p (-v) hp
      · rw [Matrix.mulVec_neg, hv, neg_zero]
      · intro i hi
        simp [hout i hi]
      · exact ⟨j, neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hj)⟩
  obtain ⟨q, hq, hlt⟩ := hreduce
  exact (not_lt_of_ge (hmin q hq)) hlt

/-- Real feasibility for the same rational matrix and right-hand side. -/
def RealFeasible (A : Matrix r c ℚ) (b : r → ℚ) (p : c → ℝ) : Prop :=
  p ∈ feasibleSet (A.map (algebraMap ℚ ℝ)) (fun i => (b i : ℝ))

/-- A nonempty rational standard-form polyhedron contains a rational point. -/
theorem exists_rational_feasible_of_real (A : Matrix r c ℚ) (b : r → ℚ)
    (hne : ∃ p, RealFeasible A b p) : ∃ q, Feasible A b q := by
  classical
  have hex : ∃ k : ℕ, ∃ p, RealFeasible A b p ∧ (positiveSupport p).card = k := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨_, p, hp, rfl⟩
  obtain ⟨p, hp, hcard⟩ := Nat.find_spec hex
  have hminimal : ∀ q ∈ feasibleSet (A.map (algebraMap ℚ ℝ)) (fun i => (b i : ℝ)),
      (positiveSupport p).card ≤ (positiveSupport q).card := by
    intro q hq
    rw [hcard]
    exact Nat.find_min' hex ⟨q, hq, rfl⟩
  let U := positiveSupport p
  let R : Matrix r U ℚ := A.submatrix id (↑)
  let u : U → ℝ := fun j => p j
  have hext : extendActive U u = p := by
    funext j
    by_cases hj : j ∈ U
    · simp [extendActive, hj, u]
    · have hz : p j = 0 := le_antisymm (by simpa [U, positiveSupport] using hj) (hp.2 j)
      simp [extendActive, hj, hz]
  have hu : (R.map (algebraMap ℚ ℝ)).mulVec u = fun i => (b i : ℝ) := by
    change ((A.map (algebraMap ℚ ℝ)).submatrix id (↑)).mulVec u = _
    rw [← mulVec_extendActive, hext]
    exact hp.1
  have hker : ∀ v : U → ℝ, (R.map (algebraMap ℚ ℝ)).mulVec v = 0 → ∀ j, v j = 0 := by
    intro v hv
    have heq : extendActive U v = 0 := by
      apply kernel_zero_at_minimal_support (A.map (algebraMap ℚ ℝ))
        (fun i => (b i : ℝ)) p hp hminimal
      · rw [mulVec_extendActive]
        exact hv
      · intro j hj
        have hnot : j ∉ U := by simp [U, positiveSupport, hj]
        simp [extendActive, hnot]
    intro j
    simpa using congrFun heq j
  obtain ⟨q, hq, hcoords⟩ := MainTheory.Rationalize.exists_solution_preserving_coordinates
    (L := ℝ) R b id u hu hker
  let q' : c → ℚ := fun j => if h : j ∈ U then q ⟨j, h⟩ else 0
  have hcast : (fun j => (q' j : ℝ)) = p := by
    rw [← hext]
    funext j
    by_cases hj : j ∈ U
    · simpa [q', extendActive, hj, u] using hcoords ⟨j, hj⟩
    · simp [q', extendActive, hj]
  refine ⟨q', ?_, ?_⟩
  · funext i
    apply Rat.cast_injective (α := ℝ)
    have h := congrFun hp.1 i
    rw [← hcast] at h
    simpa [Matrix.mulVec, dotProduct] using h
  · intro j
    have h := hp.2 j
    rw [← hcast] at h
    change (0 : ℝ) ≤ (q' j : ℝ) at h
    exact_mod_cast h

/-- Passing between rationals and reals does not change standard-form feasibility. -/
theorem rational_feasible_iff_real (A : Matrix r c ℚ) (b : r → ℚ) :
    (∃ q, Feasible A b q) ↔ ∃ p, RealFeasible A b p := by
  constructor
  · rintro ⟨q, hq, hnonneg⟩
    refine ⟨fun j => (q j : ℝ), ?_, fun j => ?_⟩
    swap
    · change (0 : ℝ) ≤ (q j : ℝ)
      exact_mod_cast hnonneg j
    funext i
    have h := congrArg (algebraMap ℚ ℝ) (congrFun hq i)
    simpa [Matrix.mulVec, dotProduct] using h
  · exact exists_rational_feasible_of_real A b

private def activeAugment [DecidableEq c] (A : Matrix r c ℚ) (i : c) :
    Matrix (Sum r Unit) (Sum c Unit) ℚ := fun row col =>
  match row, col with
  | Sum.inl k, Sum.inl j => A k j
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl j => if j = i then 1 else 0
  | Sum.inr _, Sum.inr _ => -1

/-- Every real active coordinate admits an exact rational positive primal witness. -/
theorem exists_rational_active_of_real (A : Matrix r c ℚ) (b : r → ℚ) (i : c)
    (hne : ∃ p, RealFeasible A b p ∧ 0 < p i) :
    ∃ q, Feasible A b q ∧ 0 < q i := by
  classical
  obtain ⟨p, hp, hpi⟩ := hne
  obtain ⟨ε, hε, hbound⟩ := exists_rat_btwn hpi
  let b' : Sum r Unit → ℚ := Sum.elim b (fun _ => ε)
  let p' : Sum c Unit → ℝ := Sum.elim p (fun _ => p i - ε)
  have hp' : RealFeasible (activeAugment A i) b' p' := by
    constructor
    · funext row
      cases row with
      | inl k =>
        have h := congrFun hp.1 k
        simpa [Matrix.mulVec, dotProduct, activeAugment, b', p'] using h
      | inr k => simp [Matrix.mulVec, dotProduct, activeAugment, b', p', apply_ite]
    · intro j
      cases j with
      | inl j => exact hp.2 j
      | inr j => exact sub_nonneg.mpr hbound.le
  obtain ⟨q, hqeq, hqnn⟩ := exists_rational_feasible_of_real (activeAugment A i) b' ⟨p', hp'⟩
  refine ⟨fun j => q (Sum.inl j), ⟨?_, fun j => hqnn (Sum.inl j)⟩, ?_⟩
  · funext k
    have h := congrFun hqeq (Sum.inl k)
    simpa [Matrix.mulVec, dotProduct, activeAugment, b'] using h
  · have h := congrFun hqeq (Sum.inr ())
    have heq : q (Sum.inl i) - q (Sum.inr ()) = ε := by
      simpa [Matrix.mulVec, dotProduct, activeAugment, b', sub_eq_add_neg] using h
    have hεq : (0 : ℚ) < ε := by exact_mod_cast hε
    have hslack := hqnn (Sum.inr ())
    linarith

/-- Rational and real LPs have exactly the same active coordinates. -/
theorem rational_active_iff_real (A : Matrix r c ℚ) (b : r → ℚ) (i : c) :
    (∃ q, Feasible A b q ∧ 0 < q i) ↔ ∃ p, RealFeasible A b p ∧ 0 < p i := by
  constructor
  · rintro ⟨q, ⟨hq, hnn⟩, hi⟩
    refine ⟨fun j => (q j : ℝ), ⟨?_, ?_⟩, ?_⟩
    · funext k
      have h := congrArg (algebraMap ℚ ℝ) (congrFun hq k)
      simpa [Matrix.mulVec, dotProduct] using h
    · intro j
      change (0 : ℝ) ≤ (q j : ℝ)
      exact_mod_cast hnn j
    · change (0 : ℝ) < (q i : ℝ)
      exact_mod_cast hi
  · exact exists_rational_active_of_real A b i

end

end MainTheory.ExactLP
