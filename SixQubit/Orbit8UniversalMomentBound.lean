import SixQubit.Orbit8UniversalMagnitudes

/-!
# Orbit 8: the two-point moment bound

This file isolates the last real-variable estimate in the universal orbit-8
argument.  It does not assume a displayed support: the support is the actual
nonzero set of the six singleton probabilities.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators

noncomputable section

/-- The actual nonzero support of a six-component probability vector. -/
def probabilitySupport (p : Fin 6 → ℝ) : Finset (Fin 6) :=
  Finset.univ.filter fun i => p i ≠ 0

lemma sum_probabilitySupport (p : Fin 6 → ℝ) :
    (∑ i ∈ probabilitySupport p, p i) = ∑ i, p i := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
  exact not_ne_iff.mp hnot

lemma sum_sq_probabilitySupport (p : Fin 6 → ℝ) :
    (∑ i ∈ probabilitySupport p, p i ^ 2) = ∑ i, p i ^ 2 := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
  rw [not_ne_iff.mp hnot]
  norm_num

/-- A nonnegative six-component vector of total mass `1/6`, supported on at
most two coordinates, has its second moment in the exact interval needed for
the orbit-8 enumerator. -/
theorem two_point_moment_bound (p : Fin 6 → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hsum : (∑ i, p i) = 1 / 6)
    (hcard : (probabilitySupport p).card ≤ 2) :
    1 / 72 ≤ (∑ i, p i ^ 2) ∧ (∑ i, p i ^ 2) ≤ 1 / 36 := by
  have hsquares : 0 ≤ ∑ i, p i ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := probabilitySupport p) (f := p)
  rw [sum_probabilitySupport, sum_sq_probabilitySupport, hsum] at hcs
  have hcardR : ((probabilitySupport p).card : ℝ) ≤ 2 := by
    exact_mod_cast hcard
  have hlower : 1 / 72 ≤ ∑ i, p i ^ 2 := by
    have hmul :
        ((probabilitySupport p).card : ℝ) * (∑ i, p i ^ 2)
          ≤ 2 * (∑ i, p i ^ 2) :=
      mul_le_mul_of_nonneg_right hcardR hsquares
    norm_num at hcs ⊢
    linarith
  have hpoint : ∀ i, p i ≤ 1 / 6 := by
    intro i
    have hrest : 0 ≤ ∑ j ∈ (Finset.univ.erase i), p j :=
      Finset.sum_nonneg fun j hj => hp j
    have hu : (∑ j, p j) = p i + ∑ j ∈ (Finset.univ.erase i), p j := by
      rw [← Finset.sum_insert (s := Finset.univ.erase i)
        (by simp)]
      congr
      exact (Finset.insert_erase (Finset.mem_univ i)).symm
    rw [hsum] at hu
    linarith
  have hterm : ∀ i, p i ^ 2 ≤ (1 / 6 : ℝ) * p i := by
    intro i
    nlinarith [hp i, hpoint i]
  have hupperSum :
      (∑ i, p i ^ 2) ≤ ∑ i, (1 / 6 : ℝ) * p i :=
    Finset.sum_le_sum fun i hi => hterm i
  rw [← Finset.mul_sum, hsum] at hupperSum
  constructor
  · exact hlower
  · norm_num at hupperSum ⊢
    exact hupperSum

end

end SixQubit.Orbit8Universal
