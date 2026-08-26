import SixQubit.Block33
import SixQubit.ParityFour

/-!
# Orbit 7: positive-semidefinite boundary algebra in `ℂ²`

These lemmas are the pure two-dimensional core of the isolated-vertex
branch.  They contain no graph classification and no orbit-specific support
ansatz.
-/

namespace SixQubit.Orbit7BoundaryPSD

open scoped BigOperators ComplexConjugate

noncomputable section

/-- If the complementary wedge already exhausts the product of two
`1/6` masses, Lagrange's identity forces the two spinors to be orthogonal. -/
theorem overlap_zero_of_wedge_lower
    (u0 u1 v0 v1 : ℂ)
    (hu : Complex.normSq u0 + Complex.normSq u1 = (1 / 6 : ℝ))
    (hv : Complex.normSq v0 + Complex.normSq v1 = (1 / 6 : ℝ))
    (hlower : (1 / 18 : ℝ) ≤
      2 * Complex.normSq (v0 * u1 - v1 * u0)) :
    star v0 * u0 + star v1 * u1 = 0 := by
  have hlag := SixQubit.ParityFour.lagrange v0 v1 u0 u1
  rw [hv, hu] at hlag
  have hw : (1 / 36 : ℝ) ≤ Complex.normSq (v0 * u1 - v1 * u0) := by
    linarith
  norm_num at hlag
  have hip : 0 ≤ Complex.normSq
      ((starRingEnd ℂ) v0 * u0 + (starRingEnd ℂ) v1 * u1) :=
    Complex.normSq_nonneg _
  have hip' : Complex.normSq
      ((starRingEnd ℂ) v0 * u0 + (starRingEnd ℂ) v1 * u1) ≤ 0 := by
    linarith
  have hz := Complex.normSq_eq_zero.mp (le_antisymm hip' hip)
  exact hz

/-- A family of total mass `1/3` orthogonal to a spinor `v` of mass `1/6`
has frame operator twice the outer product of any equally normalized spinor
`u` orthogonal to `v`.  The proof sums the division-free `ℂ²`
orthogonality identities; no choice of phase or coordinate chart occurs. -/
theorem incident_outer_eq_two
    {I : Type*} [DecidableEq I]
    (E : Finset I)
    (a0 a1 : I → ℂ)
    (u0 u1 v0 v1 : ℂ)
    (hu : u0 * star u0 + u1 * star u1 = (1 / 6 : ℂ))
    (hv : v0 * star v0 + v1 * star v1 = (1 / 6 : ℂ))
    (huv : star v0 * u0 + star v1 * u1 = 0)
    (haMass : (∑ e ∈ E,
      (a0 e * star (a0 e) + a1 e * star (a1 e))) = (1 / 3 : ℂ))
    (haOrth : ∀ e ∈ E, star v0 * a0 e + star v1 * a1 e = 0) :
    (∑ e ∈ E, a0 e * star (a0 e)) = 2 * (u0 * star u0) ∧
    (∑ e ∈ E, a0 e * star (a1 e)) = 2 * (u0 * star u1) ∧
    (∑ e ∈ E, a1 e * star (a0 e)) = 2 * (u1 * star u0) ∧
    (∑ e ∈ E, a1 e * star (a1 e)) = 2 * (u1 * star u1) := by
  have hsum0 :
      (∑ e ∈ E, (a0 e * star (a0 e) + a1 e * star (a1 e))) *
          (v0 * star v0) =
        (v0 * star v0 + v1 * star v1) *
          (∑ e ∈ E, a1 e * star (a1 e)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he =>
      (SixQubit.Block33.ortho2 v0 v1 (a0 e) (a1 e) (haOrth e he)).1
  have hsum1 :
      (∑ e ∈ E, (a0 e * star (a0 e) + a1 e * star (a1 e))) *
          (v0 * star v1) =
        -((v0 * star v0 + v1 * star v1) *
          (∑ e ∈ E, a0 e * star (a1 e))) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun e he =>
      (SixQubit.Block33.ortho2 v0 v1 (a0 e) (a1 e) (haOrth e he)).2.1
  have hsum2 :
      (∑ e ∈ E, (a0 e * star (a0 e) + a1 e * star (a1 e))) *
          (v1 * star v1) =
        (v0 * star v0 + v1 * star v1) *
          (∑ e ∈ E, a0 e * star (a0 e)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he =>
      (SixQubit.Block33.ortho2 v0 v1 (a0 e) (a1 e) (haOrth e he)).2.2
  rw [haMass, hv] at hsum0 hsum1 hsum2
  have hP11 : (∑ e ∈ E, a1 e * star (a1 e)) =
      2 * (v0 * star v0) := by
    linear_combination (-6) * hsum0
  have hP01 : (∑ e ∈ E, a0 e * star (a1 e)) =
      -2 * (v0 * star v1) := by
    linear_combination 6 * hsum1
  have hP00 : (∑ e ∈ E, a0 e * star (a0 e)) =
      2 * (v1 * star v1) := by
    linear_combination (-6) * hsum2
  have ho := SixQubit.Block33.ortho2 v0 v1 u0 u1 huv
  rw [hu, hv] at ho
  have hv00 : v0 * star v0 = u1 * star u1 := by
    linear_combination 6 * ho.1
  have hv01 : v0 * star v1 = -(u0 * star u1) := by
    linear_combination 6 * ho.2.1
  have hv11 : v1 * star v1 = u0 * star u0 := by
    linear_combination 6 * ho.2.2
  have h00 : (∑ e ∈ E, a0 e * star (a0 e)) =
      2 * (u0 * star u0) := by rw [hP00, hv11]
  have h01 : (∑ e ∈ E, a0 e * star (a1 e)) =
      2 * (u0 * star u1) := by
    rw [hP01, hv01]
    ring
  have h10 : (∑ e ∈ E, a1 e * star (a0 e)) =
      2 * (u1 * star u0) := by
    have hc := congrArg star h01
    simp only [star_sum, star_mul', star_star] at hc
    norm_num at hc
    simpa [mul_comm] using hc
  have h11 : (∑ e ∈ E, a1 e * star (a1 e)) =
      2 * (u1 * star u1) := by rw [hP11, hv00]
  exact ⟨h00, h01, h10, h11⟩

end

end SixQubit.Orbit7BoundaryPSD
