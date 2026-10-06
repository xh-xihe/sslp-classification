import Orbit2.Certificate

/-! Selected scalar steps of the analytic argument. These are conditional
lemmas, not a formal derivation from six-qubit Knill--Laflamme equations. -/
namespace Orbit2
open scoped BigOperators

/-- The algebra in the complementary-purity argument, including boundary strata.
The hypotheses are exactly the three scalar purity equations in the TeX. -/
theorem purity_flatness (a u v w b m s h₃ : ℝ)
    (hs : s = a + u + v + w)
    (h₁ : 1 + s = 2 * (1 + b))
    (hh : h₃ = 2 * (1 + b))
    (h₂ : 2 * (4 * (1 + b) + a + m) = 4 * (1 + s) - 2*u - 2*v - 4*w + h₃)
    (hb : 0 ≤ b) (hm : 0 ≤ m) (hw : 0 ≤ w) :
    b = 0 ∧ m = 0 ∧ w = 0 ∧ a + u + v = 1 := by
  have hz : b + m + w = 0 := by linarith
  have hb0 : b = 0 := by linarith
  have hm0 : m = 0 := by linarith
  have hw0 : w = 0 := by linarith
  exact ⟨hb0, hm0, hw0, by linarith⟩

/-- The shadow bound eliminates the remaining spectator-dressed mass. -/
theorem shadow_eliminates_extra_mass (a u v n : ℝ)
    (hmass : a + u + v = 1) (hn : 0 ≤ n)
    (hshadow : a + u + (v + n) ≤ 1) : n = 0 := by
  linarith

/-- A vanishing finite sum of nonnegative terms kills each term. This is also
what makes the spectral saturation argument work on zero rows. -/
theorem saturation {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i = 0) : ∀ i, a i = 0 := by
  intro i
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).mp hs i (Finset.mem_univ i)

/-- Finite-dimensional diagonal spectral saturation without division by a norm. -/
theorem diagonal_spectral_saturation {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (w : ι → ℂ) (he : ∀ i, 0 ≤ e i)
    (hzero : ∑ i, e i * Complex.normSq (w i) = 0) :
    ∀ i, 0 < e i → w i = 0 := by
  have h := saturation (fun i => e i * Complex.normSq (w i))
    (fun i => mul_nonneg (he i) (Complex.normSq_nonneg (w i))) hzero
  intro i hi
  have hn : Complex.normSq (w i) = 0 := (mul_eq_zero.mp (h i)).resolve_left (ne_of_gt hi)
  exact Complex.normSq_eq_zero.mp hn

/-- The central rigidity implication of the quartic certificate.
`S` is the set of nonzero-block monomials; it includes every weight-three
coefficient's square. The trace-to-polynomial identity and coercivity must
be supplied separately; they are NOT silently assumed as axioms. -/
theorem quartic_rigidity {κ ι μ : Type*} [Fintype κ] [Fintype ι] [Fintype μ]
    [DecidableEq μ] (c : κ → ℝ) (t : ι → ℂ) (z : μ → ℂ) (S : Finset μ)
    (diagonal : ι → μ) (hmem : ∀ i, diagonal i ∈ S)
    (hdiag : ∀ i, z (diagonal i) = t i * t i)
    (Q : ℝ) (hidentity : Q = -(∑ e, c e ^ 2))
    (hcoercive : (1/3 : ℝ) * ∑ j ∈ S, Complex.normSq (z j) ≤ Q) :
    (∀ e, c e = 0) ∧ (∀ i, t i = 0) := by
  have hc : 0 ≤ ∑ e, c e ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hz : 0 ≤ ∑ j ∈ S, Complex.normSq (z j) :=
    Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  have hc0 : ∑ e, c e ^ 2 = 0 := by linarith
  have hz0 : ∑ j ∈ S, Complex.normSq (z j) = 0 := by linarith
  constructor
  · have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => sq_nonneg (c e))).mp hc0
    intro e
    exact eq_zero_of_pow_eq_zero (hs e (Finset.mem_univ e))
  · have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (z j))).mp hz0
    intro i
    have hi : t i * t i = 0 := by
      rw [← hdiag i]
      exact Complex.normSq_eq_zero.mp (hs (diagonal i) (hmem i))
    exact (mul_self_eq_zero.mp hi)

/-- MacWilliams normal form as a scalar function, not as a theorem about codes. -/
def macWilliams (x y z : ℝ) : Fin 7 → ℝ :=
  ![1, x, y, z, 15-4*y-3*z, 12+3*x+4*y+3*z, 4-4*x-y-z]

def enumeratorLine (α : ℝ) : Fin 7 → ℝ :=
  ![1, α, 1-α, 0, 11+4*α, 16-α, 3-3*α]

/-- Once A₃=0 and flatness are proved, the claimed interval follows algebraically. -/
theorem enumerator_of_flatness_and_rigidity (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hflat : x+y+z = 1) (hrigid : z = 0) :
    0 ≤ x ∧ x ≤ 1 ∧ macWilliams x y z = enumeratorLine x := by
  have hxy : y = 1-x := by linarith
  refine ⟨hx, by linarith, ?_⟩
  subst z
  rw [hxy]
  ext i
  fin_cases i <;> simp [macWilliams, enumeratorLine] <;> ring

/-- Equality for all seven slots, including the two cancellations involving A₃. -/
theorem enumerator_plane (α ν : ℝ) :
    macWilliams α (1-α-ν) ν =
      ![1, α, 1-α-ν, ν, 11+4*α+ν, 16-α-ν, 3-3*α] := by
  ext i
  fin_cases i <;> simp [macWilliams] <;> ring

end Orbit2
