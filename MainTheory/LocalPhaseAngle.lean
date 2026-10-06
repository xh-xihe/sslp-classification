import MainTheory.ClassificationLevels
import MainTheory.PhaseSectorBridge

/-!
# Every local diagonal phase is a real-angle gate

`ProjectiveGroupFinite.BoundedLiftCover` has to surject bounded phase labels
onto the intrinsic group, and the entrance theorem
`D3CertifiedSpectralOuterEntrance.arbitrary_code_enters_outer` is stated for a
*real angle vector* `theta`.  The intrinsic group, by contrast, is built from
`LocalPhase n = Fin n → unitary ℂ`.  This file closes that gap: every local
phase is the real-angle gate of some `theta`, so every element of the group is
in the entrance theorem's domain.

The content is one classical fact -- a complex number of modulus one is
`exp (i t)` -- applied site by site, plus the observation that the subset-sum
angle of `MainTheory/RealGate.lean` turns the product over sites into a sum in
the exponent.
-/

namespace MainTheory.LocalPhaseAngle

open MainTheory.ClassificationLevels

variable {n : ℕ}

/-! ## One site -/

theorem norm_coe_unitary (z : unitary ℂ) : ‖((z : ℂ))‖ = 1 := by
  have h : star ((z : ℂ)) * ((z : ℂ)) = 1 := z.2.1
  have hmc : ((z : ℂ)) * (starRingEnd ℂ) ((z : ℂ))
      = (Complex.normSq ((z : ℂ)) : ℂ) := Complex.mul_conj _
  have hns : Complex.normSq ((z : ℂ)) = 1 := by
    have : ((Complex.normSq ((z : ℂ)) : ℂ)) = 1 := by
      rw [← hmc]
      simpa [Complex.star_def, mul_comm] using h
    exact_mod_cast this
  have hsq : ‖((z : ℂ))‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hns
  nlinarith [norm_nonneg ((z : ℂ)), hsq]

/-- A unit-modulus number is `exp (2 pi i t)` for a real `t`. -/
theorem exists_twoPiAngle (z : unitary ℂ) :
    ∃ t : ℝ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = (z : ℂ) := by
  obtain ⟨ s, hs ⟩ := (Complex.norm_eq_one_iff ((z : ℂ))).1 (norm_coe_unitary z)
  refine ⟨ s / (2 * Real.pi), ?_ ⟩
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [← hs]
  congr 1
  push_cast
  field_simp

/-! ## All sites at once -/

/-- A real angle vector reproducing a given local phase site by site. -/
theorem exists_angleVector (u : LocalPhase n) :
    ∃ theta : Fin n → ℝ, ∀ j,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((theta j : ℝ) : ℂ))
        = ((u j : ℂ)) := by
  choose theta htheta using fun j => exists_twoPiAngle (u j)
  exact ⟨ theta, htheta ⟩

/-- **The diagonal value of a local phase is the real gate's phase.**

The product over sites becomes a sum in the exponent, which is exactly the
subset-sum angle of `MainTheory/RealGate.lean`. -/
theorem diagonalValue_eq_exp (u : LocalPhase n) (theta : Fin n → ℝ)
    (h : ∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((theta j : ℝ) : ℂ))
      = ((u j : ℂ))) (x : SS.BitString n) :
    diagonalValue u x
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I
          * ((MainTheory.RealGate.angle theta x : ℝ) : ℂ)) := by
  rw [diagonalValue, MainTheory.RealGate.angle]
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hx : x j
  · simp [hx, ← h j]
  · simp [hx]

end MainTheory.LocalPhaseAngle
