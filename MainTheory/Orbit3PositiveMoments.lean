import MainTheory.FiniteCubicMoments
import SixQubit.Generated.Orbit3PositiveSquare
import SixQubit.Realize

/-! # Actual cubic Gram matrices and the orbit-3 square

This supplies actual complex-amplitude positivity. It deliberately exposes the
remaining reduced-coordinate and vanishing-row hypotheses: those must still
be proved for the orbit's symmetry average before obtaining a full converse.
-/

namespace MainTheory.Orbit3PositiveMoments

open scoped Matrix
open SixQubit.Generated
open MainTheory.FiniteCubicMoments

noncomputable section

variable {G : Type*} [Fintype G]

def actualCubic (w : G → SS.State 6 ℂ) : G → Fin 36 → ℂ :=
  cubic Orbit3PositiveSquare.cubicTriples (fun g i => w g (SixQubit.Realize.nbit i.val))

def actualMoment (w : G → SS.State 6 ℂ) : Matrix (Fin 36) (Fin 36) ℝ :=
  realGram (actualCubic w)

theorem actualMoment_posSemidef (w : G → SS.State 6 ℂ) :
    (actualMoment w).PosSemidef := realGram_posSemidef _

theorem actualMoment_quadratic_form (w : G → SS.State 6 ℂ) (a : Fin 36 → ℝ) :
    a ⬝ᵥ (actualMoment w *ᵥ a) =
      ∑ g, Complex.normSq (∑ i, (a i : ℂ) * actualCubic w g i) :=
  realGram_quadratic_form _ _

/-- Positivity follows from the entry interpretation, not a PSD assumption. -/
theorem reduced_square_nonneg (w : G → SS.State 6 ℂ) (y : Fin 269 → ℝ)
    (hentry : ∀ i j, y (Orbit3PositiveSquare.coordinate i j) = actualMoment w i j) :
    0 ≤ Orbit3SexticIdentity.evaluate Orbit3SexticIdentity.square y := by
  have hmatrix : Orbit3PositiveSquare.momentMatrix y = actualMoment w := by
    ext i j
    exact hentry i j
  apply Orbit3PositiveSquare.square_nonneg_of_psd
  rw [hmatrix]
  exact actualMoment_posSemidef w

theorem target_zero_of_actual_moments (w : G → SS.State 6 ℂ) (y : Fin 269 → ℝ)
    (hentry : ∀ i j, y (Orbit3PositiveSquare.coordinate i j) = actualMoment w i j)
    (hrows : ∀ i, Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i) y = 0)
    (htarget : 0 ≤ Orbit3SexticIdentity.evaluate Orbit3SexticIdentity.target y) :
    Orbit3SexticIdentity.evaluate Orbit3SexticIdentity.target y = 0 :=
  Orbit3SexticIdentity.target_zero_of_constraints y hrows htarget
    (reduced_square_nonneg w y hentry)

end
end MainTheory.Orbit3PositiveMoments
