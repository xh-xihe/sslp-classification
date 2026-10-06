import MainTheory.IntrinsicTransport
import MainTheory.FiniteLift

namespace MainTheory.RealXNormalization

open scoped BigOperators
open MainTheory.PhaseSectorFull

noncomputable section

variable {n : ℕ}

def flipAngle (theta : Fin n → ℝ) (x₀ : SS.BitString n) : Fin n → ℝ :=
  fun j => if x₀ j then -theta j else theta j

theorem flipAngle_flipAngle (theta : Fin n → ℝ) (x₀ : SS.BitString n) :
    flipAngle (flipAngle theta x₀) x₀ = theta := by
  funext j
  cases h : x₀ j <;> simp [flipAngle, h]

theorem angle_flip_self (theta : Fin n → ℝ) (x₀ : SS.BitString n) :
    RealGate.angle (flipAngle theta x₀) x₀ = -RealGate.angle theta x₀ := by
  simp only [RealGate.angle, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases h : x₀ j <;> simp [flipAngle, h]

theorem angle_bxor (theta : Fin n → ℝ) (x₀ x : SS.BitString n) :
    RealGate.angle theta (SS.bxor x x₀) =
      RealGate.angle (flipAngle theta x₀) x + RealGate.angle theta x₀ := by
  simp only [RealGate.angle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases hx : x j <;> cases hy : x₀ j <;> simp [SS.bxor, flipAngle, hx, hy]

theorem phaseExp_ne_zero (z : ℝ) : phaseExp z ≠ 0 := Complex.exp_ne_zero _

theorem phaseExp_add (a b : ℝ) : phaseExp (a + b) = phaseExp a * phaseExp b := by
  simp only [phaseExp, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem phaseExp_sub (a b : ℝ) : phaseExp (a - b) = phaseExp a / phaseExp b := by
  simp only [phaseExp, Complex.ofReal_sub, mul_sub, Complex.exp_sub]

theorem phaseExp_fract (a : ℝ) : phaseExp (Int.fract a) = phaseExp a := by
  apply FiniteLift.phaseExp_eq_of_sub_int _ _ (-⌊a⌋)
  change a - (⌊a⌋ : ℝ) - a = ((-⌊a⌋ : ℤ) : ℝ)
  push_cast
  ring

def xMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def oneQubitDiagonal (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, phaseExp a]

theorem x_conjugation (a : ℝ) :
    xMatrix * oneQubitDiagonal a * xMatrix =
      phaseExp a • oneQubitDiagonal (-a) := by
  have hn : phaseExp (-a) = (phaseExp a)⁻¹ := by
    simpa [phaseExp] using phaseExp_sub 0 a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xMatrix, oneQubitDiagonal, Matrix.mul_apply,
      Matrix.diagonal, Matrix.vecHead, Matrix.vecTail, hn, phaseExp_ne_zero]

theorem gate_shift (theta : Fin n → ℝ) (x₀ : SS.BitString n) (ψ : SS.State n ℂ) :
    RealGate.realGate theta (fun x => ψ (SS.bxor x x₀)) =
      fun x => phaseExp (RealGate.angle theta x₀) *
        RealGate.realGate (flipAngle theta x₀) ψ (SS.bxor x x₀) := by
  funext x
  have he := angle_bxor theta x₀ (SS.bxor x x₀)
  have hx : SS.bxor (SS.bxor x x₀) x₀ = x := by
    funext j
    simp [SS.bxor]
  rw [hx] at he
  change phaseExp (RealGate.angle theta x) * ψ (SS.bxor x x₀) = _
  rw [he, phaseExp_add]
  change _ = phaseExp (RealGate.angle theta x₀) *
    (phaseExp (RealGate.angle (flipAngle theta x₀) (SS.bxor x x₀)) * _)
  ring

end

end MainTheory.RealXNormalization
