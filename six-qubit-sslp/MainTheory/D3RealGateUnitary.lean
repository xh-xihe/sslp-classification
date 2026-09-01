import MainTheory.D3LogicalAction

/-!
# Kernel proof that the real diagonal gate is unitary

The paper invokes unitarity when extracting logical phase sectors.  This file
proves the needed analytic-algebraic fact directly in the repository's custom
finite-sum inner product: every diagonal exponential has norm one, hence the
real gate preserves `SS.innerC` exactly.  It also records injectivity.

These are genuine inputs to the remaining construction of the second
orthogonal logical eigenvector; no operator is treated as unitary merely
because it is called a gate.
-/

namespace MainTheory.D3RealGateUnitary

variable {n d : ℕ}

open MainTheory
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Norm one of every computational-basis diagonal entry. -/
theorem realGate_diagonal_norm
    (theta : Fin n → ℝ) (s : SS.BitString n) :
    ‖Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I *
        (MainTheory.RealGate.angle theta s : ℂ))‖ = 1 := by
  have harg :
      2 * (Real.pi : ℂ) * Complex.I *
          (MainTheory.RealGate.angle theta s : ℂ) =
        ((2 * Real.pi * MainTheory.RealGate.angle theta s : ℝ) : ℂ) *
          Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Star times itself of every diagonal entry is one. -/
theorem realGate_diagonal_star_mul
    (theta : Fin n → ℝ) (s : SS.BitString n) :
    star (Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I *
        (MainTheory.RealGate.angle theta s : ℂ))) *
      Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I *
        (MainTheory.RealGate.angle theta s : ℂ)) = 1 := by
  rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, realGate_diagonal_norm]
  norm_num

/-- The real diagonal gate preserves the repository's Hermitian inner
product on the full physical state space. -/
theorem innerC_realGate
    (theta : Fin n → ℝ) (phi psi : SS.State n ℂ) :
    SS.innerC (MainTheory.RealGate.realGate theta phi)
        (MainTheory.RealGate.realGate theta psi) =
      SS.innerC phi psi := by
  unfold SS.innerC MainTheory.RealGate.realGate
  apply Finset.sum_congr rfl
  intro s _
  rw [star_mul]
  calc
    (star phi s *
          star (Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I *
              (MainTheory.RealGate.angle theta s : ℂ)))) *
        (Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I *
              (MainTheory.RealGate.angle theta s : ℂ)) * psi s) =
        (star (Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I *
              (MainTheory.RealGate.angle theta s : ℂ))) *
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I *
              (MainTheory.RealGate.angle theta s : ℂ))) *
          (star phi s * psi s) := by ring
    _ = star phi s * psi s := by
      rw [realGate_diagonal_star_mul]
      simp

/-- The real diagonal gate is injective on the full physical space. -/
theorem realGate_injective (theta : Fin n → ℝ) :
    Function.Injective (MainTheory.RealGate.realGate theta) := by
  intro phi psi h
  funext s
  have hs := congrFun h s
  unfold MainTheory.RealGate.realGate at hs
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) hs

end

end MainTheory.D3RealGateUnitary
