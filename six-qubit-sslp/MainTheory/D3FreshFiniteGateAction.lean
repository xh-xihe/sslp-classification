import MainTheory.D3FreshFiniteGate
import MainTheory.Cyclic

/-!
# Action-level bridge for the fresh finite gate

The coordinate bridge in `D3FreshFiniteGate` is promoted here to equality of
the complete diagonal action on every computational-basis amplitude.  The
definitions install `NeZero P.order` from the kernel-proved positivity of the
fresh least denominator; it is not an external instance assumption.
-/

namespace MainTheory.D3FreshFiniteGateAction

open MainTheory
open scoped BigOperators

noncomputable section

/-- Diagonal value of the fresh modular angle at the standard primitive root. -/
def freshDiag {n r : ℕ} (P : D3SparseRationalization.Data n r)
    (s : SS.BitString n) : ℂ := by
  letI : NeZero P.order := ⟨P.order_pos.ne'⟩
  exact Gate.diag (D3FreshFiniteGate.standardRoot P) P.angle s

/-- The corresponding linear diagonal action, defined without exposing a
dependent typeclass premise to callers. -/
def freshGate {n r : ℕ} (P : D3SparseRationalization.Data n r)
    (psi : SS.State n ℂ) : SS.State n ℂ :=
  fun s => freshDiag P s * psi s

private theorem prod_chi_eq_chi_sum {q : ℕ} [NeZero q]
    (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta q)
    (a : Fin n → ZMod q) (s : SS.BitString n) (T : Finset (Fin n)) :
    (∏ j ∈ T, if s j then Cyclic.chi zeta (a j) else 1) =
      Cyclic.chi zeta (∑ j ∈ T, a j * SS.bit (s j)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Cyclic.chi]
  | @insert j T hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj,
        Cyclic.chi_add zeta hzeta, ih]
      cases s j <;> simp [SS.bit, Cyclic.chi]

/-- The fresh diagonal value is the product of its coordinate phases. -/
theorem freshDiag_eq_prod {n r : ℕ}
    (P : D3SparseRationalization.Data n r) (s : SS.BitString n) :
    freshDiag P s =
      ∏ j : Fin n,
        if s j then
          D3FreshFiniteGate.standardRoot P ^ (P.angle j).val
        else 1 := by
  letI : NeZero P.order := ⟨P.order_pos.ne'⟩
  rw [freshDiag, Cyclic.diag_eq_chi]
  simpa [SS.weight, Cyclic.chi] using
    (prod_chi_eq_chi_sum
      (D3FreshFiniteGate.standardRoot P)
      (D3FreshFiniteGate.standardRoot_primitive P)
      P.angle s Finset.univ).symm

/-- The complete fresh finite diagonal value is exactly the real exponential
diagonal value of the freshly constructed rational phase. -/
theorem freshDiag_eq_realPhase {n r : ℕ}
    (P : D3SparseRationalization.Data n r) (s : SS.BitString n) :
    freshDiag P s =
      Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          (MainTheory.RealGate.angle P.fullSolutionReal s : ℂ)) := by
  rw [freshDiag_eq_prod]
  let A : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  calc
    (∏ j : Fin n,
        if s j then
          D3FreshFiniteGate.standardRoot P ^ (P.angle j).val
        else 1) =
        ∏ j : Fin n,
          Complex.exp
            (A * ((if s j then P.fullSolutionReal j else 0 : ℝ) : ℂ)) := by
      apply Finset.prod_congr rfl
      intro j _
      cases s j <;>
        simp [A, D3FreshFiniteGate.standardRoot_pow_angle_val]
    _ = Complex.exp
        (∑ j : Fin n,
          A * ((if s j then P.fullSolutionReal j else 0 : ℝ) : ℂ)) := by
      exact (Complex.exp_sum Finset.univ _).symm
    _ = Complex.exp
        (A * (MainTheory.RealGate.angle P.fullSolutionReal s : ℂ)) := by
      congr 1
      simp only [MainTheory.RealGate.angle]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      cases s j <;> simp

/-- Hence the fresh finite root-of-unity gate and the rational real gate are
identical as operations on the full physical state space, not merely on the
two logical supports. -/
theorem freshGate_eq_realGate {n r : ℕ}
    (P : D3SparseRationalization.Data n r) :
    freshGate P = MainTheory.RealGate.realGate P.fullSolutionReal := by
  funext psi s
  rw [freshGate, MainTheory.RealGate.realGate, freshDiag_eq_realPhase]

/-- With any locally installed `NeZero P.order` instance, the repository's
`Gate.gate` definition is the instance-free `freshGate` above. -/
theorem gate_eq_freshGate {n r : ℕ}
    (P : D3SparseRationalization.Data n r) [NeZero P.order] :
    Gate.gate (D3FreshFiniteGate.standardRoot P) P.angle = freshGate P := by
  funext psi s
  rfl

end

end MainTheory.D3FreshFiniteGateAction
