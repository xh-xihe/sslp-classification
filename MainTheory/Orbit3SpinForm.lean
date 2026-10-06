import MainTheory.Orbit3QuadraticZeros

/-! # The vanishing spin form is the actual physical Y-tensor bilinear

The paper's spin form has no complex conjugation on its first factor. This
identifies the signed complement sum with the action of Y on all six sites,
including its minus sign in the repository's Hermitian Pauli convention.
-/

namespace MainTheory.Orbit3SpinForm

open SS.MacWilliams SS.Shadow MainTheory.Orbit3ScalarCategoryRealization
open SixQubit.ParityLogicalState
open scoped BigOperators

noncomputable section

def fullY : SS.PauliString 6 := ⟨SS.ones 6, SS.ones 6⟩

theorem fullY_action (w : SS.State 6 ℂ) (s : SS.BitString 6) :
    SS.pauliAct fullY w s = -(psign s : ℂ) * w (SS.complement s) := by
  have hy : fullY.numY = 6 := by decide +kernel
  have ho : chi (SS.ones 6) (SS.ones 6) = 1 := by norm_num [chi, SS.ones]
  unfold SS.pauliAct
  rw [hy]
  change Complex.I ^ 6 * SS.signC (SS.bdot (SS.ones 6) (SS.bxor s (SS.ones 6)))
    (w (SS.bxor s (SS.ones 6))) = _
  rw [signC_bdot, chi_bxor_right, ho, mul_one, chi_comm, ← SS.complement_eq_bxor_ones]
  change Complex.I ^ 6 * ((psign s : ℂ) * w (SS.complement s)) = _
  have hi : Complex.I ^ 6 = -1 := by
    rw [show 6 = 2 * 3 by decide, pow_mul, Complex.I_sq]
    norm_num
  rw [hi]
  ring

def spin (w : SS.State 6 ℂ) : ℂ := ∑ s, w s * SS.pauliAct fullY w s

theorem spin_eq (w : SS.State 6 ℂ) :
    spin w = -(∑ s : SS.BitString 6, (psign s : ℂ) * w s * w (SS.complement s)) := by
  unfold spin
  simp_rw [fullY_action]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem actual_spin_zero (W : Encoder) : spin (superposition W.states) = 0 := by
  rw [spin_eq, MainTheory.Orbit3QuadraticZeros.superposition_spin_zero, neg_zero]

theorem spin_multiplier_zero (W : Encoder) (t : SS.BitString 6 × SS.BitString 6 × SS.BitString 6)
    (v : SS.BitString 6) :
    star (superposition W.states t.1 * superposition W.states t.2.1 *
      superposition W.states t.2.2) * spin (superposition W.states) * superposition W.states v = 0 := by
  rw [actual_spin_zero, mul_zero, zero_mul]

end
end MainTheory.Orbit3SpinForm
