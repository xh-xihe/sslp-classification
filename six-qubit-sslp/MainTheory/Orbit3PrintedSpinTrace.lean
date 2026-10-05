import MainTheory.Orbit3SpinForm
import MainTheory.Orbit3PrintedAmplitudes
import MainTheory.Orbit8SpinProjector

/-! The printed spin trace for arbitrary complex amplitudes and a positive
common column norm. This is an operator identity before any final A3-zero
conclusion. Individual amplitudes may vanish.
-/

namespace MainTheory.Orbit3PrintedSpinTrace
noncomputable section

open SS.MacWilliams SS.Shadow SixQubit.ParityPauliScalars
open MainTheory.Orbit3SpinForm MainTheory.Orbit3PrintedAmplitudes
open MainTheory.HomogeneousCompletionNormalization MainTheory.PairPartialTrace
open MainTheory.Orbit8SpinProjector MainTheory.CodeSpec
open scoped BigOperators

def bilinear (psi : Fin 2 → SS.State 6 ℂ) (a b : Fin 2) : ℂ :=
  ∑ s, psi a s * SS.pauliAct fullY (psi b) s

theorem bilinear_eq (psi : Fin 2 → SS.State 6 ℂ) (a b : Fin 2) :
    bilinear psi a b = -Tf psi a b := by
  simp only [bilinear, fullY_action, Tf]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem complement_sign (s : SS.BitString 6) : psign (SS.complement s) = psign s := by
  rw [SS.complement_eq_bxor_ones, psign_bxor]
  have ho : psign (SS.ones 6) = 1 := by norm_num [psign, chi, SS.ones]
  rw [ho, mul_one]

theorem pairing_symmetric (psi : Fin 2 → SS.State 6 ℂ) (a b : Fin 2) :
    Tf psi a b = Tf psi b a := by
  unfold Tf
  rw [← complementEquiv.sum_comp]
  simp only [complementEquiv, Equiv.coe_fn_mk, SS.complement_complement, complement_sign]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem pairing_diagonal_zero (psi : Fin 2 → SS.State 6 ℂ) (mask : SS.BitString 6)
    (hp : ParityPair mask psi) (ho : chi mask (SS.ones 6) = -1) (a : Fin 2) :
    Tf psi a a = 0 := by
  unfold Tf
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : chi mask s = logicalSign a
  · have ht : chi mask (SS.complement s) ≠ logicalSign a := by
      rw [SS.complement_eq_bxor_ones, chi_bxor_right, hs, ho]
      fin_cases a <;> norm_num [logicalSign]
    rw [hp a _ ht]
    ring
  · rw [hp a s hs]
    ring

theorem trace_formula (psi : Fin 2 → SS.State 6 ℂ) (mask : SS.BitString 6)
    (hp : ParityPair mask psi) (ho : chi mask (SS.ones 6) = -1) :
    Matrix.trace (familyKernel psi * spinConjugate (familyKernel psi)) =
      ((2 * Complex.normSq (bilinear psi 0 1) : ℝ) : ℂ) := by
  rw [trace_core, core_eq_sum_normSq]
  simp only [Fin.sum_univ_two, pairing_diagonal_zero psi mask hp ho,
    Complex.normSq_zero, Complex.ofReal_zero, zero_add, add_zero]
  rw [pairing_symmetric psi 1 0, bilinear_eq, Complex.normSq_neg]
  push_cast
  ring

theorem sqrt_two_spin (psi : Fin 2 → SS.State 6 ℂ) (mask : SS.BitString 6)
    (hp : ParityPair mask psi) (ho : chi mask (SS.ones 6) = -1) :
    spin (w psi) = bilinear psi 0 1 := by
  rw [spin_eq]
  have hc : (scale : ℂ) * (scale : ℂ) = (1/2 : ℂ) := by
    rw [← Complex.ofReal_mul, scale_product]
    norm_num
  have ht (s : SS.BitString 6) :
      (psign s : ℂ) * w psi s * w psi (SS.complement s) =
        (1/2 : ℂ) *
        (((psign s : ℂ) * psi 0 s * psi 0 (SS.complement s) +
          (psign s : ℂ) * psi 0 s * psi 1 (SS.complement s)) +
          (psign s : ℂ) * psi 1 s * psi 0 (SS.complement s) +
          (psign s : ℂ) * psi 1 s * psi 1 (SS.complement s)) := by
    simp only [w, SixQubit.ParityLogicalState.superposition, Pi.smul_apply, smul_eq_mul]
    calc
      _ = ((scale : ℂ) * (scale : ℂ)) *
          (((psign s : ℂ) * psi 0 s * psi 0 (SS.complement s) +
            (psign s : ℂ) * psi 0 s * psi 1 (SS.complement s)) +
            (psign s : ℂ) * psi 1 s * psi 0 (SS.complement s) +
            (psign s : ℂ) * psi 1 s * psi 1 (SS.complement s)) := by ring
      _ = _ := by rw [hc]
  simp_rw [ht]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  change -((1/2 : ℂ) * ((Tf psi 0 0 + Tf psi 0 1) + Tf psi 1 0 + Tf psi 1 1)) = _
  rw [pairing_diagonal_zero psi mask hp ho, pairing_diagonal_zero psi mask hp ho,
    pairing_symmetric psi 1 0, bilinear_eq]
  ring

theorem bilinear_normalized {F : MainTheory.CubeAction.FiberPair 6} (R : Raw F)
    (a b : Fin 2) : bilinear (completion R).states a b =
      (R.norm : ℂ)⁻¹ * bilinear R.states a b := by
  simp only [bilinear, completion, normalizedStates, pauliAct_smul,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  calc
    _ = (scalar R * scalar R) *
        (R.states a s * SS.pauliAct fullY (R.states b) s) := by ring
    _ = _ := by rw [scalar_product]

theorem raw_parity
    (R : Raw (MainTheory.DirectoryEnumeratorImages.angleFibers SixQubit.OpenLOrbit3.angle)) :
    ParityPair MainTheory.OrderTwoScalarBridge.orbit3Mask R.states := by
  intro a s hs
  have h := MainTheory.OrderTwoScalarBridge.orbit3_parity (completion R) a s hs
  change scalar R * R.states a s = 0 at h
  have hn : scalar R ≠ 0 := by
    simp only [scalar, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr R.positive)
  exact (mul_eq_zero.mp h).resolve_left hn

theorem orbit3_odd : chi MainTheory.OrderTwoScalarBridge.orbit3Mask (SS.ones 6) = -1 := by
  rw [chi_bdot]
  have h : SS.bdot MainTheory.OrderTwoScalarBridge.orbit3Mask (SS.ones 6) = true := by
    decide +kernel
  rw [h]
  rfl

theorem raw_spin
    (R : Raw (MainTheory.DirectoryEnumeratorImages.angleFibers SixQubit.OpenLOrbit3.angle)) :
    spin (w R.states) = bilinear R.states 0 1 :=
  sqrt_two_spin R.states _ (raw_parity R) orbit3_odd

theorem raw_trace
    (R : Raw (MainTheory.DirectoryEnumeratorImages.angleFibers SixQubit.OpenLOrbit3.angle)) :
    Matrix.trace (familyKernel (completion R).states *
      spinConjugate (familyKernel (completion R).states)) =
      ((2 * Complex.normSq (bilinear R.states 0 1) / R.norm^2 : ℝ) : ℂ) := by
  rw [trace_formula _ _ (MainTheory.OrderTwoScalarBridge.orbit3_parity (completion R)) orbit3_odd,
    bilinear_normalized, Complex.normSq_mul]
  have he : Complex.normSq ((R.norm : ℂ)⁻¹) = (R.norm^2)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.normSq_ofReal, ← pow_two, inv_pow]
  rw [he]
  congr 1
  ring

end
end MainTheory.Orbit3PrintedSpinTrace
