import MainTheory.SpinPauliShadowPairing

set_option autoImplicit false

namespace MainTheory.CompleteShadowTrace

open MainTheory.PairPartialTrace MainTheory.PauliKernelTrace
open MainTheory.Orbit8SpinProjector MainTheory.SpinPauliShadowPairing
open SS.ShadowTwisted

theorem trace_core (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) :
    Matrix.trace (familyKernel psi*pauliKernel E*spinConjugate (familyKernel psi)*pauliKernel E)=
      coreT psi E.x E.z := by
  have h := MainTheory.MixedFamilyTrace.pauli_trace
    (fun i => SixQubit.Orbit8Universal.spinJ (psi i)) psi E
  rw [← spin_family] at h
  simp_rw [norm_pairing] at h
  rw [show spinConjugate (familyKernel psi)*pauliKernel E*familyKernel psi*pauliKernel E=
    (spinConjugate (familyKernel psi)*pauliKernel E)*(familyKernel psi*pauliKernel E) by
      simp only [Matrix.mul_assoc],Matrix.trace_mul_comm] at h
  rw [coreT_eq_sum_normSq]
  simpa only [Matrix.mul_assoc,Complex.ofReal_sum] using h

noncomputable def coefficient (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) : ℝ :=
  (∑ a,∑ b,Complex.normSq (TfT psi E.x E.z a b))/2

theorem coefficient_trace (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) :
    (coefficient psi E : ℂ)=(1/2 : ℂ)*Matrix.trace
      (familyKernel psi*pauliKernel E*spinConjugate (familyKernel psi)*pauliKernel E) := by
  rw [trace_core,coreT_eq_sum_normSq]
  unfold coefficient
  push_cast
  ring

theorem coefficient_nonneg (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) :
    0 ≤ coefficient psi E := by
  unfold coefficient
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Complex.normSq_nonneg _) (by norm_num)

theorem coefficient_transform (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) :
    coefficient psi E=(1/32 : ℝ)*∑ F : SS.PauliString 6,
      (-1 : ℝ)^F.wt*pairSign E F*(Complex.normSq (SS.MacWilliams.trProj psi F)/4) := by
  have h := congrArg Complex.re (altT_sum_eq_coreT psi E)
  rw [coreT_eq_sum_normSq] at h
  simp only [Complex.re_sum,Complex.ofReal_re] at h
  norm_num [Complex.mul_re] at h
  unfold coefficient
  have he : (∑ F : SS.PauliString 6,
      (-1 : ℝ)^F.wt*pairSign E F*(Complex.normSq (SS.MacWilliams.trProj psi F)/4))=
      (∑ F : SS.PauliString 6,
      (-1 : ℝ)^F.wt*pairSign E F*Complex.normSq (SS.MacWilliams.trProj psi F))/4 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro F _
    ring
  rw [he]
  simp only [Fin.sum_univ_two]
  linarith

end MainTheory.CompleteShadowTrace
