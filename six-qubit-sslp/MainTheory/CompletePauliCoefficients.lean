import MainTheory.CompleteShadowTrace
import MainTheory.PauliFamilyTrace

set_option autoImplicit false

namespace MainTheory.CompletePauliCoefficients

open SS.MacWilliams SS.ShadowTwisted MainTheory.PairPartialTrace MainTheory.PauliKernelTrace

noncomputable def a (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) : ℝ :=
  Complex.normSq (trProj psi E)/4

noncomputable def b (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) : ℝ := frob psi E/2

theorem a_trace (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) :
    a psi E=(1/4 : ℝ)*Complex.normSq (Matrix.trace (pauliKernel E*familyKernel psi)) := by
  rw [MainTheory.PauliFamilyTrace.trace_family]
  unfold a
  ring

theorem b_trace (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) :
    (b psi E : ℂ)=(1/2 : ℂ)*Matrix.trace
      (familyKernel psi*pauliKernel E*familyKernel psi*pauliKernel E) := by
  rw [MainTheory.MixedFamilyTrace.pauli_trace]
  unfold b frob
  push_cast
  ring

theorem a_nonneg (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) : 0 ≤ a psi E :=
  div_nonneg (Complex.normSq_nonneg _) (by norm_num)

theorem b_nonneg (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) : 0 ≤ b psi E := by
  unfold b frob
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Complex.normSq_nonneg _) (by norm_num)

theorem weight_sum (psi : Fin 2 → SS.State 6 ℂ) (j : ℕ) :
    Aco psi j/4=∑ E ∈ Finset.univ.filter (fun E : SS.PauliString 6 => E.wt=j),a psi E := by
  simp only [Aco,a,Finset.sum_div]

theorem b_transform (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) :
    b psi E=(1/32 : ℝ)*∑ F : SS.PauliString 6,pairSign E F*a psi F := by
  have h := pauli_duality psi E
  have hs : (∑ F : SS.PauliString 6,pairSign E F*a psi F)=
      (∑ F : SS.PauliString 6,chi E.x F.z*chi E.z F.x*Complex.normSq (trProj psi F))/4 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro F _
    unfold pairSign a
    rw [chi_comm F.x E.z,chi_comm F.z E.x]
    ring
  rw [hs,h]
  unfold b
  norm_num
  ring

theorem s_transform (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) :
    MainTheory.CompleteShadowTrace.coefficient psi E=
      (1/32 : ℝ)*∑ F : SS.PauliString 6,(-1 : ℝ)^F.wt*pairSign E F*a psi F :=
  MainTheory.CompleteShadowTrace.coefficient_transform psi E

theorem kl_equality (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6)
    (h : SS.KLCondition psi E) : b psi E=a psi E := by
  have he := frob_of_KL psi E h
  norm_num at he
  unfold a b
  linarith

end MainTheory.CompletePauliCoefficients
