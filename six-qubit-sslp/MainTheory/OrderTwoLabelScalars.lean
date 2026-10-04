import MainTheory.OrderTwoScalarBridge

/-! # The scalar laws of actual orbit-2/3 completions, with paper normalization

The quantities here are individual physical-Pauli coefficients, not arbitrary
nonnegative LP variables. The category averaging used by the finite scalar
duals is a further step.
-/

namespace MainTheory.OrderTwoLabelScalars

open SS.MacWilliams SS.ShadowTwisted
open MainTheory.CubeCompletionTransport MainTheory.DirectoryEnumeratorImages
open MainTheory.OrderTwoScalarBridge SixQubit.ParityPauliScalars

noncomputable section

def a (psi : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) : ℝ :=
  Complex.normSq (trProj psi P) / 4

def b (psi : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) : ℝ := frob psi P / 2

def shadow (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) : ℝ :=
  (∑ P : SS.PauliString 6, (-1 : ℝ) ^ P.wt * pairSign E P * a psi P) / 32

theorem a_nonneg (psi : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) :
    0 ≤ a psi P := div_nonneg (Complex.normSq_nonneg _) (by norm_num)

theorem b_nonneg (psi : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) :
    0 ≤ b psi P := by
  apply div_nonneg _ (by norm_num)
  unfold frob
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem b_fourier (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) :
    b psi E = (∑ P : SS.PauliString 6, pairSign E P * a psi P) / 32 := by
  have h := pauli_duality psi E
  have hsign (P : SS.PauliString 6) :
      chi E.x P.z * chi E.z P.x = pairSign E P := by
    unfold pairSign
    rw [chi_comm E.x P.z, chi_comm E.z P.x]
    ring
  simp_rw [hsign] at h
  norm_num only [show (2 : ℝ) ^ 6 = 64 by norm_num] at h
  unfold b a
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, h]
  ring

theorem shadow_nonneg (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6) :
    0 ≤ shadow psi E := by
  unfold shadow a
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  exact div_nonneg (div_nonneg (altT_sum_nonneg psi E) (by norm_num)) (by norm_num)

theorem b_eq_a_of_KL (psi : Fin 2 → SS.State 6 ℂ) (E : SS.PauliString 6)
    (hkl : SS.KLCondition psi E) : b psi E = a psi E := by
  have h := frob_of_KL psi E hkl
  norm_num only [Nat.cast_ofNat] at h
  unfold b a
  linarith

theorem orbit3_a_odd_zero
    (W : Completion (angleFibers SixQubit.OpenLOrbit3.angle)) (P : SS.PauliString 6)
    (hodd : SS.bdot orbit3Mask P.x = true) : a W.states P = 0 := by
  have hchi : chi orbit3Mask P.x = -1 := by rw [chi_bdot, hodd]; rfl
  unfold a
  rw [odd_trace_zero (orbit3_parity W) P hchi, Complex.normSq_zero, zero_div]

theorem orbit3_diagonal
    (W : Completion (angleFibers SixQubit.OpenLOrbit3.angle)) (E : SS.PauliString 6)
    (heven : SS.bdot orbit3Mask E.x = false) :
    b W.states E = a W.states E + a W.states ⟨E.x, SS.bxor E.z orbit3Mask⟩ := by
  have h := orbit3_diagonal_relation W E heven
  unfold a b
  linarith

theorem orbit3_low_weight
    (W : Completion (angleFibers SixQubit.OpenLOrbit3.angle)) (E : SS.PauliString 6)
    (hwt : E.wt ≤ 2) : b W.states E = a W.states E :=
  b_eq_a_of_KL _ E (W.hasDistance E hwt)

theorem orbit3_shadow_odd_zero
    (W : Completion (angleFibers SixQubit.OpenLOrbit3.angle)) (E : SS.PauliString 6)
    (htrans : SS.bdot orbit3Mask E.x = true) (hodd : E.wt % 2 = 1) :
    shadow W.states E = 0 := by
  unfold shadow a
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, orbit3_shadow_zero W E htrans hodd, zero_div, zero_div]

end
end MainTheory.OrderTwoLabelScalars
