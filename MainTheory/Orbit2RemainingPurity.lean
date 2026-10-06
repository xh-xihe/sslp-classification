import MainTheory.Orbit2ComplementaryPurity

/-! # The remaining actual complementary Gram purities for orbit 2

The logical reference is explicitly encoded as a binary coordinate. All
identities below use actual arbitrary Completion amplitudes. The further
Pauli support/counting reduction to b+m+w=0 remains a separate step.
-/

namespace MainTheory.Orbit2RemainingPurity

open MainTheory.Orbit2TraceReduction MainTheory.Orbit2ComplementaryPurity
open MainTheory.ClassificationLevels MainTheory.SingletonBitSplit
open MainTheory.SingletonPurity MainTheory.TensorPauliPurity MainTheory.PauliTensorTransfer
open scoped BigOperators Matrix

noncomputable section

def logicalBitEquiv : Fin 2 ≃ Bool where
  toFun k := k == 1
  invFun := bitIndex
  left_inv k := by fin_cases k <;> rfl
  right_inv b := by cases b <;> rfl

def logicalCubeEquiv (n : ℕ) : (Fin 2 × SS.BitString n) ≃ SS.BitString (1 + n) :=
  (Equiv.prodCongr logicalBitEquiv (Equiv.refl _)).trans
    ((Equiv.prodCongr (Equiv.funUnique (Fin 1) Bool).symm (Equiv.refl _)).trans (splitEquiv 1 n))

def spectatorAmplitudes (W : Encoder) : Matrix (SS.BitString 2) (SS.BitString 5) ℂ :=
  fun b r => W.states ((logicalCubeEquiv 4).symm r).1
    (Fin.append b ((logicalCubeEquiv 4).symm r).2)

theorem spectator_gram (W : Encoder) :
    spectatorAmplitudes W * (spectatorAmplitudes W).conjTranspose = (2 : ℂ) • spectator W := by
  ext b b'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, spectatorAmplitudes,
    Matrix.smul_apply, smul_eq_mul]
  rw [← (logicalCubeEquiv 4).sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [decoupling W 0 0 b b', decoupling W 1 1 b b']
  simp only [ite_true]
  ring

theorem reference_active_purity (W : Encoder) :
    frobSq ((spectatorAmplitudes W).conjTranspose * spectatorAmplitudes W) =
      4 * frobSq (spectator W) := by
  rw [← gram_purity_eq, spectator_gram]
  have h := frobSq_nat_smul 2 (spectator W)
  norm_num at h
  exact h

theorem reference_active_pauli_mass (W : Encoder) :
    (∑ p : Word 5, Complex.normSq (Matrix.trace
      (wordKernel p * ((spectatorAmplitudes W).conjTranspose * spectatorAmplitudes W)))) / 4 =
      8 * ∑ p : Word 2, Complex.normSq (Matrix.trace (wordKernel p * spectator W)) := by
  rw [parseval, parseval, reference_active_purity]
  norm_num
  ring

/-- Coefficient tensor for spectator pair plus one active site versus its
logical reference and the remaining three active sites. -/
def oneSiteAmplitudes (W : Encoder) (i : Fin 4) :
    Matrix (SS.BitString 3) (SS.BitString 4) ℂ :=
  fun b r => W.states ((logicalCubeEquiv 3).symm r).1
    (Fin.append (fun j : Fin 2 => b (Fin.castAdd 1 j))
      (Fin.insertNth i (b 2) ((logicalCubeEquiv 3).symm r).2))

theorem oneSite_complementary_pauli_mass (W : Encoder) (i : Fin 4) :
    (∑ p : Word 4, Complex.normSq (Matrix.trace
      (wordKernel p * ((oneSiteAmplitudes W i).conjTranspose * oneSiteAmplitudes W i)))) =
      2 * ∑ p : Word 3, Complex.normSq (Matrix.trace
        (wordKernel p * (oneSiteAmplitudes W i * (oneSiteAmplitudes W i).conjTranspose))) := by
  rw [parseval, parseval, ← gram_purity_eq]
  norm_num
  ring

theorem four_oneSite_complementary_pauli_masses (W : Encoder) :
    (∑ i : Fin 4, ∑ p : Word 4, Complex.normSq (Matrix.trace
      (wordKernel p * ((oneSiteAmplitudes W i).conjTranspose * oneSiteAmplitudes W i)))) =
      2 * ∑ i : Fin 4, ∑ p : Word 3, Complex.normSq (Matrix.trace
        (wordKernel p * (oneSiteAmplitudes W i * (oneSiteAmplitudes W i).conjTranspose))) := by
  simp_rw [oneSite_complementary_pauli_mass]
  rw [Finset.mul_sum]

end
end MainTheory.Orbit2RemainingPurity
