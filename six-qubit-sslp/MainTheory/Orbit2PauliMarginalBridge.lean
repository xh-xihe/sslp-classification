import MainTheory.PauliPartialTrace
import MainTheory.Orbit2RemainingPurity
import MainTheory.PauliWordBridge

/-! # Orbit-2 complementary purities use the actual full-code Pauli coefficients

Partial traces of the genuine rank-two projector are identified with the
amplitude Gram matrices already used by the purity proof. The spectator
partial trace is twice the single-logical-word marginal, by full KL.
-/

namespace MainTheory.Orbit2PauliMarginalBridge

open MainTheory.Orbit2TraceReduction MainTheory.Orbit2ComplementaryPurity
open MainTheory.Orbit2RemainingPurity MainTheory.PauliTensorTransfer
open MainTheory.ClassificationLevels MainTheory.CodeSpec MainTheory.PauliWordBridge
open scoped Matrix BigOperators

noncomputable section

def projector (W : Encoder) : OperatorKernel 6 :=
  projectorKernel (MainTheory.CompletionCodeBridge.frame W)

theorem active_partial_trace (W : Encoder) :
    MainTheory.PauliPartialTrace.second (a := 2) (b := 4) (projector W) =
      amplitudes W * (amplitudes W).conjTranspose := by
  ext a a'
  simp only [MainTheory.PauliPartialTrace.second, projector, projectorKernel,
    MainTheory.CompletionCodeBridge.frame, Matrix.mul_apply, Matrix.conjTranspose_apply,
    amplitudes, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem spectator_partial_trace (W : Encoder) :
    MainTheory.PauliPartialTrace.first (a := 2) (b := 4) (projector W) =
      (2 : ℂ) • spectator W := by
  ext b b'
  simp only [MainTheory.PauliPartialTrace.first, projector, projectorKernel,
    MainTheory.CompletionCodeBridge.frame, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm, Fin.sum_univ_two, decoupling W 0 0 b b', decoupling W 1 1 b b']
  simp only [ite_true]
  ring

def coefficient (W : Encoder) (p : Word 6) : ℂ := Matrix.trace (wordKernel p * projector W)

theorem coefficient_physical_pauli (W : Encoder) (P : SS.PauliString 6) :
    coefficient W (pauliWordEquiv P) = SS.MacWilliams.trProj W.states P := by
  unfold coefficient
  rw [wordKernel_pauliWordEquiv]
  exact MainTheory.PauliKernelTrace.trace_pauliKernel_mul_projector
    (MainTheory.CompletionCodeBridge.frame W) P

theorem active_coefficient (W : Encoder) (p : Word 4) :
    coefficient W (Fin.append (fun _ : Fin 2 => 0) p) =
      Matrix.trace (wordKernel p * (amplitudes W * (amplitudes W).conjTranspose)) := by
  rw [coefficient, MainTheory.PauliPartialTrace.second_coefficient, active_partial_trace]

theorem spectator_coefficient (W : Encoder) (p : Word 2) :
    coefficient W (Fin.append p (fun _ : Fin 4 => 0)) =
      2 * Matrix.trace (wordKernel p * spectator W) := by
  rw [coefficient, MainTheory.PauliPartialTrace.first_coefficient, spectator_partial_trace,
    Matrix.mul_smul, Matrix.trace_smul]
  rfl

theorem active_spectator_physical_pauli_mass (W : Encoder) :
    (∑ p : Word 4, Complex.normSq (coefficient W (Fin.append (fun _ : Fin 2 => 0) p))) =
      2 * ∑ p : Word 2, Complex.normSq (coefficient W (Fin.append p (fun _ : Fin 4 => 0))) := by
  simp_rw [active_coefficient, spectator_coefficient, Complex.normSq_mul]
  norm_num only [Complex.normSq_ofNat]
  rw [← Finset.mul_sum]
  have h := active_spectator_pauli_mass W
  linarith

end
end MainTheory.Orbit2PauliMarginalBridge
