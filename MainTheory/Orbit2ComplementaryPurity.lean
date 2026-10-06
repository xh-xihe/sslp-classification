import MainTheory.Orbit2TraceReduction
import MainTheory.CompletionCodeBridge
import MainTheory.SingletonBitSplit
import MainTheory.TensorPauliPurity

/-! # An actual orbit-2 complementary-purity equation

The two spectator qubits are a correctable erasure region. The genuine KL
matrix-unit identities make the reference/spectator Gram matrix block scalar.
Its purity equals the active Gram purity, giving the first Pauli-mass equation
of the manuscript directly from arbitrary encoder amplitudes.
-/

namespace MainTheory.Orbit2ComplementaryPurity

open MainTheory.Orbit2TraceReduction MainTheory.PauliTensorTransfer
open MainTheory.SingletonPurity MainTheory.TensorPauliPurity
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000

def amplitudes (W : Encoder) : Matrix (SS.BitString 4) (Fin 2 × SS.BitString 2) ℂ :=
  fun a kb => W.states kb.1 (Fin.append kb.2 a)

def spectator (W : Encoder) : Matrix (SS.BitString 2) (SS.BitString 2) ℂ :=
  fun b b' => ∑ a : SS.BitString 4,
    W.states 0 (Fin.append b a) * star (W.states 0 (Fin.append b' a))

theorem decoupling (W : Encoder) (k l : Fin 2) (b b' : SS.BitString 2) :
    (∑ a : SS.BitString 4, W.states k (Fin.append b a) *
      star (W.states l (Fin.append b' a))) = if k = l then spectator W b b' else 0 := by
  obtain ⟨c, hc⟩ := MainTheory.SingletonBitSplit.first_erasure_scalar
    (a := 2) (b := 4) (MainTheory.CompletionCodeBridge.code W) (by decide) b b'
  have h00 := hc 0 0
  change (∑ a : SS.BitString 4, W.states 0 (Fin.append b a) *
    star (W.states 0 (Fin.append b' a))) = if (0 : Fin 2) = 0 then c else 0 at h00
  change spectator W b b' = if (0 : Fin 2) = 0 then c else 0 at h00
  rw [if_pos rfl] at h00
  rw [h00]
  exact hc k l

theorem reference_gram (W : Encoder) :
    (amplitudes W).conjTranspose * amplitudes W = logicalBlock 2 (spectator W).transpose := by
  ext kb lb
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, amplitudes,
    logicalBlock, Matrix.transpose_apply]
  have hd := decoupling W lb.1 kb.1 lb.2 kb.2
  simpa only [mul_comm, eq_comm] using hd

theorem active_purity (W : Encoder) :
    frobSq (amplitudes W * (amplitudes W).conjTranspose) = 2 * frobSq (spectator W) := by
  rw [gram_purity_eq, reference_gram, frobSq_logicalBlock, frobSq_transpose]
  norm_num

theorem active_spectator_pauli_mass (W : Encoder) :
    (∑ p : Word 4, Complex.normSq (Matrix.trace
      (wordKernel p * (amplitudes W * (amplitudes W).conjTranspose)))) / 4 =
      2 * ∑ p : Word 2, Complex.normSq (Matrix.trace (wordKernel p * spectator W)) := by
  rw [parseval, parseval, active_purity]
  norm_num
  ring

end
end MainTheory.Orbit2ComplementaryPurity
