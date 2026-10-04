import Orbit2.FrameConstruction
import Orbit2.PauliConjugation

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli
open Orbit2.PurityReduction Orbit2.Quartic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The physical mixed compression is the spectator Pauli coefficient of
the actual active-frame compression. The transpose accounts for the order
of the spectator coefficient indices. -/
theorem Encoder.frame_compression_trace (V : Encoder) (j k : Fin 2)
    (p : Label 2) (q : Label 4) :
    4 * (V.tensorMatrix.conjTranspose * operator (joinLabel p q) * V.tensorMatrix) j k =
      Matrix.trace ((operator p).transpose *
        ((V.schmidtFrame j).conjTranspose * operator q * V.schmidtFrame k)) := by
  rw [Matrix.mul_assoc V.tensorMatrix.conjTranspose,Matrix.mul_assoc (V.schmidtFrame j).conjTranspose]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.trace,Matrix.diag,Matrix.transpose_apply,Encoder.schmidtFrame,
    star_mul,star_ofNat]
  simp_rw [sum_splitBits,operator_split]
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_lhs =>
    arg 2
    intro b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem mixed_zero_reason : ∀ (p : Label 2) (i : Fin 4) (a : Fin 4),
    p≠(fun _ => 0) → a≠0 →
    0 < targetCoefficient (Fin.cons 0 (joinLabel p (single i a))) ∨
      zeroParity (Fin.cons 0 (joinLabel p (single i a))) := by decide +kernel

theorem Encoder.mixed_trace_zero (V : Encoder) (p : Label 2) (i a : Fin 4)
    (hp : p≠fun _ => 0) (ha : a≠0) :
    Matrix.trace (V.tensorMatrix.conjTranspose * operator (joinLabel p (single i a)) *
      V.tensorMatrix) = 0 := by
  have hm : V.labelMass (Fin.cons 0 (joinLabel p (single i a))) = 0 := by
    rcases mixed_zero_reason p i a hp ha with h|h
    · exact PhysicalFlatness.target_masses_zero V _ h
    · exact V.labelMass_parity_zero _ h
  rw [PhysicalFlatness.reference_identity_mass] at hm
  unfold PhysicalFlatness.physicalMass at hm
  have hz : SS.MacWilliams.trProj V.psi (decode (joinLabel p (single i a))) = 0 := by
    apply Complex.normSq_eq_zero.mp
    linarith
  rwa [V.tensor_trace] at hz

theorem mixed_KL_weight : ∀ (p : Label 2) (i a : Fin 4),
    (∑ b, if p b=0 then 0 else 1 : ℕ) ≤ 1 →
    (∑ b, if joinLabel p (single i a) b=0 then 0 else 1 : ℕ) ≤ 2 := by
  decide +kernel

theorem Encoder.mixed_compression_zero (V : Encoder) (p : Label 2) (i a : Fin 4)
    (hp : p≠fun _ => 0) (ha : a≠0)
    (hw : (∑ b, if p b=0 then 0 else 1 : ℕ) ≤ 1) :
    V.tensorMatrix.conjTranspose * operator (joinLabel p (single i a)) * V.tensorMatrix = 0 := by
  obtain ⟨c,hc⟩ := V.tensor_KL _ (mixed_KL_weight p i a hw)
  have ht := V.mixed_trace_zero p i a hp ha
  rw [hc,Matrix.trace_smul] at ht
  have hi : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by norm_num
  rw [hi] at ht
  have hz : c=0 := by simp only [smul_eq_mul] at ht; linear_combination ht/2
  simp [hc,hz]

/-- Every weight-one spectator coefficient of every active single-site
compression block vanishes, as a consequence of actual mixed KL. -/
theorem Encoder.frame_odd_trace_zero (V : Encoder) (j k : Fin 2)
    (p : Label 2) (i a : Fin 4) (ha : a≠0)
    (hw : (∑ b, if p b=0 then 0 else 1 : ℕ) = 1) :
    Matrix.trace ((operator p).transpose *
      ((V.schmidtFrame j).conjTranspose * operator (single i a) * V.schmidtFrame k)) = 0 := by
  have hp : p≠fun _ => 0 := by intro hp; simp [hp] at hw
  rw [← V.frame_compression_trace,V.mixed_compression_zero p i a hp ha (by omega)]
  simp

theorem matrix_reconstruction_transpose {n : ℕ}
    (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    M = ∑ p : Label n, tau ((operator p).transpose * M) • (operator p).transpose := by
  have h := congrArg Matrix.transpose (matrix_reconstruction M.transpose)
  have ht (p : Label n) : tau (operator p * M.transpose) = tau ((operator p).transpose * M) := by
    unfold tau
    rw [← Matrix.trace_transpose (operator p * M.transpose),Matrix.transpose_mul,
      Matrix.transpose_transpose,Matrix.trace_mul_comm]
  simpa only [Matrix.transpose_transpose,Matrix.transpose_sum,Matrix.transpose_smul,ht] using h

theorem matrix_scalar_of_transpose_traces
    (M : Matrix SpectatorBits SpectatorBits ℂ)
    (h : ∀ p : Label 2, p≠(fun _ => 0) → Matrix.trace ((operator p).transpose * M)=0) :
    M = (Matrix.trace M / 4) • 1 := by
  have ht (p : Label 2) : tau ((operator p).transpose * M) =
      if p=(fun _ => 0) then Matrix.trace M / 4 else 0 := by
    by_cases hp : p=(fun _ => 0)
    · subst p
      norm_num [tau,operator_zero]
    · simp [tau,h p hp,hp]
  rw [matrix_reconstruction_transpose M]
  simp_rw [ht]
  simp [ite_smul,operator_zero]

noncomputable def Encoder.diagonalFrameSum (V : Encoder) (q : Label 4) :
    Matrix SpectatorBits SpectatorBits ℂ :=
  (V.schmidtFrame 0).conjTranspose * operator q * V.schmidtFrame 0 +
    (V.schmidtFrame 1).conjTranspose * operator q * V.schmidtFrame 1

/-- The two diagonal active-frame blocks have scalar sum. This uses all
spectator Paulis, including weight two, through the physical mass zeros. -/
theorem Encoder.diagonalFrameSum_scalar (V : Encoder) (i a : Fin 4) (ha : a≠0) :
    V.diagonalFrameSum (single i a) =
      (Matrix.trace (V.diagonalFrameSum (single i a))/4) • 1 := by
  apply matrix_scalar_of_transpose_traces
  intro p hp
  have h0 := V.frame_compression_trace 0 0 p (single i a)
  have h1 := V.frame_compression_trace 1 1 p (single i a)
  have hz := V.mixed_trace_zero p i a hp ha
  have he : Matrix.trace (V.tensorMatrix.conjTranspose *
      operator (joinLabel p (single i a)) * V.tensorMatrix) =
      (V.tensorMatrix.conjTranspose * operator (joinLabel p (single i a)) * V.tensorMatrix) 0 0 +
      (V.tensorMatrix.conjTranspose * operator (joinLabel p (single i a)) * V.tensorMatrix) 1 1 := by
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_succ]
  rw [he] at hz
  simp only [Encoder.diagonalFrameSum,Matrix.mul_add,Matrix.trace_add]
  rw [← h0,← h1]
  linear_combination 4*hz

end Orbit2
