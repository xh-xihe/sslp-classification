import Orbit2.LowWeightFlatness
import Orbit2.PauliReconstruction

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.HilbertBridge Orbit2.PurityReduction
open SS.MacWilliams
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def spectatorPauli (p : Label 2) : Label 6 := ![p 0,p 1,0,0,0,0]

theorem spectator_weight : ∀ p : Label 2,
    (∑ i, if spectatorPauli p i=0 then 0 else 1 : ℕ) ≤ 2 := by decide +kernel

theorem Encoder.tensor_trace (V : Encoder) (p : Label 6) :
    trProj V.psi (decode p) = Matrix.trace (V.tensorMatrix.conjTranspose * operator p * V.tensorMatrix) := by
  unfold trProj Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro j _
  have h := compression V.tensorMatrix (decode p) j j
  rwa [V.tensor_words,label_decode] at h

theorem spectator_phi_supported (p : Label 2) :
    supported (Fin.cons (0 : Fin 4) (spectatorPauli p)) B := by
  unfold supported
  simp only [decide_eq_true_eq]
  intro i
  fin_cases i <;> simp [spectatorPauli,B] <;> rfl

theorem spectator_phi_nonzero (p : Label 2) (hp : p ≠ fun _ => 0) :
    (Fin.cons (0 : Fin 4) (spectatorPauli p) : Label 7) ≠ (fun _ => (0 : Fin 4)) := by
  intro h
  apply hp
  funext i
  fin_cases i
  · have h0 := congrFun h ⟨1,by decide⟩
    exact h0
  · have h1 := congrFun h ⟨2,by decide⟩
    exact h1

/-- Every nonidentity spectator Pauli has zero compression for the actual code,
including the weight-two spectator Paulis. -/
theorem Encoder.spectator_detection (V : Encoder) (p : Label 2) :
    V.tensorMatrix.conjTranspose * operator (spectatorPauli p) * V.tensorMatrix =
      if p=(fun _ => 0) then 1 else 0 := by
  by_cases hp : p=(fun _ => 0)
  · subst p
    have he : spectatorPauli (fun _ : Fin 2 => 0) = (fun _ => 0) := by
      funext i; fin_cases i <;> rfl
    rw [he,operator_zero,Matrix.mul_one,V.tensor_isometry]
    simp
  · obtain ⟨c,hc⟩ := V.tensor_KL (spectatorPauli p) (spectator_weight p)
    have hsp : spectatorMass (Fin.cons (0 : Fin 4) (spectatorPauli p)) := by
      simp only [spectatorMass,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨spectator_phi_supported p,spectator_phi_nonzero p hp⟩
    have hm := PhysicalFlatness.target_masses_zero V _ (PhysicalFlatness.spectator_positive _ hsp)
    rw [PhysicalFlatness.reference_identity_mass] at hm
    unfold PhysicalFlatness.physicalMass at hm
    have ht : trProj V.psi (decode (spectatorPauli p)) = 0 := by
      apply Complex.normSq_eq_zero.mp
      linarith
    rw [V.tensor_trace,hc,Matrix.trace_smul] at ht
    have hi : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by norm_num
    rw [hi] at ht
    have hz : c=0 := by simp only [smul_eq_mul] at ht; linear_combination ht/2
    rw [hc,hz]
    simp [hp]

end Orbit2
