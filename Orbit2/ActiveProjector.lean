import Orbit2.PhysicalDefects

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.Quartic Orbit2.PurityReduction
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable def Encoder.activeProjector (V : Encoder) : Defects.ActiveMatrix := Frames.pi V.magicFrames

theorem Encoder.magicFrame_projector (V : Encoder) (j : Fin 2) :
    V.magicFrame j * (V.magicFrame j).conjTranspose =
      V.schmidtFrame j * (V.schmidtFrame j).conjTranspose := by
  unfold Encoder.magicFrame
  rw [Matrix.conjTranspose_mul]
  calc
    _ = V.schmidtFrame j * (magicBasis * magicBasis.conjTranspose) * (V.schmidtFrame j).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [magicBasis_unitary,Matrix.mul_one]

theorem Encoder.activeProjector_frames (V : Encoder) :
    V.activeProjector = V.schmidtFrame 0 * (V.schmidtFrame 0).conjTranspose +
      V.schmidtFrame 1 * (V.schmidtFrame 1).conjTranspose := by
  calc
    _ = V.magicFrame 0 * (V.magicFrame 0).conjTranspose +
        V.magicFrame 1 * (V.magicFrame 1).conjTranspose := by
      ext x y
      simp [Encoder.activeProjector,Frames.pi,Encoder.magicFrames,Matrix.mul_apply,
        Matrix.conjTranspose_apply,Fintype.sum_sum_type]
    _ = _ := by rw [V.magicFrame_projector,V.magicFrame_projector]

theorem Encoder.activeProjector_trace_transport (V : Encoder) (q : Label 4) :
    tau (operator q * V.activeProjector) =
      SS.MacWilliams.trProj V.psi (decode (joinLabel (fun _ => 0) q))/4 := by
  have h0 := V.frame_compression_trace 0 0 (fun _ => 0) q
  have h1 := V.frame_compression_trace 1 1 (fun _ => 0) q
  simp only [operator_zero,Matrix.transpose_one,Matrix.one_mul] at h0 h1
  have hc (j : Fin 2) : Matrix.trace (operator q * (V.schmidtFrame j * (V.schmidtFrame j).conjTranspose)) =
      Matrix.trace ((V.schmidtFrame j).conjTranspose * operator q * V.schmidtFrame j) := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle (operator q) (V.schmidtFrame j) (V.schmidtFrame j).conjTranspose]
  have ht : Matrix.trace (operator q * V.activeProjector) =
      4 * Matrix.trace (V.tensorMatrix.conjTranspose * operator (joinLabel (fun _ => 0) q) * V.tensorMatrix) := by
    rw [V.activeProjector_frames,Matrix.mul_add,Matrix.trace_add]
    rw [hc 0,hc 1]
    rw [← h0,← h1]
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_succ,mul_add]
  unfold tau
  rw [ht,← V.tensor_trace]
  norm_num
  ring

theorem Encoder.physical_trace_zero_of_mass (V : Encoder) (p : Label 6)
    (hm : V.labelMass (Fin.cons 0 p)=0) :
    SS.MacWilliams.trProj V.psi (decode p)=0 := by
  rw [PhysicalFlatness.reference_identity_mass] at hm
  unfold PhysicalFlatness.physicalMass at hm
  apply Complex.normSq_eq_zero.mp
  linarith

theorem Encoder.activeProjector_trace_zero (V : Encoder) (q : Label 4)
    (hm : V.labelMass (PhysicalFlatness.activeEmbedding q)=0) :
    tau (operator q * V.activeProjector)=0 := by
  rw [V.activeProjector_trace_transport]
  have he : PhysicalFlatness.activeEmbedding q = Fin.cons 0 (joinLabel (fun _ => 0) q) := by
    funext i; fin_cases i <;> rfl
  rw [he] at hm
  rw [V.physical_trace_zero_of_mass _ hm]
  simp

theorem Encoder.activeProjector_weight_four_zero (V : Encoder) (q : Label 4)
    (hq : PhysicalFlatness.activeWeight q=4) :
    tau (operator q * V.activeProjector)=0 :=
  V.activeProjector_trace_zero q (PhysicalFlatness.active_four_zero V q hq)

end Orbit2
