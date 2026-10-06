import Orbit2.MagicBasis
import Orbit2.Frames

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.Quartic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable def Encoder.magicFrame (V : Encoder) (j : Fin 2) :
    Matrix ActiveBits (Fin 4) ℂ := V.schmidtFrame j * magicBasis

theorem Encoder.magicFrame_cross (V : Encoder) (j k : Fin 2) :
    (V.magicFrame j).conjTranspose * V.magicFrame k = if j=k then 1 else 0 := by
  unfold Encoder.magicFrame
  rw [Matrix.conjTranspose_mul]
  calc
    _ = magicBasis.conjTranspose * ((V.schmidtFrame j).conjTranspose * V.schmidtFrame k) * magicBasis := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [V.schmidtFrame_cross]; split_ifs <;> simp [magicBasis_isometry]

noncomputable def Encoder.magicFrames (V : Encoder) : Matrix ActiveBits Frames.LogicalFrame ℂ :=
  Matrix.fromCols (V.magicFrame 0) (V.magicFrame 1)

theorem Encoder.magicFrames_isometry (V : Encoder) :
    V.magicFrames.conjTranspose * V.magicFrames = 1 := by
  ext b c
  rcases b with b|b <;> rcases c with c|c
  · have h := congrFun (congrFun (V.magicFrame_cross 0 0) b) c
    simpa [Encoder.magicFrames,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using h
  · have h := congrFun (congrFun (V.magicFrame_cross 0 1) b) c
    simpa [Encoder.magicFrames,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using h
  · have h := congrFun (congrFun (V.magicFrame_cross 1 0) b) c
    simpa [Encoder.magicFrames,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using h
  · have h := congrFun (congrFun (V.magicFrame_cross 1 1) b) c
    simpa [Encoder.magicFrames,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using h

noncomputable def Encoder.magicCompression (V : Encoder) (j k : Fin 2) (q : Label 4) :
    Matrix (Fin 4) (Fin 4) ℂ := (V.magicFrame j).conjTranspose * operator q * V.magicFrame k

theorem Encoder.magicCompression_transport (V : Encoder) (j k : Fin 2) (q : Label 4) :
    V.magicCompression j k q = magicBasis.conjTranspose *
      ((V.schmidtFrame j).conjTranspose * operator q * V.schmidtFrame k) * magicBasis := by
  simp [Encoder.magicCompression,Encoder.magicFrame,Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem Encoder.magicCompression_symmetric (V : Encoder) (j k : Fin 2) (i a : Fin 4) (ha : a≠0) :
    (V.magicCompression j k (single i a)).transpose = V.magicCompression j k (single i a) := by
  rw [V.magicCompression_transport]
  exact magicBasis_compression_symmetric _ (V.frame_spin_symmetry j k i a ha)

noncomputable def Encoder.activeMu (V : Encoder) (q : Label 4) : ℂ :=
  Matrix.trace (V.diagonalFrameSum q)/8

theorem Encoder.magicCompression_diagonal_sum (V : Encoder) (i a : Fin 4) (ha : a≠0) :
    V.magicCompression 0 0 (single i a) + V.magicCompression 1 1 (single i a) =
      (2 * V.activeMu (single i a)) • 1 := by
  rw [V.magicCompression_transport,V.magicCompression_transport]
  rw [← Matrix.add_mul,← Matrix.mul_add]
  change magicBasis.conjTranspose * V.diagonalFrameSum (single i a) * magicBasis = _
  rw [V.diagonalFrameSum_scalar i a ha,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,magicBasis_isometry]
  congr 1
  unfold Encoder.activeMu
  ring

theorem commonJ_symmetric_blocks
    (R C D E : Matrix (Fin 4) (Fin 4) ℂ) (μ : ℂ)
    (hR : R.transpose=R) (hC : C.transpose=C) (hD : D.transpose=D) (hE : E.transpose=E)
    (hs : R+E=(2*μ) • 1) :
    Matrix.fromBlocks R C D E * Frames.J + Frames.J * (Matrix.fromBlocks R C D E).transpose =
      (2*μ) • Frames.J := by
  simp only [Frames.J,Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_add,Matrix.fromBlocks_smul,hR,hC,hD,hE,
    Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_one,Matrix.one_mul,
    Matrix.mul_neg,Matrix.neg_mul,smul_zero,smul_neg]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_,?_,?_,?_⟩
  · module
  · simpa using hs
  · rw [← hs]
    module
  · module

theorem Encoder.magicFrames_compression_blocks (V : Encoder) (q : Label 4) :
    V.magicFrames.conjTranspose * operator q * V.magicFrames =
      Matrix.fromBlocks (V.magicCompression 0 0 q) (V.magicCompression 0 1 q)
        (V.magicCompression 1 0 q) (V.magicCompression 1 1 q) := by
  ext b c
  rcases b with b|b <;> rcases c with c|c <;>
    simp [Encoder.magicFrames,Encoder.magicCompression,Matrix.mul_apply,Matrix.conjTranspose_apply]

/-- The common-J equation is now derived from every actual orbit-2 Encoder. -/
theorem Encoder.physical_commonJ (V : Encoder) (i a : Fin 4) (ha : a≠0) :
    (V.magicFrames.conjTranspose * operator (single i a) * V.magicFrames) * Frames.J +
      Frames.J * (V.magicFrames.conjTranspose * operator (single i a) * V.magicFrames).transpose =
        (2 * V.activeMu (single i a)) • Frames.J := by
  rw [V.magicFrames_compression_blocks]
  exact commonJ_symmetric_blocks _ _ _ _ _
    (V.magicCompression_symmetric 0 0 i a ha) (V.magicCompression_symmetric 0 1 i a ha)
    (V.magicCompression_symmetric 1 0 i a ha) (V.magicCompression_symmetric 1 1 i a ha)
    (V.magicCompression_diagonal_sum i a ha)

end Orbit2
