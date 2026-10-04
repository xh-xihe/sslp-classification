import Orbit2.Complete
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The literal active projector has rank eight, as well as trace eight. -/

namespace MainTheory.Orbit2ActiveProjectorRank

noncomputable section

open ComplexOrder

theorem rank_eight (V : Orbit2.Encoder) : V.activeProjector.rank=8 := by
  rw [Orbit2.Encoder.activeProjector,Orbit2.Frames.pi,Matrix.rank_self_mul_conjTranspose,
    ← Matrix.rank_conjTranspose_mul_self,V.magicFrames_isometry,Matrix.rank_one]
  norm_num [Orbit2.Frames.LogicalFrame]

theorem projector (V : Orbit2.Encoder) :
    V.activeProjector.conjTranspose=V.activeProjector ∧
      V.activeProjector*V.activeProjector=V.activeProjector ∧
      Matrix.trace V.activeProjector=8 ∧ V.activeProjector.rank=8 := by
  refine ⟨?_,?_,?_,rank_eight V⟩
  · exact Orbit2.Frames.pi_hermitian V.magicFrames V.magicFrames_isometry
  · change Orbit2.Frames.pi V.magicFrames*Orbit2.Frames.pi V.magicFrames=Orbit2.Frames.pi V.magicFrames
    exact Orbit2.Frames.pi_idempotent V.magicFrames V.magicFrames_isometry
  · change Matrix.trace (Orbit2.Frames.pi V.magicFrames)=8
    exact Orbit2.Frames.pi_trace V.magicFrames V.magicFrames_isometry

end

end MainTheory.Orbit2ActiveProjectorRank
