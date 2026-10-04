import Orbit2.PhysicalSpectral

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.Quartic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem hamming_parity_cases : ∀ x y : ActiveBits, hamming x y≠3 →
    (evenBits x ↔ evenBits y) ∨ hamming x y=1 := by decide +kernel
theorem hamming_complement : ∀ x y : ActiveBits,
    hamming x (complementBits y)=4-hamming x y := by decide +kernel
theorem hamming_complement_iff : ∀ x y : ActiveBits,
    hamming x (complementBits y)=3 ↔ hamming x y=1 := by decide +kernel

theorem Encoder.physicalOmega_support (V : Encoder) (x y : ActiveBits) (h : hamming x y≠3) :
    V.physicalOmega x y=0 := by
  rcases hamming_parity_cases x y h with hp|hd
  · exact V.physicalOmega_parity_zero x y hp
  · exact V.physicalOmega_distance_one_zero x y hd

theorem activeSpin_transpose_G : ∀ x y : ActiveBits,
    (∏ i, localG 2 (y i) (x i))=(∏ i, localG 2 (x i) (y i)) := by decide +kernel

theorem activeSpin_transpose : activeSpin.transpose=activeSpin := by
  ext x y
  have h := congrArg GaussianInt.toComplex (activeSpin_transpose_G x y)
  simpa only [activeSpin,operator,tensor,Matrix.transpose_apply,localC,Matrix.map_apply,map_prod] using h

theorem activeSpin_flip (x : ActiveBits) : HilbertBridge.flip (fun _ : Fin 4 => 2) x=complementBits x := by
  funext i
  change FiveQubit.flipSite 2 (x i)=FiveQubit.flipSite 1 (x i)
  generalize x i = a
  fin_cases a <;> rfl

theorem Encoder.physicalT_entry (V : Encoder) (x y : ActiveBits) :
    V.physicalT x y = V.physicalOmega x (complementBits y) *
      (∏ i, localC 2 (y i) (complementBits y i)) := by
  have hs (z : ActiveBits) : activeSpin z y=activeSpin y z := by
    have h := congrFun (congrFun activeSpin_transpose y) z
    exact h
  change (V.physicalOmega * activeSpin) x y = _
  rw [Matrix.mul_apply]
  simp_rw [hs]
  simp only [activeSpin,HilbertBridge.operator_row,activeSpin_flip,mul_ite,mul_zero]
  simp

/-- The actual T has only Hamming-distance-one matrix entries. -/
theorem Encoder.physicalT_support (V : Encoder) (x y : ActiveBits) (h : hamming x y≠1) :
    V.physicalT x y=0 := by
  rw [V.physicalT_entry,V.physicalOmega_support x (complementBits y) (by
    intro hd; exact h ((hamming_complement_iff x y).mp hd)),zero_mul]

theorem Encoder.physicalT_spin_skew (V : Encoder) :
    activeSpin * V.physicalT.transpose * activeSpin = -V.physicalT :=
  Frames.t_spin_skew V.magicFrames V.magicFrames_isometry activeSpin activeSpin_transpose activeSpin_square

end Orbit2
