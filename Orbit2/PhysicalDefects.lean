import Orbit2.PhysicalCommonJ
import Orbit2.Defects

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.Quartic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem tensor_transpose {n : ℕ} (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (tensor A).transpose = tensor (fun i => (A i).transpose) := by
  ext x y
  simp [tensor,Matrix.transpose_apply]

theorem local_spin_G : ∀ a : Fin 4,
    localG 2 * (localG a).transpose * localG 2 =
      (if a=0 then (1 : GaussianInt) else -1) • localG a := by decide +kernel

theorem local_spin (a : Fin 4) :
    localC 2 * (localC a).transpose * localC 2 =
      (if a=0 then (1 : ℂ) else -1) • localC a := by
  have h := congrArg (fun M => M.map GaussianInt.toComplex) (local_spin_G a)
  have he : (localC 2 * (localC a).transpose * localC 2) =
      (localG 2 * (localG a).transpose * localG 2).map GaussianInt.toComplex := by
    simp [localC,Matrix.map_mul,Matrix.transpose_map]
  rw [he]
  ext x y
  have hxy := congrFun (congrFun h x) y
  by_cases ha : a=0 <;>
    simpa only [ha,if_true,if_false,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,
      GaussianInt.toComplex_mul,GaussianInt.toComplex_neg,map_one,localC] using hxy

noncomputable def activeSpin : Defects.ActiveMatrix := operator (fun _ => 2)

theorem activeSpin_hermitian : activeSpin.conjTranspose = activeSpin :=
  operator_hermitian (fun _ => 2)

theorem activeSpin_square : activeSpin * activeSpin = 1 := by
  unfold activeSpin
  rw [operator_mul,phase_self,(product_eq_zero_iff _ _).mpr rfl,operator_zero]
  simp

theorem activeSpin_single (i a : Fin 4) (ha : a≠0) :
    activeSpin * (operator (single i a)).transpose * activeSpin = -operator (single i a) := by
  unfold activeSpin operator
  rw [tensor_transpose,tensor_mul,tensor_mul]
  simp_rw [local_spin]
  rw [tensor_smul]
  have hp : (∏ j : Fin 4, if single i a j=0 then (1 : ℂ) else -1) = -1 := by
    rw [Finset.prod_eq_single i]
    · simp [single,ha]
    · intro j _ hj
      simp [single,hj]
    · simp
  rw [hp,neg_one_smul]

noncomputable def Encoder.physicalT (V : Encoder) : Defects.ActiveMatrix :=
  Frames.t V.magicFrames activeSpin

/-- Actual T, with normalized mass and all frame defects proved directly
from the encoder's isometry, logical operator, and full weight-two KL. -/
theorem Encoder.physicalT_equations (V : Encoder) :
    Defects.normMass V.physicalT = 1/2 ∧
    Defects.projectionDefect V.physicalT = 0 ∧
    ∀ (i a : Fin 4), a≠0 → Defects.compressionDefect V.physicalT (operator (single i a)) = 0 := by
  refine ⟨Defects.frame_normMass V.magicFrames V.magicFrames_isometry activeSpin
    activeSpin_hermitian activeSpin_square,
    Defects.frame_projectionDefect V.magicFrames V.magicFrames_isometry activeSpin
      activeSpin_hermitian activeSpin_square,?_⟩
  intro i a ha
  exact Defects.frame_compressionDefect V.magicFrames V.magicFrames_isometry activeSpin
    activeSpin_hermitian activeSpin_square (operator (single i a)) (V.activeMu (single i a))
      (V.physical_commonJ i a ha) (activeSpin_single i a ha)

end Orbit2
