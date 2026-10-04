import Orbit2.ProjectorSupport

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def evenBits (x : ActiveBits) : Prop := (∑ i, (x i).val)%2=0
instance (x : ActiveBits) : Decidable (evenBits x) := inferInstanceAs (Decidable ((∑ i, (x i).val)%2=0))

theorem Z_phase_G : ∀ x : ActiveBits,
    (∏ i, localG 3 (x i) (x i)) = if evenBits x then (1 : GaussianInt) else -1 := by decide +kernel

theorem Z_phase (x : ActiveBits) :
    (∏ i, localC 3 (x i) (x i)) = if evenBits x then (1 : ℂ) else -1 := by
  have h := congrArg GaussianInt.toComplex (Z_phase_G x)
  simpa [localC,Matrix.map_apply,map_prod,apply_ite,GaussianInt.toComplex_neg] using h

theorem Z_action {β : Type*} [Fintype β] [DecidableEq β]
    (M : Matrix ActiveBits β ℂ) (x : ActiveBits) (j : β) :
    (operator (fun _ : Fin 4 => 3) * M) x j =
      (if evenBits x then (1 : ℂ) else -1) * M x j := by
  have hf : HilbertBridge.flip (fun _ : Fin 4 => 3) x = x := by
    funext i
    change FiveQubit.flipSite 3 (x i)=x i
    generalize x i = b
    fin_cases b <;> rfl
  simp only [Matrix.mul_apply,HilbertBridge.operator_row,hf,ite_mul,zero_mul]
  simp [Finset.sum_ite_eq',Z_phase]

/-- Each actual Schmidt frame has zero rows in the wrong parity sector. -/
theorem Encoder.schmidtFrame_wrong_parity (V : Encoder) (j : Fin 2) (x : ActiveBits)
    (hp : evenBits x ↔ j≠0) (b : SpectatorBits) : V.schmidtFrame j x b=0 := by
  have h := congrFun (congrFun (V.schmidtFrame_parity j) x) b
  rw [Z_action,Matrix.smul_apply] at h
  by_cases he : evenBits x
  · have hj : j≠0 := hp.mp he
    simp only [he,hj,if_true,if_false,smul_eq_mul,one_mul,neg_one_mul] at h
    linear_combination h/2
  · have hj : j=0 := by by_contra hj; exact he (hp.mpr hj)
    simp only [he,hj,if_true,if_false,smul_eq_mul,one_mul,neg_one_mul] at h
    rw [hj]
    linear_combination -h/2

theorem Encoder.magicFrame_wrong_parity (V : Encoder) (j : Fin 2) (x : ActiveBits)
    (hp : evenBits x ↔ j≠0) (b : Fin 4) : V.magicFrame j x b=0 := by
  unfold Encoder.magicFrame
  simp only [Matrix.mul_apply,V.schmidtFrame_wrong_parity j x hp,zero_mul,Finset.sum_const_zero]

/-- The physical active projector preserves parity. -/
theorem Encoder.activeProjector_parity_zero (V : Encoder) (x y : ActiveBits)
    (hp : ¬ (evenBits x ↔ evenBits y)) : V.activeProjector x y=0 := by
  rw [V.activeProjector_frames]
  simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
  by_cases hx : evenBits x
  · have hy : ¬ evenBits y := by intro hy; exact hp (by simp [hx,hy])
    have hx1 : evenBits x ↔ (1 : Fin 2)≠0 := by simp [hx]
    have hy0 : evenBits y ↔ (0 : Fin 2)≠0 := by simp [hy]
    simp [V.schmidtFrame_wrong_parity 1 x hx1,V.schmidtFrame_wrong_parity 0 y hy0]
  · have hy : evenBits y := by by_contra hy; exact hp (by simp [hx,hy])
    have hx0 : evenBits x ↔ (0 : Fin 2)≠0 := by simp [hx]
    have hy1 : evenBits y ↔ (1 : Fin 2)≠0 := by simp [hy]
    simp [V.schmidtFrame_wrong_parity 0 x hx0,V.schmidtFrame_wrong_parity 1 y hy1]

noncomputable def Encoder.physicalOmega (V : Encoder) : Defects.ActiveMatrix := Frames.omega V.magicFrames

theorem Encoder.physicalOmega_blocks (V : Encoder) :
    V.physicalOmega = V.magicFrame 0 * (V.magicFrame 1).transpose -
      V.magicFrame 1 * (V.magicFrame 0).transpose := by
  ext x y
  simp [Encoder.physicalOmega,Frames.omega,Frames.J,Encoder.magicFrames,Matrix.mul_apply,
    Matrix.transpose_apply,Matrix.sub_apply,Fintype.sum_sum_type,Matrix.one_apply,
    Finset.sum_neg_distrib,eq_comm]
  ring

theorem Encoder.physicalOmega_parity_zero (V : Encoder) (x y : ActiveBits)
    (hp : evenBits x ↔ evenBits y) : V.physicalOmega x y=0 := by
  rw [V.physicalOmega_blocks]
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply]
  by_cases hx : evenBits x
  · have hy : evenBits y := hp.mp hx
    have hx1 : evenBits x ↔ (1 : Fin 2)≠0 := by simp [hx]
    have hy1 : evenBits y ↔ (1 : Fin 2)≠0 := by simp [hy]
    simp [V.magicFrame_wrong_parity 1 x hx1,V.magicFrame_wrong_parity 1 y hy1]
  · have hy : ¬ evenBits y := by intro hy; exact hx (hp.mpr hy)
    have hx0 : evenBits x ↔ (0 : Fin 2)≠0 := by simp [hx]
    have hy0 : evenBits y ↔ (0 : Fin 2)≠0 := by simp [hy]
    simp [V.magicFrame_wrong_parity 0 x hx0,V.magicFrame_wrong_parity 0 y hy0]

end Orbit2
