import MainTheory.QuaternionThirdTraceFrame
import MainTheory.QuaternionHalfTurnGroup

/-! A body-diagonal third-turn and its Clifford half-turn normalizer. -/

namespace MainTheory.QuaternionThirdCanonicalTargets

noncomputable section

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionSpinMatrices
  MainTheory.QuaternionAxisAngles MainTheory.QuaternionCliffordAxes
  MainTheory.QuaternionRationalNormalizer MainTheory.QuaternionHalfTurnGroup

def bodyThird : unitary ℍ[ℝ] := ⟨⟨1/2,1/2,1/2,1/2⟩,by
  constructor <;> apply Quaternion.ext <;> norm_num⟩

def halfScale : ℝ := (Real.sqrt 2)⁻¹

theorem halfScale_square : halfScale^2=1/2 := by
  rw [halfScale,inv_pow,Real.sq_sqrt (by norm_num)]
  norm_num

def bodyHalf : unitary ℍ[ℝ] := ⟨⟨0,halfScale,-halfScale,0⟩,by
  have hn : Quaternion.normSq (⟨0,halfScale,-halfScale,0⟩ : ℍ[ℝ])=1 := by
    simp only [Quaternion.normSq_def',neg_sq]
    nlinarith [halfScale_square]
  constructor
  · rw [Quaternion.star_mul_self,hn]; rfl
  · rw [Quaternion.self_mul_star,hn]; rfl⟩

theorem bodyThird_re : bodyThird.val.re=1/2 := rfl
theorem bodyHalf_re : bodyHalf.val.re=0 := rfl

theorem target_orthogonal : MainTheory.QuaternionAxisAngles.imaginaryDot bodyThird.val bodyHalf.val=0 := by
  simp only [MainTheory.QuaternionAxisAngles.imaginaryDot,bodyThird,bodyHalf]
  ring

theorem bodyThird_normalizes : Normalizes bodyThird := by
  apply rational_normalizes
  all_goals norm_num [AllowedWithoutQuarter,bodyThird]

theorem bodyThird_inverse_normalizes : Normalizes bodyThird⁻¹ := by
  apply rational_normalizes
  · change AllowedWithoutQuarter (star bodyThird.val).re
    norm_num [AllowedWithoutQuarter,bodyThird]
  · change AllowedWithoutQuarter (star bodyThird.val).imI
    norm_num [AllowedWithoutQuarter,bodyThird]
  · change AllowedWithoutQuarter (star bodyThird.val).imJ
    norm_num [AllowedWithoutQuarter,bodyThird]
  · change AllowedWithoutQuarter (star bodyThird.val).imK
    norm_num [AllowedWithoutQuarter,bodyThird]

theorem conjugate_negative (g s : unitary ℍ[ℝ]) : conjugate (-g) s=conjugate g s := by
  apply Subtype.ext
  simp [conjugate_value,Unitary.coe_neg]

theorem normalizes_negative (g : unitary ℍ[ℝ]) (h : Normalizes g) : Normalizes (-g) := by
  simpa only [Normalizes,conjugate_negative] using h

theorem bodyHalf_action : conjugate bodyHalf axisI= -axisJ ∧
    conjugate bodyHalf axisJ= -axisI ∧ conjugate bodyHalf axisK= -axisK := by
  have hs := halfScale_square
  refine ⟨?_,?_,?_⟩
  all_goals apply Subtype.ext; rw [conjugate_value]; apply Quaternion.ext
  all_goals simp [bodyHalf,axisI,axisJ,axisK,Unitary.coe_neg]
  all_goals nlinarith [hs]

theorem bodyHalf_normalizes : Normalizes bodyHalf := by
  unfold Normalizes
  rw [bodyHalf_action.1,bodyHalf_action.2.1,bodyHalf_action.2.2]
  exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))),Or.inr (Or.inl rfl),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

theorem bodyHalf_inverse_normalizes : Normalizes bodyHalf⁻¹ := by
  have he : bodyHalf⁻¹= -bodyHalf := by
    apply Subtype.ext
    change star bodyHalf.val= -bodyHalf.val
    exact Quaternion.star_eq_neg.mpr bodyHalf_re
  rw [he]
  exact normalizes_negative _ bodyHalf_normalizes

theorem cyclic_normalizes (g : unitary ℍ[ℝ])
    (h : g.val.re^2=1 ∨ g=bodyThird ∨ g=bodyThird⁻¹ ∨
      g= -bodyThird ∨ g= -(bodyThird⁻¹)) : Normalizes g := by
  rcases h with h | rfl | rfl | rfl | rfl
  · exact scalar_normalizes g h
  · exact bodyThird_normalizes
  · exact bodyThird_inverse_normalizes
  · exact normalizes_negative _ bodyThird_normalizes
  · exact normalizes_negative _ bodyThird_inverse_normalizes

end

end MainTheory.QuaternionThirdCanonicalTargets
