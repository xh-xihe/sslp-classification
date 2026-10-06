import MainTheory.Generated.Orbit31DirectTriangles.Type01
import MainTheory.Generated.Orbit31DirectTriangles.Type02

/-! Literal SI equations for the mixed triangle and final twelve-string class.
Each equation follows from actual signed paths and canonical physical rows. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
namespace MainTheory.Orbit31FinalCross
noncomputable section
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31CanonicalPhase
open MainTheory.Orbit31SignedSupport
open MainTheory.Orbit31PermanentAlgebra
open MainTheory.SignedPhaseSupport
open scoped BigOperators

theorem inactive_zero {mask : ℕ} {c : Fin 16 → ℂ} (hm : AmplitudeSupport mask c)
    (j : Fin 16) (hj : active mask j=false) : c j=0 := by
  by_contra hn
  have ha := (hm j).mpr hn
  rw [hj] at ha
  contradiction

namespace Type01
open MainTheory.Generated.Orbit31DirectTriangles.Type01

theorem equation1 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : (c ⟨2,by decide⟩)*(c ⟨10,by decide⟩)+(c ⟨3,by decide⟩)*(c ⟨11,by decide⟩)=0 := by
  have he := weight_one_phase_sum hp hs ⟨1,by decide⟩
  norm_num [A,B,rowPairs,colPairs,Fin.sum_univ_succ,Fin.succ] at he
  have hz0 := inactive_zero hm ⟨0,by decide⟩ (by decide +kernel)
  have hz1 := inactive_zero hm ⟨1,by decide⟩ (by decide +kernel)
  simp at hz0 hz1
  simp [hz0,hz1] at he
  have hs10 := phase_pattern hp hs hm ⟨10,by decide⟩ (by decide +kernel)
  have hs11 := phase_pattern hp hs hm ⟨11,by decide⟩ (by decide +kernel)
  simp [colors,sign] at hs10 hs11
  simp only [hs10,hs11] at he
  have hf : sigma c d anchor*((c ⟨2,by decide⟩)*(c ⟨10,by decide⟩)+(c ⟨3,by decide⟩)*(c ⟨11,by decide⟩))=0 := by
    conv_lhs => simp
    linear_combination (1 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (anchor_nonzero hp hm)

theorem equation2 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : (c ⟨2,by decide⟩)*(c ⟨14,by decide⟩)+(c ⟨3,by decide⟩)*(c ⟨15,by decide⟩)=0 := by
  have he := weight_one_phase_sum hp hs ⟨2,by decide⟩
  norm_num [A,B,rowPairs,colPairs,Fin.sum_univ_succ,Fin.succ] at he
  have hz0 := inactive_zero hm ⟨0,by decide⟩ (by decide +kernel)
  have hz1 := inactive_zero hm ⟨1,by decide⟩ (by decide +kernel)
  simp at hz0 hz1
  simp [hz0,hz1] at he
  have hs14 := phase_pattern hp hs hm ⟨14,by decide⟩ (by decide +kernel)
  have hs15 := phase_pattern hp hs hm ⟨15,by decide⟩ (by decide +kernel)
  simp [colors,sign] at hs14 hs15
  simp only [hs14,hs15] at he
  have hf : sigma c d anchor*((c ⟨2,by decide⟩)*(c ⟨14,by decide⟩)+(c ⟨3,by decide⟩)*(c ⟨15,by decide⟩))=0 := by
    conv_lhs => simp
    linear_combination (1 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (anchor_nonzero hp hm)

theorem equation3 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : (c ⟨10,by decide⟩)*(c ⟨15,by decide⟩)+(c ⟨11,by decide⟩)*(c ⟨14,by decide⟩)=0 := by
  have he := rectangle_phase hp hs ⟨2,by decide⟩ ⟨5,by decide⟩
  dsimp only at he
  norm_num [A,B,rowPairs,colPairs,Fin.sum_univ_succ,Fin.succ] at he
  simp at he
  have hs10 := phase_pattern hp hs hm ⟨10,by decide⟩ (by decide +kernel)
  have hs11 := phase_pattern hp hs hm ⟨11,by decide⟩ (by decide +kernel)
  have hs14 := phase_pattern hp hs hm ⟨14,by decide⟩ (by decide +kernel)
  have hs15 := phase_pattern hp hs hm ⟨15,by decide⟩ (by decide +kernel)
  simp [colors,sign] at hs10 hs11 hs14 hs15
  simp only [hs10,hs11,hs14,hs15] at he
  have hf : sigma c d anchor*((c ⟨10,by decide⟩)*(c ⟨15,by decide⟩)+(c ⟨11,by decide⟩)*(c ⟨14,by decide⟩))=0 := by
    conv_lhs => simp
    linear_combination (1/2 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (anchor_nonzero hp hm)

theorem no_go {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : False :=
  mixed_triangle (c ⟨2,by decide⟩) (c ⟨3,by decide⟩) (c ⟨10,by decide⟩) (c ⟨11,by decide⟩) (c ⟨14,by decide⟩) (c ⟨15,by decide⟩)
    ((hm _).mp (by decide +kernel)) ((hm _).mp (by decide +kernel))
    ((hm _).mp (by decide +kernel)) (equation1 hp hs hm) (equation2 hp hs hm) (equation3 hp hs hm)

end Type01

namespace Type02
open MainTheory.Generated.Orbit31DirectTriangles.Type02

theorem equation1 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : (c ⟨0,by decide⟩)*(c ⟨8,by decide⟩)+(c ⟨1,by decide⟩)*(c ⟨9,by decide⟩)=0 := by
  have he := weight_one_phase_sum hp hs ⟨1,by decide⟩
  norm_num [A,B,rowPairs,colPairs,Fin.sum_univ_succ,Fin.succ] at he
  have hz10 := inactive_zero hm ⟨10,by decide⟩ (by decide +kernel)
  have hz11 := inactive_zero hm ⟨11,by decide⟩ (by decide +kernel)
  simp at hz10 hz11
  simp [hz10,hz11] at he
  have hs8 := phase_pattern hp hs hm ⟨8,by decide⟩ (by decide +kernel)
  have hs9 := phase_pattern hp hs hm ⟨9,by decide⟩ (by decide +kernel)
  simp [colors,sign] at hs8 hs9
  simp only [hs8,hs9] at he
  have hf : sigma c d anchor*((c ⟨0,by decide⟩)*(c ⟨8,by decide⟩)+(c ⟨1,by decide⟩)*(c ⟨9,by decide⟩))=0 := by
    conv_lhs => simp
    linear_combination (1 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (anchor_nonzero hp hm)

theorem equation2 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : (c ⟨4,by decide⟩)*(c ⟨9,by decide⟩)+(c ⟨5,by decide⟩)*(c ⟨8,by decide⟩)=0 := by
  have he := rectangle_phase hp hs ⟨0,by decide⟩ ⟨0,by decide⟩
  dsimp only at he
  norm_num [A,B,rowPairs,colPairs,Fin.sum_univ_succ,Fin.succ] at he
  simp at he
  have hs4 := phase_pattern hp hs hm ⟨4,by decide⟩ (by decide +kernel)
  have hs5 := phase_pattern hp hs hm ⟨5,by decide⟩ (by decide +kernel)
  have hs8 := phase_pattern hp hs hm ⟨8,by decide⟩ (by decide +kernel)
  have hs9 := phase_pattern hp hs hm ⟨9,by decide⟩ (by decide +kernel)
  simp [colors,sign] at hs4 hs5 hs8 hs9
  simp only [hs4,hs5,hs8,hs9] at he
  have hf : sigma c d anchor*((c ⟨4,by decide⟩)*(c ⟨9,by decide⟩)+(c ⟨5,by decide⟩)*(c ⟨8,by decide⟩))=0 := by
    conv_lhs => simp
    linear_combination (1/2 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (anchor_nonzero hp hm)

theorem equation3 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : (c ⟨2,by decide⟩)*(c ⟨14,by decide⟩)+(c ⟨3,by decide⟩)*(c ⟨15,by decide⟩)=0 := by
  have he := weight_one_phase_sum hp hs ⟨2,by decide⟩
  norm_num [A,B,rowPairs,colPairs,Fin.sum_univ_succ,Fin.succ] at he
  have hz12 := inactive_zero hm ⟨12,by decide⟩ (by decide +kernel)
  have hz13 := inactive_zero hm ⟨13,by decide⟩ (by decide +kernel)
  simp at hz12 hz13
  simp [hz12,hz13] at he
  have hs14 := phase_pattern hp hs hm ⟨14,by decide⟩ (by decide +kernel)
  have hs15 := phase_pattern hp hs hm ⟨15,by decide⟩ (by decide +kernel)
  simp [colors,sign] at hs14 hs15
  simp only [hs14,hs15] at he
  have hf : sigma c d anchor*((c ⟨2,by decide⟩)*(c ⟨14,by decide⟩)+(c ⟨3,by decide⟩)*(c ⟨15,by decide⟩))=0 := by
    conv_lhs => simp
    linear_combination (-1 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (anchor_nonzero hp hm)

theorem equation4 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : (c ⟨6,by decide⟩)*(c ⟨15,by decide⟩)+(c ⟨7,by decide⟩)*(c ⟨14,by decide⟩)=0 := by
  have he := rectangle_phase hp hs ⟨1,by decide⟩ ⟨5,by decide⟩
  dsimp only at he
  norm_num [A,B,rowPairs,colPairs,Fin.sum_univ_succ,Fin.succ] at he
  simp at he
  have hs6 := phase_pattern hp hs hm ⟨6,by decide⟩ (by decide +kernel)
  have hs7 := phase_pattern hp hs hm ⟨7,by decide⟩ (by decide +kernel)
  have hs14 := phase_pattern hp hs hm ⟨14,by decide⟩ (by decide +kernel)
  have hs15 := phase_pattern hp hs hm ⟨15,by decide⟩ (by decide +kernel)
  simp [colors,sign] at hs6 hs7 hs14 hs15
  simp only [hs6,hs7,hs14,hs15] at he
  have hf : sigma c d anchor*((c ⟨6,by decide⟩)*(c ⟨15,by decide⟩)+(c ⟨7,by decide⟩)*(c ⟨14,by decide⟩))=0 := by
    conv_lhs => simp
    linear_combination (-1/2 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (anchor_nonzero hp hm)

theorem equation5 {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) : (c ⟨0,by decide⟩)*(c ⟨4,by decide⟩)+(c ⟨1,by decide⟩)*(c ⟨5,by decide⟩)-(c ⟨2,by decide⟩)*(c ⟨6,by decide⟩)-(c ⟨3,by decide⟩)*(c ⟨7,by decide⟩)=0 := by
  have he := weight_one_phase_sum hp hs ⟨0,by decide⟩
  norm_num [A,B,rowPairs,colPairs,Fin.sum_univ_succ,Fin.succ] at he
  simp at he
  have hs4 := phase_pattern hp hs hm ⟨4,by decide⟩ (by decide +kernel)
  have hs5 := phase_pattern hp hs hm ⟨5,by decide⟩ (by decide +kernel)
  have hs6 := phase_pattern hp hs hm ⟨6,by decide⟩ (by decide +kernel)
  have hs7 := phase_pattern hp hs hm ⟨7,by decide⟩ (by decide +kernel)
  simp [colors,sign] at hs4 hs5 hs6 hs7
  simp only [hs4,hs5,hs6,hs7] at he
  have hf : sigma c d anchor*((c ⟨0,by decide⟩)*(c ⟨4,by decide⟩)+(c ⟨1,by decide⟩)*(c ⟨5,by decide⟩)-(c ⟨2,by decide⟩)*(c ⟨6,by decide⟩)-(c ⟨3,by decide⟩)*(c ⟨7,by decide⟩))=0 := by
    conv_lhs => simp
    linear_combination (1 : ℂ)*he
  exact (mul_eq_zero.mp hf).resolve_left (anchor_nonzero hp hm)

theorem commonK {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) :
    ∃ K : ℂ, K ≠ 0 ∧ ∀ e : Fin 4, c (A e)*c (B ⟨0,by decide⟩ e)=K := by
  have hl := product_equality (c ⟨0,by decide⟩) (c ⟨1,by decide⟩) (c ⟨4,by decide⟩) (c ⟨5,by decide⟩) (c ⟨8,by decide⟩) (c ⟨9,by decide⟩)
    ((hm _).mp (by decide +kernel)) (equation1 hp hs hm) (equation2 hp hs hm)
  have hr := product_equality (c ⟨2,by decide⟩) (c ⟨3,by decide⟩) (c ⟨6,by decide⟩) (c ⟨7,by decide⟩) (c ⟨14,by decide⟩) (c ⟨15,by decide⟩)
    ((hm _).mp (by decide +kernel)) (equation3 hp hs hm) (equation4 hp hs hm)
  have hall := common_product ![(c ⟨0,by decide⟩),(c ⟨1,by decide⟩),(c ⟨2,by decide⟩),(c ⟨3,by decide⟩)] ![(c ⟨4,by decide⟩),(c ⟨5,by decide⟩),(c ⟨6,by decide⟩),(c ⟨7,by decide⟩)]
    hl hr (equation5 hp hs hm)
  refine ⟨(c ⟨0,by decide⟩)*(c ⟨4,by decide⟩),mul_ne_zero ((hm _).mp (by decide +kernel))
    ((hm _).mp (by decide +kernel)),?_⟩
  intro e
  fin_cases e
  · rfl
  · exact hl.symm
  · exact hall.1.symm
  · exact hall.2.symm

end Type02

end
end MainTheory.Orbit31FinalCross
