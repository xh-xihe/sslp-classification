import MainTheory.QuaternionCliffordAxes

/-! Coordinate form of the subgroup preserving a fixed unoriented axis. -/

namespace MainTheory.QuaternionAxisNormalizerShape

noncomputable section

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionCliffordAxes
  MainTheory.QuaternionAxisGeometry MainTheory.QuaternionProjectiveOrders

theorem intertwiner (g s t : unitary ℍ[ℝ]) (h : conjugate g s=t) : g*s=t*g := by
  have he := congrArg (fun q => q*g) h
  simpa only [conjugate,mul_assoc,inv_mul_cancel,mul_one] using he

theorem commutes_I_shape (g : unitary ℍ[ℝ]) (h : g*axisI=axisI*g) :
    g.val.imJ=0 ∧ g.val.imK=0 := by
  have hj := congrArg (fun q : unitary ℍ[ℝ] => q.val.imJ) h
  have hk := congrArg (fun q : unitary ℍ[ℝ] => q.val.imK) h
  simp [axisI] at hj hk
  constructor <;> linarith

theorem axis_positive_shape (g : unitary ℍ[ℝ]) (h : conjugate g axisI=axisI) :
    g.val.imJ=0 ∧ g.val.imK=0 := commutes_I_shape g (intertwiner g _ _ h)

theorem axis_negative_shape (g : unitary ℍ[ℝ]) (h : conjugate g axisI= -axisI) :
    g.val.re=0 ∧ g.val.imI=0 := by
  have he := intertwiner g _ _ h
  have hr := congrArg (fun q : unitary ℍ[ℝ] => q.val.re) he
  have hi := congrArg (fun q : unitary ℍ[ℝ] => q.val.imI) he
  simp [axisI,Unitary.coe_neg] at hr hi
  constructor <;> linarith

theorem quarter_root_I (q : unitary ℍ[ℝ]) (hq : 2*q.val.re^2=1)
    (h : q^2=axisI) : q.val.imI=q.val.re ∧ q.val.imJ=0 ∧ q.val.imK=0 := by
  have hc : q*axisI=axisI*q := by rw [← h]; group
  obtain ⟨hj,hk⟩ := commutes_I_shape q hc
  have hi := congrArg (fun q : unitary ℍ[ℝ] => q.val.imI) h
  rw [pow_two] at hi
  simp [axisI] at hi
  have hn : q.val.re≠0 := by intro he; rw [he] at hq; norm_num at hq
  have he : q.val.re*(q.val.imI-q.val.re)=0 := by nlinarith [hi,hq]
  exact ⟨by linarith [(mul_eq_zero.mp he).resolve_left hn],hj,hk⟩

theorem coordinate_neg (s : unitary ℍ[ℝ]) (h : CoordinateAxis s) :
    CoordinateAxis (-s) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [CoordinateAxis,Subtype.ext_iff,quaternion_eq_iff,
    Unitary.coe_neg,axisI,axisJ,axisK]

theorem coordinate_image (g s : unitary ℍ[ℝ]) (hg : Normalizes g)
    (hs : CoordinateAxis s) : CoordinateAxis (conjugate g s) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg.1
  · rw [MainTheory.QuaternionOrthogonalFrame.conjugate_neg]; exact coordinate_neg _ hg.1
  · exact hg.2.1
  · rw [MainTheory.QuaternionOrthogonalFrame.conjugate_neg]; exact coordinate_neg _ hg.2.1
  · exact hg.2.2
  · rw [MainTheory.QuaternionOrthogonalFrame.conjugate_neg]; exact coordinate_neg _ hg.2.2

theorem normalizes_mul (g h : unitary ℍ[ℝ]) (hg : Normalizes g) (hh : Normalizes h) :
    Normalizes (g*h) := by
  unfold Normalizes
  simp only [conjugate_comp]
  exact ⟨coordinate_image _ _ hg hh.1,coordinate_image _ _ hg hh.2.1,
    coordinate_image _ _ hg hh.2.2⟩

theorem normalizes_axisJ_inv : Normalizes axisJ⁻¹ := by
  have he : axisJ⁻¹= -axisJ := by
    apply Subtype.ext
    change star axisJ.val= -axisJ.val
    apply Quaternion.ext <;> norm_num [axisJ]
  rw [he]
  norm_num [Normalizes,CoordinateAxis,Subtype.ext_iff,conjugate_value,
    quaternion_eq_iff,Unitary.coe_neg,axisI,axisJ,axisK]

end

end MainTheory.QuaternionAxisNormalizerShape
