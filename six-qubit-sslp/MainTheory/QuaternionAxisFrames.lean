import MainTheory.QuaternionAxisConjugation

/-! Pure axes and unitary frame changes used by the common Clifford basis. -/

namespace MainTheory.QuaternionAxisFrames

noncomputable section

open Quaternion MainTheory.QuaternionAxisConjugation

def axisI : unitary ℍ[ℝ] := ⟨⟨0,1,0,0⟩,by
  constructor <;> apply Quaternion.ext <;> norm_num⟩
def axisJ : unitary ℍ[ℝ] := ⟨⟨0,0,1,0⟩,by
  constructor <;> apply Quaternion.ext <;> norm_num⟩
def axisK : unitary ℍ[ℝ] := ⟨⟨0,0,0,1⟩,by
  constructor <;> apply Quaternion.ext <;> norm_num⟩

theorem axisI_pure : axisI.val.re = 0 := rfl
theorem axisJ_pure : axisJ.val.re = 0 := rfl
theorem axisK_pure : axisK.val.re = 0 := rfl

theorem basis_products : axisI*axisJ = axisK ∧ axisJ*axisI = -axisK := by
  constructor <;> apply Subtype.ext <;> apply Quaternion.ext <;>
    norm_num [axisI,axisJ,axisK,Unitary.coe_neg]

def conjugate (u s : unitary ℍ[ℝ]) : unitary ℍ[ℝ] := u*s*u⁻¹

theorem conjugate_value (u s : unitary ℍ[ℝ]) :
    (conjugate u s).val = u.val*s.val*star u.val := rfl

theorem conjugate_pure (u s : unitary ℍ[ℝ]) (hs : s.val.re = 0) :
    (conjugate u s).val.re = 0 := by
  apply Quaternion.star_eq_neg.mp
  rw [conjugate_value]
  have hstar : star s.val = -s.val := Quaternion.star_eq_neg.mpr hs
  simp only [star_mul,star_star,hstar,mul_neg,neg_mul,mul_assoc]

theorem conjugate_comp (u v s : unitary ℍ[ℝ]) :
    conjugate (v*u) s = conjugate v (conjugate u s) := by
  simp only [conjugate,mul_inv_rev]
  group

theorem axes_distinct : axisI.val ≠ axisJ.val ∧ axisI.val ≠ -axisJ.val := by
  constructor <;> intro h
  · have he := congrArg (fun q : ℍ[ℝ] => q.imI) h
    norm_num [axisI,axisJ] at he
  · have he := congrArg (fun q : ℍ[ℝ] => q.imI) h
    norm_num [axisI,axisJ] at he

theorem any_axis (s t : unitary ℍ[ℝ]) (hs : s.val.re = 0) (ht : t.val.re = 0) :
    ∃ u : unitary ℍ[ℝ], conjugate u s = t := by
  by_cases hst : s.val ≠ -t.val
  · obtain ⟨u,hu⟩ := conjugate_axis s t hs ht hst
    exact ⟨u,Subtype.ext hu⟩
  · have he : s.val = -t.val := not_ne_iff.mp hst
    have pivot : ∃ r : unitary ℍ[ℝ],r.val.re = 0 ∧
        s.val ≠ -r.val ∧ r.val ≠ -t.val := by
      by_cases hi : s.val = -axisI.val
      · refine ⟨axisJ,axisJ_pure,?_,?_⟩
        · intro hj
          have hx : axisI.val = axisJ.val := neg_injective (hi.symm.trans hj)
          exact axes_distinct.1 hx
        · intro hj
          have hsJ : s.val = axisJ.val := he.trans hj.symm
          have hx : -axisI.val = axisJ.val := hi.symm.trans hsJ
          have hiJ : axisI.val = -axisJ.val := by
            simpa only [neg_neg] using congrArg Neg.neg hx
          exact axes_distinct.2 hiJ
      · by_cases hj : axisI.val = -t.val
        · refine ⟨axisJ,axisJ_pure,?_,?_⟩
          · intro hJ
            have hx := (he.trans hj.symm).symm.trans hJ
            exact axes_distinct.2 hx
          · intro hJ
            exact axes_distinct.1 (hj.trans hJ.symm)
        · exact ⟨axisI,axisI_pure,hi,hj⟩
    obtain ⟨r,hr,hsr,hrt⟩ := pivot
    obtain ⟨u,hu⟩ := conjugate_axis s r hs hr hsr
    obtain ⟨v,hv⟩ := conjugate_axis r t hr ht hrt
    refine ⟨v*u,?_⟩
    rw [conjugate_comp,show conjugate u s=r from Subtype.ext hu]
    exact Subtype.ext hv

end

end MainTheory.QuaternionAxisFrames
