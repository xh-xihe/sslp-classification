import MainTheory.QuaternionThirdOrbit

/-! The cyclic part of a bounded subgroup about a third-turn axis. -/

namespace MainTheory.QuaternionCommutingThird

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisAngles
  MainTheory.QuaternionThirdOrbit

theorem lagrange (q g : ℍ[ℝ]) :
    (imaginaryDot q g)^2+(q.imI*g.imJ-q.imJ*g.imI)^2+
      (q.imJ*g.imK-q.imK*g.imJ)^2+(q.imK*g.imI-q.imI*g.imK)^2 =
      imaginaryDot q q*imaginaryDot g g := by
  unfold imaginaryDot; ring

theorem commuting_dot_square (q g : unitary ℍ[ℝ]) (h : q*g=g*q) :
    (imaginaryDot q.val g.val)^2=(1-q.val.re^2)*(1-g.val.re^2) := by
  have hI := congrArg (fun q : unitary ℍ[ℝ] => q.val.imI) h
  have hJ := congrArg (fun q : unitary ℍ[ℝ] => q.val.imJ) h
  have hK := congrArg (fun q : unitary ℍ[ℝ] => q.val.imK) h
  simp only [Submonoid.coe_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul] at hI hJ hK
  have hcI : q.val.imI*g.val.imJ-q.val.imJ*g.val.imI=0 := by linarith [hK]
  have hcJ : q.val.imJ*g.val.imK-q.val.imK*g.val.imJ=0 := by linarith [hI]
  have hcK : q.val.imK*g.val.imI-q.val.imI*g.val.imK=0 := by linarith [hJ]
  have hq := normSq_unitary q
  have hg := normSq_unitary g
  rw [Quaternion.normSq_def'] at hq hg
  have hnq : imaginaryDot q.val q.val=1-q.val.re^2 := by unfold imaginaryDot; nlinarith
  have hng : imaginaryDot g.val g.val=1-g.val.re^2 := by unfold imaginaryDot; nlinarith
  have he := lagrange q.val g.val
  rw [hcI,hcJ,hcK,hnq,hng] at he
  simpa using he

theorem parallel_thirds (q g : unitary ℍ[ℝ]) (hq : q.val.re=1/2) (hg : g.val.re=1/2)
    (h : (imaginaryDot q.val g.val)^2=9/16) : g=q ∨ g=q⁻¹ := by
  have hz : (imaginaryDot q.val g.val-3/4)*(imaginaryDot q.val g.val+3/4)=0 := by nlinarith
  rcases mul_eq_zero.mp hz with hz | hz
  · left; apply same_trace_equal g q (hg.trans hq.symm)
    rw [dot_symm,hq]; linarith
  · right; apply same_trace_equal g q⁻¹
    · change g.val.re=(star q.val).re; simp only [Quaternion.re_star,hg,hq]
    · change imaginaryDot g.val (star q.val)=1-(star q.val).re^2
      have hd : imaginaryDot g.val q.val= -3/4 := by rw [dot_symm]; linarith
      simp only [imaginaryDot,Quaternion.re_star,Quaternion.imI_star,
        Quaternion.imJ_star,Quaternion.imK_star,hq]
      unfold imaginaryDot at hd
      linarith

theorem cyclic_part (q g : unitary ℍ[ℝ]) (hq : q.val.re=1/2)
    (hg : AllowedWithoutQuarter g.val.re) (hprod : AllowedWithoutQuarter (q*g).val.re)
    (hcomm : q*g=g*q) :
    g.val.re^2=1 ∨ g=q ∨ g=q⁻¹ ∨ g= -q ∨ g= -(q⁻¹) := by
  have hd := commuting_dot_square q g hcomm
  rw [hq] at hd
  rcases rational_scalar g.val.re hg with hr | hr | hr | hr | hr
  · left; rw [hr]; norm_num
  · left; rw [hr]; norm_num
  · exfalso
    have he : (q*g).val.re= -imaginaryDot q.val g.val := by
      change (q.val*g.val).re= -imaginaryDot q.val g.val
      simp only [Quaternion.re_mul,imaginaryDot,hr]; ring
    rw [he] at hprod
    rw [hr] at hd
    rcases hprod with hprod | hprod | hprod <;> nlinarith
  · have hp := parallel_thirds q g hq hr (by rw [hr] at hd; nlinarith)
    rcases hp with hp | hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hp))
  · have hgn : (-g).val.re=1/2 := by norm_num [Unitary.coe_neg,hr]
    have hdneg : (imaginaryDot q.val (-g).val)^2=9/16 := by
      have he : imaginaryDot q.val (-g).val= -imaginaryDot q.val g.val := by
        simp only [imaginaryDot,Unitary.coe_neg,Quaternion.imI_neg,Quaternion.imJ_neg,
          Quaternion.imK_neg]; ring
      rw [he,neg_sq]
      rw [hr] at hd
      nlinarith
    rcases parallel_thirds q (-g) hq hgn hdneg with he | he
    · right; right; right; left
      apply Subtype.ext
      have hv := congrArg Subtype.val he
      simpa [Unitary.coe_neg] using congrArg Neg.neg hv
    · right; right; right; right
      apply Subtype.ext
      have hv := congrArg Subtype.val he
      simpa [Unitary.coe_neg] using congrArg Neg.neg hv

end

end MainTheory.QuaternionCommutingThird
