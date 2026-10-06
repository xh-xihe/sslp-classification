import MainTheory.QuaternionCliffordMatrixBridge

/-! The trace values of a proper signed permutation of the quaternion axes. -/

namespace MainTheory.QuaternionCliffordTrace

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisFrames
  MainTheory.QuaternionCliffordAxes MainTheory.QuaternionOrthogonalFrame
  MainTheory.QuaternionProjectiveOrders

set_option maxHeartbeats 8000000

theorem trace_identity (q : unitary ℍ[ℝ]) :
    (conjugate q axisI).val.imI+(conjugate q axisJ).val.imJ+
      (conjugate q axisK).val.imK=4*q.val.re^2-1 := by
  have hn := normSq_unitary q
  simp only [Quaternion.normSq_def'] at hn
  simp only [conjugate_value,axisI,axisJ,axisK,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul,Quaternion.re_mul,
    Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star]
  nlinarith [hn]

theorem allowed_trace (q : unitary ℍ[ℝ]) (hq : Normalizes q) :
    AllowedScalar q.val.re := by
  have he := trace_identity q
  have hk : conjugate q axisK=conjugate q axisI*conjugate q axisJ := by
    rw [← conjugate_mul,basis_products.1]
  have ha := conjugate_anti q axisI axisJ basis_anti
  rcases hq.1 with hi | hi | hi | hi | hi | hi <;>
    rcases hq.2.1 with hj | hj | hj | hj | hj | hj
  all_goals rw [hi,hj] at hk ha he
  all_goals simp only [hk] at he
  all_goals norm_num [Anti,Subtype.ext_iff,Unitary.coe_neg,
    quaternion_eq_iff,axisI,axisJ,axisK] at ha
  all_goals norm_num [Unitary.coe_neg,axisI,axisJ,axisK] at he
  all_goals simp only [AllowedScalar]
  all_goals first | left; nlinarith | right; left; nlinarith |
    right; right; left; nlinarith | right; right; right; nlinarith

end

end MainTheory.QuaternionCliffordTrace
