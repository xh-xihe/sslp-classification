import MainTheory.QuaternionCliffordAxes

/-! The rational unit quaternion coordinates forced by a Pauli frame. -/

namespace MainTheory.QuaternionRationalNormalizer

noncomputable section

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

open Quaternion MainTheory.QuaternionSpinMatrices MainTheory.QuaternionAxisFrames
  MainTheory.QuaternionAxisAngles MainTheory.QuaternionCliffordAxes
  MainTheory.QuaternionAxisGeometry

theorem rational_normalizes (q : unitary ℍ[ℝ])
    (ha : AllowedWithoutQuarter q.val.re) (hb : AllowedWithoutQuarter q.val.imI)
    (hc : AllowedWithoutQuarter q.val.imJ) (hd : AllowedWithoutQuarter q.val.imK) :
    Normalizes q := by
  have hn := normSq_unitary q
  rcases rational_scalar q.val.re ha with ha | ha | ha | ha | ha <;>
    rcases rational_scalar q.val.imI hb with hb | hb | hb | hb | hb <;>
    rcases rational_scalar q.val.imJ hc with hc | hc | hc | hc | hc <;>
    rcases rational_scalar q.val.imK hd with hd | hd | hd | hd | hd
  all_goals norm_num [Quaternion.normSq_def',ha,hb,hc,hd] at hn
  all_goals norm_num [Normalizes,CoordinateAxis,Subtype.ext_iff,conjugate_value,
    quaternion_eq_iff,Unitary.coe_neg,
    axisI,axisJ,axisK,ha,hb,hc,hd]

end

end MainTheory.QuaternionRationalNormalizer
