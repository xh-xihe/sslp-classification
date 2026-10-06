import SixQubit.CodeOrbit12
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit12PhysicalRowData
open scoped BigOperators Matrix
open SixQubit SixQubit.Orbit12
noncomputable section
def RowData (c d : SS.State 6 ℂ) : Prop :=
  (star (c y0) * d z0 + star (c y7) * d z7 = 0) ∧
  (star (c y0) * d z8 + star (c y7) * d z15 = 0) ∧
  (star (c y8) * d z0 + star (c y15) * d z7 = 0) ∧
  (star (c y8) * d z8 + star (c y15) * d z15 = 0) ∧
  (star (c y8) * c y0 + star (c y15) * c y7 = star (d z14) * d z6 + star (d z13) * d z5 + star (d z12) * d z4 + star (d z11) * d z3 + star (d z10) * d z2 + star (d z9) * d z1) ∧
  (Complex.normSq (c y0) + Complex.normSq (c y8) = 1/4) ∧
  (Complex.normSq (c y7) + Complex.normSq (c y15) = 1/4) ∧
  (Complex.normSq (c y0) + Complex.normSq (c y7) = Complex.normSq (d z6) + Complex.normSq (d z5) + Complex.normSq (d z4) + Complex.normSq (d z3) + Complex.normSq (d z2) + Complex.normSq (d z1)) ∧
  (Complex.normSq (c y8) + Complex.normSq (c y15) = Complex.normSq (d z14) + Complex.normSq (d z13) + Complex.normSq (d z12) + Complex.normSq (d z11) + Complex.normSq (d z10) + Complex.normSq (d z9)) ∧
  ((Complex.normSq (d z1) + Complex.normSq (d z9)) + (Complex.normSq (d z2) + Complex.normSq (d z10)) + (Complex.normSq (d z3) + Complex.normSq (d z11)) = 1/4) ∧
  (star (c y6) * d z0 + star (c y14) * d z8
        + (star (c y7) * d z1 + star (c y15) * d z9) = 0) ∧
  (star (c y0) * d z1 + star (c y8) * d z9
        + (star (c y6) * d z7 + star (c y14) * d z15) = 0) ∧
  (star (c y5) * d z0 + star (c y13) * d z8
        + (star (c y7) * d z2 + star (c y15) * d z10) = 0) ∧
  (star (c y0) * d z2 + star (c y8) * d z10
        + (star (c y5) * d z7 + star (c y13) * d z15) = 0) ∧
  (star (c y4) * d z0 + star (c y12) * d z8
        + (star (c y7) * d z3 + star (c y15) * d z11) = 0) ∧
  (star (c y0) * d z3 + star (c y8) * d z11
        + (star (c y4) * d z7 + star (c y12) * d z15) = 0)

theorem row_data_of_rows (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (ho0 : offSum c d ef0 w0 = 0)
    (ho1 : offSum c d ef0 w1 = 0)
    (ho2 : offSum c d ef0 w5 = 0)
    (ho3 : offSum c d ef0 w6 = 0)
    (ho4 : offSum c d ef1 w0 = 0)
    (ho5 : offSum c d ef1 w1 = 0)
    (ho6 : offSum c d ef1 w5 = 0)
    (ho7 : offSum c d ef1 w6 = 0)
    (ho8 : offSum c d ef2 w0 = 0)
    (ho9 : offSum c d ef2 w4 = 0)
    (ho10 : offSum c d ef3 w0 = 0)
    (ho11 : offSum c d ef3 w2 = 0)
    (ho12 : offSum c d ef4 w0 = 0)
    (ho13 : offSum c d ef4 w3 = 0)
    (ho14 : offSum c d ef5 w0 = 0)
    (ho15 : offSum c d ef5 w2 = 0)
    (ho16 : offSum c d ef6 w0 = 0)
    (ho17 : offSum c d ef6 w2 = 0)
    (ho18 : offSum c d ef7 w0 = 0)
    (ho19 : offSum c d ef7 w3 = 0)
    (hd0 : diagBot c efA w0 = diagTop d efA w0)
    (hd1 : diagBot c efA w1 = diagTop d efA w1)
    (hd2 : diagBot c efA w5 = diagTop d efA w5)
    (hd3 : diagBot c efA w6 = diagTop d efA w6)
    : RowData c d := by
  rw [ex_ef0_w0] at ho0
  rw [ex_ef0_w1] at ho1
  rw [ex_ef0_w5] at ho2
  rw [ex_ef0_w6] at ho3
  rw [ex_ef1_w0] at ho4
  rw [ex_ef1_w1] at ho5
  rw [ex_ef1_w5] at ho6
  rw [ex_ef1_w6] at ho7
  rw [ex_ef2_w0] at ho8
  rw [ex_ef2_w4] at ho9
  rw [ex_ef3_w0] at ho10
  rw [ex_ef3_w2] at ho11
  rw [ex_ef4_w0] at ho12
  rw [ex_ef4_w3] at ho13
  rw [ex_ef5_w0] at ho14
  rw [ex_ef5_w2] at ho15
  rw [ex_ef6_w0] at ho16
  rw [ex_ef6_w2] at ho17
  rw [ex_ef7_w0] at ho18
  rw [ex_ef7_w3] at ho19
  rw [dexB_w0, dexT_w0] at hd0
  rw [dexB_w1, dexT_w1] at hd1
  rw [dexB_w5, dexT_w5] at hd2
  rw [dexB_w6, dexT_w6] at hd3
  have K00 : star (c y0) * d z0 + star (c y7) * d z7 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (-1/4 : ℂ) * ho1 + (1/4 : ℂ) * ho2 + (-1/4 : ℂ) * ho3
  have K01 : star (c y0) * d z8 + star (c y7) * d z15 = 0 := by
    linear_combination (1/4 : ℂ) * ho4 + (-1/4 : ℂ) * ho5 + (-1/4 : ℂ) * ho6 + (1/4 : ℂ) * ho7
  have K10 : star (c y8) * d z0 + star (c y15) * d z7 = 0 := by
    linear_combination (1/4 : ℂ) * ho4 + (-1/4 : ℂ) * ho5 + (1/4 : ℂ) * ho6 + (-1/4 : ℂ) * ho7
  have K11 : star (c y8) * d z8 + star (c y15) * d z15 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (-1/4 : ℂ) * ho1 + (-1/4 : ℂ) * ho2 + (1/4 : ℂ) * ho3
  have Doff : star (c y8) * c y0 + star (c y15) * c y7 = star (d z14) * d z6 + star (d z13) * d z5 + star (d z12) * d z4 + star (d z11) * d z3 + star (d z10) * d z2 + star (d z9) * d z1 := by
    linear_combination (1/4 : ℂ) * hd0 + (1/4 : ℂ) * hd1 + (1/4 : ℂ) * hd2 + (1/4 : ℂ) * hd3
  obtain ⟨hu4,hv4,D0,D1,hsum⟩ := hm.facts
  have P1_0 : star (c y6) * d z0 + star (c y14) * d z8
        + (star (c y7) * d z1 + star (c y15) * d z9) = 0 := by
      linear_combination (1/2 : ℂ) * ho8 + (1/2 : ℂ) * ho9
  have P2_0 : star (c y0) * d z1 + star (c y8) * d z9
        + (star (c y6) * d z7 + star (c y14) * d z15) = 0 := by
      linear_combination (1/2 : ℂ) * ho10 + (-1/2 : ℂ) * ho11
  have P1_1 : star (c y5) * d z0 + star (c y13) * d z8
        + (star (c y7) * d z2 + star (c y15) * d z10) = 0 := by
      linear_combination (1/2 : ℂ) * ho12 + (1/2 : ℂ) * ho13
  have P2_1 : star (c y0) * d z2 + star (c y8) * d z10
        + (star (c y5) * d z7 + star (c y13) * d z15) = 0 := by
      linear_combination (1/2 : ℂ) * ho14 + (-1/2 : ℂ) * ho15
  have P1_2 : star (c y4) * d z0 + star (c y12) * d z8
        + (star (c y7) * d z3 + star (c y15) * d z11) = 0 := by
      linear_combination (1/2 : ℂ) * ho16 + (1/2 : ℂ) * ho17
  have P2_2 : star (c y0) * d z3 + star (c y8) * d z11
        + (star (c y4) * d z7 + star (c y12) * d z15) = 0 := by
      linear_combination (1/2 : ℂ) * ho18 + (-1/2 : ℂ) * ho19
  exact ⟨K00,K01,K10,K11,Doff,hu4,hv4,D0,D1,hsum,P1_0,P2_0,P1_1,P2_1,P1_2,P2_2⟩

theorem physical_row_data (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : RowData c d :=
  row_data_of_rows c d
    (moments c d hc hd hnc hnd hdist)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w5 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w5 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef4 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef4 w3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef5 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef5 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef6 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef6 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef7 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef7 w3 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efA w0 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efA w1 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efA w5 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efA w6 (by decide))


end
end MainTheory.Orbit12PhysicalRowData
