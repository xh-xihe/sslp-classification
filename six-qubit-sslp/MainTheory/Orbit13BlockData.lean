import SixQubit.CodeOrbit13
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace MainTheory.Orbit13BlockData
open scoped BigOperators Matrix
open SixQubit SixQubit.Orbit13
noncomputable section
def BlockData (c d : SS.State 6 ℂ) : Prop :=
  (star (c y0) * d z0 + star (c y8) * d z8 = 0) ∧
  (star (c y0) * d z1 + star (c y8) * d z9 = 0) ∧
  (star (c y1) * d z0 + star (c y9) * d z8 = 0) ∧
  (star (c y1) * d z1 + star (c y9) * d z9 = 0) ∧
  (c y0 * star (c y8) + c y1 * star (c y9)
      = d z0 * star (d z8) + d z1 * star (d z9)) ∧
  (star (c y2) * d z2 + star (c y10) * d z10 = 0) ∧
  (star (c y2) * d z3 + star (c y10) * d z11 = 0) ∧
  (star (c y3) * d z2 + star (c y11) * d z10 = 0) ∧
  (star (c y3) * d z3 + star (c y11) * d z11 = 0) ∧
  (c y2 * star (c y10) + c y3 * star (c y11)
      = d z2 * star (d z10) + d z3 * star (d z11)) ∧
  (star (c y4) * d z4 + star (c y12) * d z12 = 0) ∧
  (star (c y4) * d z5 + star (c y12) * d z13 = 0) ∧
  (star (c y5) * d z4 + star (c y13) * d z12 = 0) ∧
  (star (c y5) * d z5 + star (c y13) * d z13 = 0) ∧
  (c y4 * star (c y12) + c y5 * star (c y13)
      = d z4 * star (d z12) + d z5 * star (d z13)) ∧
  (star (c y6) * d z6 + star (c y14) * d z14 = 0) ∧
  (star (c y6) * d z7 + star (c y14) * d z15 = 0) ∧
  (star (c y7) * d z6 + star (c y15) * d z14 = 0) ∧
  (star (c y7) * d z7 + star (c y15) * d z15 = 0) ∧
  (c y6 * star (c y14) + c y7 * star (c y15)
      = d z6 * star (d z14) + d z7 * star (d z15)) ∧
  (Complex.normSq (c y0)+Complex.normSq (c y1)=Complex.normSq (d z0)+Complex.normSq (d z1)) ∧
  (Complex.normSq (c y8)+Complex.normSq (c y9)=Complex.normSq (d z8)+Complex.normSq (d z9)) ∧
  (Complex.normSq (c y2)+Complex.normSq (c y3)=Complex.normSq (d z2)+Complex.normSq (d z3)) ∧
  (Complex.normSq (c y10)+Complex.normSq (c y11)=Complex.normSq (d z10)+Complex.normSq (d z11)) ∧
  (Complex.normSq (c y4)+Complex.normSq (c y5)=Complex.normSq (d z4)+Complex.normSq (d z5)) ∧
  (Complex.normSq (c y12)+Complex.normSq (c y13)=Complex.normSq (d z12)+Complex.normSq (d z13)) ∧
  (Complex.normSq (c y6)+Complex.normSq (c y7)=Complex.normSq (d z6)+Complex.normSq (d z7)) ∧
  (Complex.normSq (c y14)+Complex.normSq (c y15)=Complex.normSq (d z14)+Complex.normSq (d z15))

theorem block_data_of_rows (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (ho0 : offSum c d ef0 w0 = 0)
    (ho1 : offSum c d ef0 w1 = 0)
    (ho2 : offSum c d ef0 w2 = 0)
    (ho3 : offSum c d ef0 w3 = 0)
    (ho4 : offSum c d ef0 w4 = 0)
    (ho5 : offSum c d ef0 w5 = 0)
    (ho6 : offSum c d ef0 w7 = 0)
    (ho7 : offSum c d ef0 w8 = 0)
    (ho8 : offSum c d ef1 w0 = 0)
    (ho9 : offSum c d ef1 w1 = 0)
    (ho10 : offSum c d ef1 w2 = 0)
    (ho11 : offSum c d ef1 w3 = 0)
    (ho12 : offSum c d ef1 w4 = 0)
    (ho13 : offSum c d ef1 w6 = 0)
    (ho14 : offSum c d ef1 w7 = 0)
    (ho15 : offSum c d ef1 w9 = 0)
    (hd0 : diagBot c efZ w0 = diagTop d efZ w0)
    (hd1 : diagBot c efZ w4 = diagTop d efZ w4)
    (hd2 : diagBot c efZ w7 = diagTop d efZ w7)
    (hd3 : diagBot c efZ w10 = diagTop d efZ w10)
    (hd4 : diagBot c efZ w11 = diagTop d efZ w11)
    (hd5 : diagBot c efZ w14 = diagTop d efZ w14)
    (hd6 : diagBot c efZ w15 = diagTop d efZ w15)
    (hd7 : diagBot c efZ w16 = diagTop d efZ w16)
    : BlockData c d := by
  rw [ex_ef0_w0] at ho0
  rw [ex_ef0_w1] at ho1
  rw [ex_ef0_w2] at ho2
  rw [ex_ef0_w3] at ho3
  rw [ex_ef0_w4] at ho4
  rw [ex_ef0_w5] at ho5
  rw [ex_ef0_w7] at ho6
  rw [ex_ef0_w8] at ho7
  rw [ex_ef1_w0] at ho8
  rw [ex_ef1_w1] at ho9
  rw [ex_ef1_w2] at ho10
  rw [ex_ef1_w3] at ho11
  rw [ex_ef1_w4] at ho12
  rw [ex_ef1_w6] at ho13
  rw [ex_ef1_w7] at ho14
  rw [ex_ef1_w9] at ho15
  rw [dexB_w0, dexT_w0] at hd0
  rw [dexB_w4, dexT_w4] at hd1
  rw [dexB_w7, dexT_w7] at hd2
  rw [dexB_w10, dexT_w10] at hd3
  rw [dexB_w11, dexT_w11] at hd4
  rw [dexB_w14, dexT_w14] at hd5
  rw [dexB_w15, dexT_w15] at hd6
  rw [dexB_w16, dexT_w16] at hd7
  obtain ⟨fa0, fa1, fa2, fa3, fa4, fa5, fa6, fa7⟩ := hm.frameA
  have o11_0 : star (c y0) * d z0 + star (c y8) * d z8 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (-1/4 : ℂ) * ho1 + (1/4 : ℂ) * ho2 + (-1/4 : ℂ) * ho3
  have o12_0 : star (c y0) * d z1 + star (c y8) * d z9 = 0 := by
    linear_combination (1/4 : ℂ) * ho8 + (1/4 : ℂ) * ho9 + (-1/4 : ℂ) * ho10 + (-1/4 : ℂ) * ho11
  have o21_0 : star (c y1) * d z0 + star (c y9) * d z8 = 0 := by
    linear_combination (1/4 : ℂ) * ho8 + (-1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho10 + (-1/4 : ℂ) * ho11
  have o22_0 : star (c y1) * d z1 + star (c y9) * d z9 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (1/4 : ℂ) * ho1 + (-1/4 : ℂ) * ho2 + (-1/4 : ℂ) * ho3
  have fc_0 : c y0 * star (c y8) + c y1 * star (c y9)
      = d z0 * star (d z8) + d z1 * star (d z9) := by
    linear_combination (1/8 : ℂ) * hd0 + (1/8 : ℂ) * hd1 + (1/8 : ℂ) * hd2 + (1/8 : ℂ) * hd3 + (1/8 : ℂ) * hd4 + (1/8 : ℂ) * hd5 + (1/8 : ℂ) * hd6 + (1/8 : ℂ) * hd7
  have o11_1 : star (c y2) * d z2 + star (c y10) * d z10 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (1/4 : ℂ) * ho1 + (-1/4 : ℂ) * ho2 + (-1/4 : ℂ) * ho3 + (-1/4 : ℂ) * ho4 + (-1/4 : ℂ) * ho5 + (-1/4 : ℂ) * ho6 + (-1/4 : ℂ) * ho7
  have o12_1 : star (c y2) * d z3 + star (c y10) * d z11 = 0 := by
    linear_combination (1/4 : ℂ) * ho8 + (1/4 : ℂ) * ho9 + (-1/4 : ℂ) * ho10 + (-1/4 : ℂ) * ho11 + (-1/4 : ℂ) * ho12 + (1/4 : ℂ) * ho13 + (-1/4 : ℂ) * ho14 + (1/4 : ℂ) * ho15
  have o21_1 : star (c y3) * d z2 + star (c y11) * d z10 = 0 := by
    linear_combination (1/4 : ℂ) * ho8 + (-1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho10 + (-1/4 : ℂ) * ho11 + (-1/4 : ℂ) * ho12 + (-1/4 : ℂ) * ho13 + (-1/4 : ℂ) * ho14 + (-1/4 : ℂ) * ho15
  have o22_1 : star (c y3) * d z3 + star (c y11) * d z11 = 0 := by
    linear_combination (1/4 : ℂ) * ho0 + (-1/4 : ℂ) * ho1 + (1/4 : ℂ) * ho2 + (-1/4 : ℂ) * ho3 + (-1/4 : ℂ) * ho4 + (1/4 : ℂ) * ho5 + (-1/4 : ℂ) * ho6 + (1/4 : ℂ) * ho7
  have fc_1 : c y2 * star (c y10) + c y3 * star (c y11)
      = d z2 * star (d z10) + d z3 * star (d z11) := by
    linear_combination (1/8 : ℂ) * hd0 + (-1/8 : ℂ) * hd1 + (-1/8 : ℂ) * hd2 + (1/8 : ℂ) * hd3 + (1/8 : ℂ) * hd4 + (-1/8 : ℂ) * hd5 + (-1/8 : ℂ) * hd6 + (1/8 : ℂ) * hd7
  have o11_2 : star (c y4) * d z4 + star (c y12) * d z12 = 0 := by
    linear_combination (1/4 : ℂ) * ho2 + (1/4 : ℂ) * ho3 + (1/4 : ℂ) * ho6 + (1/4 : ℂ) * ho7
  have o12_2 : star (c y4) * d z5 + star (c y12) * d z13 = 0 := by
    linear_combination (-1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho11 + (1/4 : ℂ) * ho14 + (-1/4 : ℂ) * ho15
  have o21_2 : star (c y5) * d z4 + star (c y13) * d z12 = 0 := by
    linear_combination (1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho11 + (1/4 : ℂ) * ho14 + (1/4 : ℂ) * ho15
  have o22_2 : star (c y5) * d z5 + star (c y13) * d z13 = 0 := by
    linear_combination (-1/4 : ℂ) * ho2 + (1/4 : ℂ) * ho3 + (1/4 : ℂ) * ho6 + (-1/4 : ℂ) * ho7
  have fc_2 : c y4 * star (c y12) + c y5 * star (c y13)
      = d z4 * star (d z12) + d z5 * star (d z13) := by
    linear_combination (1/8 : ℂ) * hd0 + (-1/8 : ℂ) * hd1 + (1/8 : ℂ) * hd2 + (-1/8 : ℂ) * hd3 + (1/8 : ℂ) * hd4 + (-1/8 : ℂ) * hd5 + (1/8 : ℂ) * hd6 + (-1/8 : ℂ) * hd7
  have o11_3 : star (c y6) * d z6 + star (c y14) * d z14 = 0 := by
    linear_combination (1/4 : ℂ) * ho2 + (1/4 : ℂ) * ho3 + (1/4 : ℂ) * ho4 + (1/4 : ℂ) * ho5
  have o12_3 : star (c y6) * d z7 + star (c y14) * d z15 = 0 := by
    linear_combination (-1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho11 + (1/4 : ℂ) * ho12 + (-1/4 : ℂ) * ho13
  have o21_3 : star (c y7) * d z6 + star (c y15) * d z14 = 0 := by
    linear_combination (1/4 : ℂ) * ho9 + (1/4 : ℂ) * ho11 + (1/4 : ℂ) * ho12 + (1/4 : ℂ) * ho13
  have o22_3 : star (c y7) * d z7 + star (c y15) * d z15 = 0 := by
    linear_combination (-1/4 : ℂ) * ho2 + (1/4 : ℂ) * ho3 + (1/4 : ℂ) * ho4 + (-1/4 : ℂ) * ho5
  have fc_3 : c y6 * star (c y14) + c y7 * star (c y15)
      = d z6 * star (d z14) + d z7 * star (d z15) := by
    linear_combination (1/8 : ℂ) * hd0 + (1/8 : ℂ) * hd1 + (-1/8 : ℂ) * hd2 + (-1/8 : ℂ) * hd3 + (1/8 : ℂ) * hd4 + (1/8 : ℂ) * hd5 + (-1/8 : ℂ) * hd6 + (-1/8 : ℂ) * hd7
  exact ⟨o11_0,o12_0,o21_0,o22_0,fc_0,o11_1,o12_1,o21_1,o22_1,fc_1,o11_2,o12_2,o21_2,o22_2,fc_2,o11_3,o12_3,o21_3,o22_3,fc_3,fa0,fa1,fa2,fa3,fa4,fa5,fa6,fa7⟩

theorem physical_block_data (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : BlockData c d :=
  block_data_of_rows c d
    (moments c d hc hd hnc hnd hdist)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w2 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w3 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w4 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w5 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w7 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w8 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w0 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w1 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w2 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w3 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w4 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w6 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w7 (by decide +kernel))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w9 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efZ w0 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efZ w4 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efZ w7 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efZ w10 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efZ w11 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efZ w14 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efZ w15 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efZ w16 (by decide +kernel))

end
end MainTheory.Orbit13BlockData
