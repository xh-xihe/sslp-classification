import SixQubit.CodeOrbit20
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit20PhysicalRowData
open scoped BigOperators Matrix
open SixQubit SixQubit.Orbit20
noncomputable section
def RowData (c d : SS.State 6 ℂ) : Prop :=
  (star (c y0) * d z2 + star (c y1) * d z3 = 0) ∧
  (star (c y0) * d z1 + star (c y2) * d z3 = 0) ∧
  (star (c y0) * d z0 + star (c y3) * d z3 = 0) ∧
  (star (c y1) * d z1 + star (c y2) * d z2 = 0) ∧
  (star (c y1) * d z0 + star (c y3) * d z2 = 0) ∧
  (star (c y2) * d z0 + star (c y3) * d z1 = 0) ∧
  (star (c y4) * d z6 + star (c y5) * d z7 = 0) ∧
  (star (c y4) * d z5 + star (c y6) * d z7 = 0) ∧
  (star (c y4) * d z4 + star (c y7) * d z7 = 0) ∧
  (star (c y5) * d z5 + star (c y6) * d z6 = 0) ∧
  (star (c y5) * d z4 + star (c y7) * d z6 = 0) ∧
  (star (c y6) * d z4 + star (c y7) * d z5 = 0) ∧
  (star (c y8) * d z10 + star (c y9) * d z11 = 0) ∧
  (star (c y8) * d z9 + star (c y10) * d z11 = 0) ∧
  (star (c y8) * d z8 + star (c y11) * d z11 = 0) ∧
  (star (c y9) * d z9 + star (c y10) * d z10 = 0) ∧
  (star (c y9) * d z8 + star (c y11) * d z10 = 0) ∧
  (star (c y10) * d z8 + star (c y11) * d z9 = 0) ∧
  (star (c y12) * d z14 + star (c y13) * d z15 = 0) ∧
  (star (c y12) * d z13 + star (c y14) * d z15 = 0) ∧
  (star (c y12) * d z12 + star (c y15) * d z15 = 0) ∧
  (star (c y13) * d z13 + star (c y14) * d z14 = 0) ∧
  (star (c y13) * d z12 + star (c y15) * d z14 = 0) ∧
  (star (c y14) * d z12 + star (c y15) * d z13 = 0) ∧
  (Complex.normSq (c y0)=Complex.normSq (d z3)) ∧
  (Complex.normSq (c y1)=Complex.normSq (d z2)) ∧
  (Complex.normSq (c y2)=Complex.normSq (d z1)) ∧
  (Complex.normSq (c y3)=Complex.normSq (d z0)) ∧
  (Complex.normSq (c y4)=Complex.normSq (d z7)) ∧
  (Complex.normSq (c y5)=Complex.normSq (d z6)) ∧
  (Complex.normSq (c y6)=Complex.normSq (d z5)) ∧
  (Complex.normSq (c y7)=Complex.normSq (d z4)) ∧
  (Complex.normSq (c y8)=Complex.normSq (d z11)) ∧
  (Complex.normSq (c y9)=Complex.normSq (d z10)) ∧
  (Complex.normSq (c y10)=Complex.normSq (d z9)) ∧
  (Complex.normSq (c y11)=Complex.normSq (d z8)) ∧
  (Complex.normSq (c y12)=Complex.normSq (d z15)) ∧
  (Complex.normSq (c y13)=Complex.normSq (d z14)) ∧
  (Complex.normSq (c y14)=Complex.normSq (d z13)) ∧
  (Complex.normSq (c y15)=Complex.normSq (d z12)) ∧
  (Complex.normSq (c y1)=Complex.normSq (c y0)) ∧
  (Complex.normSq (c y2)=Complex.normSq (c y0)) ∧
  (Complex.normSq (c y3)=Complex.normSq (c y0)) ∧
  (Complex.normSq (c y5)=Complex.normSq (c y4)) ∧
  (Complex.normSq (c y6)=Complex.normSq (c y4)) ∧
  (Complex.normSq (c y7)=Complex.normSq (c y4)) ∧
  (Complex.normSq (c y9)=Complex.normSq (c y8)) ∧
  (Complex.normSq (c y10)=Complex.normSq (c y8)) ∧
  (Complex.normSq (c y11)=Complex.normSq (c y8)) ∧
  (Complex.normSq (c y13)=Complex.normSq (c y12)) ∧
  (Complex.normSq (c y14)=Complex.normSq (c y12)) ∧
  (Complex.normSq (c y15)=Complex.normSq (c y12)) ∧
  (4*(Complex.normSq (c y0)+Complex.normSq (c y4)+Complex.normSq (c y8)+Complex.normSq (c y12))=1)

theorem row_data_of_rows (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)))
    (h0 : offSum c d efA w0 = 0)
    (h1 : offSum c d efA w3 = 0)
    (h2 : offSum c d efA w4 = 0)
    (h3 : offSum c d efA w7 = 0)
    (h4 : offSum c d efA w8 = 0)
    (h5 : offSum c d efA w11 = 0)
    (h6 : offSum c d efA w12 = 0)
    (h7 : offSum c d efA w15 = 0)
    (h8 : offSum c d efB w0 = 0)
    (h9 : offSum c d efB w2 = 0)
    (h10 : offSum c d efB w4 = 0)
    (h11 : offSum c d efB w6 = 0)
    (h12 : offSum c d efB w8 = 0)
    (h13 : offSum c d efB w10 = 0)
    (h14 : offSum c d efB w12 = 0)
    (h15 : offSum c d efB w14 = 0)
    (h16 : offSum c d efC w0 = 0)
    (h17 : offSum c d efC w1 = 0)
    (h18 : offSum c d efC w4 = 0)
    (h19 : offSum c d efC w5 = 0)
    (h20 : offSum c d efC w8 = 0)
    (h21 : offSum c d efC w9 = 0)
    (h22 : offSum c d efC w12 = 0)
    (h23 : offSum c d efC w13 = 0)
    : RowData c d := by
  rw [exA_w0] at h0
  rw [exA_w3] at h1
  rw [exA_w4] at h2
  rw [exA_w7] at h3
  rw [exA_w8] at h4
  rw [exA_w11] at h5
  rw [exA_w12] at h6
  rw [exA_w15] at h7
  rw [exB_w0] at h8
  rw [exB_w2] at h9
  rw [exB_w4] at h10
  rw [exB_w6] at h11
  rw [exB_w8] at h12
  rw [exB_w10] at h13
  rw [exB_w12] at h14
  rw [exB_w14] at h15
  rw [exC_w0] at h16
  rw [exC_w1] at h17
  rw [exC_w4] at h18
  rw [exC_w5] at h19
  rw [exC_w8] at h20
  rw [exC_w9] at h21
  rw [exC_w12] at h22
  rw [exC_w13] at h23
  have rel_0_1 : star (c y0) * d z2 + star (c y1) * d z3 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (-1/8 : ℂ) * h1 + (1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (1/8 : ℂ) * h4 + (-1/8 : ℂ) * h5 + (1/8 : ℂ) * h6 + (-1/8 : ℂ) * h7
  have rel_0_2 : star (c y0) * d z1 + star (c y2) * d z3 = 0 := by
    linear_combination (1/8 : ℂ) * h8 + (-1/8 : ℂ) * h9 + (1/8 : ℂ) * h10 + (-1/8 : ℂ) * h11 + (1/8 : ℂ) * h12 + (-1/8 : ℂ) * h13 + (1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15
  have rel_0_3 : star (c y0) * d z0 + star (c y3) * d z3 = 0 := by
    linear_combination (1/8 : ℂ) * h16 + (-1/8 : ℂ) * h17 + (1/8 : ℂ) * h18 + (-1/8 : ℂ) * h19 + (1/8 : ℂ) * h20 + (-1/8 : ℂ) * h21 + (1/8 : ℂ) * h22 + (-1/8 : ℂ) * h23
  have rel_1_2 : star (c y1) * d z1 + star (c y2) * d z2 = 0 := by
    linear_combination (1/8 : ℂ) * h16 + (1/8 : ℂ) * h17 + (1/8 : ℂ) * h18 + (1/8 : ℂ) * h19 + (1/8 : ℂ) * h20 + (1/8 : ℂ) * h21 + (1/8 : ℂ) * h22 + (1/8 : ℂ) * h23
  have rel_1_3 : star (c y1) * d z0 + star (c y3) * d z2 = 0 := by
    linear_combination (1/8 : ℂ) * h8 + (1/8 : ℂ) * h9 + (1/8 : ℂ) * h10 + (1/8 : ℂ) * h11 + (1/8 : ℂ) * h12 + (1/8 : ℂ) * h13 + (1/8 : ℂ) * h14 + (1/8 : ℂ) * h15
  have rel_2_3 : star (c y2) * d z0 + star (c y3) * d z1 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (1/8 : ℂ) * h1 + (1/8 : ℂ) * h2 + (1/8 : ℂ) * h3 + (1/8 : ℂ) * h4 + (1/8 : ℂ) * h5 + (1/8 : ℂ) * h6 + (1/8 : ℂ) * h7
  have rel_4_5 : star (c y4) * d z6 + star (c y5) * d z7 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (-1/8 : ℂ) * h1 + (-1/8 : ℂ) * h2 + (1/8 : ℂ) * h3 + (-1/8 : ℂ) * h4 + (1/8 : ℂ) * h5 + (1/8 : ℂ) * h6 + (-1/8 : ℂ) * h7
  have rel_4_6 : star (c y4) * d z5 + star (c y6) * d z7 = 0 := by
    linear_combination (1/8 : ℂ) * h8 + (-1/8 : ℂ) * h9 + (-1/8 : ℂ) * h10 + (1/8 : ℂ) * h11 + (-1/8 : ℂ) * h12 + (1/8 : ℂ) * h13 + (1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15
  have rel_4_7 : star (c y4) * d z4 + star (c y7) * d z7 = 0 := by
    linear_combination (1/8 : ℂ) * h16 + (1/8 : ℂ) * h17 + (-1/8 : ℂ) * h18 + (-1/8 : ℂ) * h19 + (-1/8 : ℂ) * h20 + (-1/8 : ℂ) * h21 + (1/8 : ℂ) * h22 + (1/8 : ℂ) * h23
  have rel_5_6 : star (c y5) * d z5 + star (c y6) * d z6 = 0 := by
    linear_combination (1/8 : ℂ) * h16 + (-1/8 : ℂ) * h17 + (-1/8 : ℂ) * h18 + (1/8 : ℂ) * h19 + (-1/8 : ℂ) * h20 + (1/8 : ℂ) * h21 + (1/8 : ℂ) * h22 + (-1/8 : ℂ) * h23
  have rel_5_7 : star (c y5) * d z4 + star (c y7) * d z6 = 0 := by
    linear_combination (1/8 : ℂ) * h8 + (1/8 : ℂ) * h9 + (-1/8 : ℂ) * h10 + (-1/8 : ℂ) * h11 + (-1/8 : ℂ) * h12 + (-1/8 : ℂ) * h13 + (1/8 : ℂ) * h14 + (1/8 : ℂ) * h15
  have rel_6_7 : star (c y6) * d z4 + star (c y7) * d z5 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (1/8 : ℂ) * h1 + (-1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (-1/8 : ℂ) * h4 + (-1/8 : ℂ) * h5 + (1/8 : ℂ) * h6 + (1/8 : ℂ) * h7
  have rel_8_9 : star (c y8) * d z10 + star (c y9) * d z11 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (-1/8 : ℂ) * h1 + (-1/8 : ℂ) * h2 + (1/8 : ℂ) * h3 + (1/8 : ℂ) * h4 + (-1/8 : ℂ) * h5 + (-1/8 : ℂ) * h6 + (1/8 : ℂ) * h7
  have rel_8_10 : star (c y8) * d z9 + star (c y10) * d z11 = 0 := by
    linear_combination (1/8 : ℂ) * h8 + (-1/8 : ℂ) * h9 + (-1/8 : ℂ) * h10 + (1/8 : ℂ) * h11 + (1/8 : ℂ) * h12 + (-1/8 : ℂ) * h13 + (-1/8 : ℂ) * h14 + (1/8 : ℂ) * h15
  have rel_8_11 : star (c y8) * d z8 + star (c y11) * d z11 = 0 := by
    linear_combination (1/8 : ℂ) * h16 + (1/8 : ℂ) * h17 + (-1/8 : ℂ) * h18 + (-1/8 : ℂ) * h19 + (1/8 : ℂ) * h20 + (1/8 : ℂ) * h21 + (-1/8 : ℂ) * h22 + (-1/8 : ℂ) * h23
  have rel_9_10 : star (c y9) * d z9 + star (c y10) * d z10 = 0 := by
    linear_combination (1/8 : ℂ) * h16 + (-1/8 : ℂ) * h17 + (-1/8 : ℂ) * h18 + (1/8 : ℂ) * h19 + (1/8 : ℂ) * h20 + (-1/8 : ℂ) * h21 + (-1/8 : ℂ) * h22 + (1/8 : ℂ) * h23
  have rel_9_11 : star (c y9) * d z8 + star (c y11) * d z10 = 0 := by
    linear_combination (1/8 : ℂ) * h8 + (1/8 : ℂ) * h9 + (-1/8 : ℂ) * h10 + (-1/8 : ℂ) * h11 + (1/8 : ℂ) * h12 + (1/8 : ℂ) * h13 + (-1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15
  have rel_10_11 : star (c y10) * d z8 + star (c y11) * d z9 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (1/8 : ℂ) * h1 + (-1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (1/8 : ℂ) * h4 + (1/8 : ℂ) * h5 + (-1/8 : ℂ) * h6 + (-1/8 : ℂ) * h7
  have rel_12_13 : star (c y12) * d z14 + star (c y13) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (-1/8 : ℂ) * h1 + (1/8 : ℂ) * h2 + (-1/8 : ℂ) * h3 + (-1/8 : ℂ) * h4 + (1/8 : ℂ) * h5 + (-1/8 : ℂ) * h6 + (1/8 : ℂ) * h7
  have rel_12_14 : star (c y12) * d z13 + star (c y14) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * h8 + (-1/8 : ℂ) * h9 + (1/8 : ℂ) * h10 + (-1/8 : ℂ) * h11 + (-1/8 : ℂ) * h12 + (1/8 : ℂ) * h13 + (-1/8 : ℂ) * h14 + (1/8 : ℂ) * h15
  have rel_12_15 : star (c y12) * d z12 + star (c y15) * d z15 = 0 := by
    linear_combination (1/8 : ℂ) * h16 + (1/8 : ℂ) * h17 + (1/8 : ℂ) * h18 + (1/8 : ℂ) * h19 + (-1/8 : ℂ) * h20 + (-1/8 : ℂ) * h21 + (-1/8 : ℂ) * h22 + (-1/8 : ℂ) * h23
  have rel_13_14 : star (c y13) * d z13 + star (c y14) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * h16 + (-1/8 : ℂ) * h17 + (1/8 : ℂ) * h18 + (-1/8 : ℂ) * h19 + (-1/8 : ℂ) * h20 + (1/8 : ℂ) * h21 + (-1/8 : ℂ) * h22 + (1/8 : ℂ) * h23
  have rel_13_15 : star (c y13) * d z12 + star (c y15) * d z14 = 0 := by
    linear_combination (1/8 : ℂ) * h8 + (1/8 : ℂ) * h9 + (1/8 : ℂ) * h10 + (1/8 : ℂ) * h11 + (-1/8 : ℂ) * h12 + (-1/8 : ℂ) * h13 + (-1/8 : ℂ) * h14 + (-1/8 : ℂ) * h15
  have rel_14_15 : star (c y14) * d z12 + star (c y15) * d z13 = 0 := by
    linear_combination (1/8 : ℂ) * h0 + (1/8 : ℂ) * h1 + (1/8 : ℂ) * h2 + (1/8 : ℂ) * h3 + (-1/8 : ℂ) * h4 + (-1/8 : ℂ) * h5 + (-1/8 : ℂ) * h6 + (-1/8 : ℂ) * h7
  have min_0_1 : Complex.normSq (c y0) * Complex.normSq (d z2)
      = Complex.normSq (c y1) * Complex.normSq (d z3) := minorEq rel_0_1
  have min_0_2 : Complex.normSq (c y0) * Complex.normSq (d z1)
      = Complex.normSq (c y2) * Complex.normSq (d z3) := minorEq rel_0_2
  have min_0_3 : Complex.normSq (c y0) * Complex.normSq (d z0)
      = Complex.normSq (c y3) * Complex.normSq (d z3) := minorEq rel_0_3
  have min_1_2 : Complex.normSq (c y1) * Complex.normSq (d z1)
      = Complex.normSq (c y2) * Complex.normSq (d z2) := minorEq rel_1_2
  have min_1_3 : Complex.normSq (c y1) * Complex.normSq (d z0)
      = Complex.normSq (c y3) * Complex.normSq (d z2) := minorEq rel_1_3
  have min_2_3 : Complex.normSq (c y2) * Complex.normSq (d z0)
      = Complex.normSq (c y3) * Complex.normSq (d z1) := minorEq rel_2_3
  have min_4_5 : Complex.normSq (c y4) * Complex.normSq (d z6)
      = Complex.normSq (c y5) * Complex.normSq (d z7) := minorEq rel_4_5
  have min_4_6 : Complex.normSq (c y4) * Complex.normSq (d z5)
      = Complex.normSq (c y6) * Complex.normSq (d z7) := minorEq rel_4_6
  have min_4_7 : Complex.normSq (c y4) * Complex.normSq (d z4)
      = Complex.normSq (c y7) * Complex.normSq (d z7) := minorEq rel_4_7
  have min_5_6 : Complex.normSq (c y5) * Complex.normSq (d z5)
      = Complex.normSq (c y6) * Complex.normSq (d z6) := minorEq rel_5_6
  have min_5_7 : Complex.normSq (c y5) * Complex.normSq (d z4)
      = Complex.normSq (c y7) * Complex.normSq (d z6) := minorEq rel_5_7
  have min_6_7 : Complex.normSq (c y6) * Complex.normSq (d z4)
      = Complex.normSq (c y7) * Complex.normSq (d z5) := minorEq rel_6_7
  have min_8_9 : Complex.normSq (c y8) * Complex.normSq (d z10)
      = Complex.normSq (c y9) * Complex.normSq (d z11) := minorEq rel_8_9
  have min_8_10 : Complex.normSq (c y8) * Complex.normSq (d z9)
      = Complex.normSq (c y10) * Complex.normSq (d z11) := minorEq rel_8_10
  have min_8_11 : Complex.normSq (c y8) * Complex.normSq (d z8)
      = Complex.normSq (c y11) * Complex.normSq (d z11) := minorEq rel_8_11
  have min_9_10 : Complex.normSq (c y9) * Complex.normSq (d z9)
      = Complex.normSq (c y10) * Complex.normSq (d z10) := minorEq rel_9_10
  have min_9_11 : Complex.normSq (c y9) * Complex.normSq (d z8)
      = Complex.normSq (c y11) * Complex.normSq (d z10) := minorEq rel_9_11
  have min_10_11 : Complex.normSq (c y10) * Complex.normSq (d z8)
      = Complex.normSq (c y11) * Complex.normSq (d z9) := minorEq rel_10_11
  have min_12_13 : Complex.normSq (c y12) * Complex.normSq (d z14)
      = Complex.normSq (c y13) * Complex.normSq (d z15) := minorEq rel_12_13
  have min_12_14 : Complex.normSq (c y12) * Complex.normSq (d z13)
      = Complex.normSq (c y14) * Complex.normSq (d z15) := minorEq rel_12_14
  have min_12_15 : Complex.normSq (c y12) * Complex.normSq (d z12)
      = Complex.normSq (c y15) * Complex.normSq (d z15) := minorEq rel_12_15
  have min_13_14 : Complex.normSq (c y13) * Complex.normSq (d z13)
      = Complex.normSq (c y14) * Complex.normSq (d z14) := minorEq rel_13_14
  have min_13_15 : Complex.normSq (c y13) * Complex.normSq (d z12)
      = Complex.normSq (c y15) * Complex.normSq (d z14) := minorEq rel_13_15
  have min_14_15 : Complex.normSq (c y14) * Complex.normSq (d z12)
      = Complex.normSq (c y15) * Complex.normSq (d z13) := minorEq rel_14_15
  obtain ⟨bm0, bm1, bm2, bm3⟩ := hm.blockMass
  obtain ⟨mt0, mt1, mt2, mt3⟩ :=
    blockMatch min_0_1 min_0_2 min_0_3 min_1_2 min_1_3 min_2_3 bm0
      (Complex.normSq_nonneg (c y0)) (Complex.normSq_nonneg (c y1)) (Complex.normSq_nonneg (c y2)) (Complex.normSq_nonneg (c y3))
      (Complex.normSq_nonneg (d z3)) (Complex.normSq_nonneg (d z2)) (Complex.normSq_nonneg (d z1)) (Complex.normSq_nonneg (d z0))
  obtain ⟨mt4, mt5, mt6, mt7⟩ :=
    blockMatch min_4_5 min_4_6 min_4_7 min_5_6 min_5_7 min_6_7 bm1
      (Complex.normSq_nonneg (c y4)) (Complex.normSq_nonneg (c y5)) (Complex.normSq_nonneg (c y6)) (Complex.normSq_nonneg (c y7))
      (Complex.normSq_nonneg (d z7)) (Complex.normSq_nonneg (d z6)) (Complex.normSq_nonneg (d z5)) (Complex.normSq_nonneg (d z4))
  obtain ⟨mt8, mt9, mt10, mt11⟩ :=
    blockMatch min_8_9 min_8_10 min_8_11 min_9_10 min_9_11 min_10_11 bm2
      (Complex.normSq_nonneg (c y8)) (Complex.normSq_nonneg (c y9)) (Complex.normSq_nonneg (c y10)) (Complex.normSq_nonneg (c y11))
      (Complex.normSq_nonneg (d z11)) (Complex.normSq_nonneg (d z10)) (Complex.normSq_nonneg (d z9)) (Complex.normSq_nonneg (d z8))
  obtain ⟨mt12, mt13, mt14, mt15⟩ :=
    blockMatch min_12_13 min_12_14 min_12_15 min_13_14 min_13_15 min_14_15 bm3
      (Complex.normSq_nonneg (c y12)) (Complex.normSq_nonneg (c y13)) (Complex.normSq_nonneg (c y14)) (Complex.normSq_nonneg (c y15))
      (Complex.normSq_nonneg (d z15)) (Complex.normSq_nonneg (d z14)) (Complex.normSq_nonneg (d z13)) (Complex.normSq_nonneg (d z12))
  obtain ⟨u1, u2, u3, u5, u6, u7, u9, u10, u11, u13, u14, u15, usum⟩ :=
    hm.uniform mt0 mt1 mt2 mt3 mt4 mt5 mt6 mt7 mt8 mt9 mt10 mt11 mt12 mt13 mt14 mt15
  exact ⟨rel_0_1,rel_0_2,rel_0_3,rel_1_2,rel_1_3,rel_2_3,rel_4_5,rel_4_6,rel_4_7,rel_5_6,rel_5_7,rel_6_7,rel_8_9,rel_8_10,rel_8_11,rel_9_10,rel_9_11,rel_10_11,rel_12_13,rel_12_14,rel_12_15,rel_13_14,rel_13_15,rel_14_15,mt0,mt1,mt2,mt3,mt4,mt5,mt6,mt7,mt8,mt9,mt10,mt11,mt12,mt13,mt14,mt15,u1,u2,u3,u5,u6,u7,u9,u10,u11,u13,u14,u15,usum⟩

theorem physical_row_data (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : RowData c d :=
  row_data_of_rows c d
    (moments c d hc hd hnc hnd hdist)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w7 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w8 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w11 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w12 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efA w15 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w8 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w10 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w12 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efB w14 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efC w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efC w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efC w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efC w5 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efC w8 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efC w9 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efC w12 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      efC w13 (by decide))


end
end MainTheory.Orbit20PhysicalRowData
